//! Locates the carved functions, decodes them, and checks that together they
//! form a closed unit:
//!
//! - every instruction is in [`AUDITED_MNEMONICS`], without `lock` or fs/gs
//!   prefixes (no atomics, no thread-local storage);
//! - every branch lands on an instruction of the carved code;
//! - the only calls are through relocated pointer slots that point at a carved
//!   function or at the panic entry;
//! - fixed memory is only reached rip-relative, and never written.
//!
//! Anything else is an error, so a rebuild that changes code generation is
//! reported rather than carved.

use {
    crate::elf::{Image, Symbol},
    anyhow::{Context, Result, bail, ensure},
    iced_x86::{
        Decoder, DecoderOptions, FlowControl, Instruction, InstructionInfoFactory, Mnemonic,
        OpAccess, Register,
    },
};

const FUNCTIONS: [(&str, &[&str]); 2] = [
    (
        "validate_fee_payer",
        &["solana_svm", "account_loader", "validate_fee_payer"],
    ),
    (
        "check_static_account_rent_state_transition",
        &[
            "solana_svm",
            "rent_calculator",
            "check_static_account_rent_state_transition",
        ],
    ),
];

/// Never returns. Reaching it is the "panicked" outcome; its code is not carved.
const PANIC_ENTRY: &[&str] = &["core", "option", "expect_failed"];

/// The instruction set the x86 semantics on the Lean side has to cover.
/// Extend it deliberately, together with those semantics.
#[rustfmt::skip]
const AUDITED_MNEMONICS: &[Mnemonic] = {
    use Mnemonic::*;
    &[
        // Integer moves and arithmetic. `movabs` is Mov with a 64-bit immediate.
        Mov, Movzx, Lea, Add, Sub, Sbb, Imul, Inc, And, Or, Xor, Sar,
        // Compares, flags, branches. Only CF and ZF are ever consumed.
        Cmp, Test, Je, Jne, Ja, Jae, Jb, Jmp, Sete, Setb, Cmovne, Cmovae, Cmovbe,
        // Stack and calls.
        Push, Pop, Call, Ret,
        // SSE integer: the 32-byte owner == System Program ID comparison.
        Movdqu, Pxor, Por, Ptest,
        // SSE floating point: Rent::minimum_balance when the exemption
        // threshold is neither 1.0 nor 2.0 (u64 -> f64, multiply, f64 -> u64).
        Movq, Punpckldq, Subpd, Movapd, Unpckhpd, Addsd, Mulsd, Subsd, Xorpd, Ucomisd, Cvttsd2si,
    ]
};

pub struct Function {
    pub name: &'static str,
    pub symbol: String,
    pub vaddr: u64,
    pub bytes: &'static [u8],
    pub instructions: Vec<Instruction>,
}

/// A rip-relative memory operand, the only way the code reaches fixed memory.
pub struct FixedRef {
    pub target: u64,
    pub use_: RefUse,
}

#[derive(Clone, Copy, PartialEq)]
pub enum RefUse {
    Read {
        size: u64,
    },
    /// `lea`: the address is computed and passed on, but not dereferenced.
    AddressOnly,
}

pub struct Code {
    pub functions: Vec<Function>,
    pub panic_entry: Symbol,
    pub fixed_refs: Vec<FixedRef>,
}

impl Code {
    pub fn instructions(&self) -> impl Iterator<Item = &Instruction> {
        self.functions.iter().flat_map(|f| &f.instructions)
    }

    pub fn function_starting_at(&self, vaddr: u64) -> Option<&Function> {
        self.functions.iter().find(|f| f.vaddr == vaddr)
    }

    fn is_instruction_start(&self, vaddr: u64) -> bool {
        self.functions.iter().any(|f| {
            f.instructions
                .binary_search_by_key(&vaddr, |i| i.ip())
                .is_ok()
        })
    }
}

pub fn carve(image: &Image) -> Result<Code> {
    let functions = FUNCTIONS
        .iter()
        .map(|&(name, path)| {
            let symbol = image.rust_fn(path)?;
            let bytes = image.read(symbol.vaddr, symbol.size)?;
            let instructions = decode(symbol.vaddr, bytes).with_context(|| name)?;
            Ok(Function {
                name,
                symbol: symbol.name,
                vaddr: symbol.vaddr,
                bytes,
                instructions,
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let mut code = Code {
        functions,
        panic_entry: image.rust_fn(PANIC_ENTRY)?,
        fixed_refs: vec![],
    };

    let mut info = InstructionInfoFactory::new();
    let mut fixed_refs = Vec::new();
    for i in code.instructions() {
        (|| {
            check_instruction(i)?;
            check_control_flow(&code, image, i)?;
            fixed_refs.extend(fixed_ref(&mut info, i)?);
            anyhow::Ok(())
        })()
        .with_context(|| format!("{:?} at {:#x}", i.mnemonic(), i.ip()))?;
    }
    code.fixed_refs = fixed_refs;
    Ok(code)
}

fn decode(vaddr: u64, bytes: &[u8]) -> Result<Vec<Instruction>> {
    let mut decoder = Decoder::with_ip(64, bytes, vaddr, DecoderOptions::NONE);
    let mut instructions = Vec::new();
    while decoder.can_decode() {
        let i = decoder.decode();
        ensure!(!i.is_invalid(), "undecodable bytes at {:#x}", i.ip());
        instructions.push(i);
    }
    Ok(instructions)
}

fn check_instruction(i: &Instruction) -> Result<()> {
    ensure!(
        AUDITED_MNEMONICS.contains(&i.mnemonic()),
        "{:?} is not audited",
        i.mnemonic()
    );
    ensure!(!i.has_lock_prefix(), "lock prefix");
    ensure!(
        !matches!(i.segment_prefix(), Register::FS | Register::GS),
        "fs/gs segment prefix"
    );
    Ok(())
}

fn check_control_flow(code: &Code, image: &Image, i: &Instruction) -> Result<()> {
    match i.flow_control() {
        FlowControl::Next | FlowControl::Return => {}
        FlowControl::ConditionalBranch | FlowControl::UnconditionalBranch => {
            let target = i.near_branch_target();
            ensure!(
                code.is_instruction_start(target),
                "branch to {target:#x} leaves the carved code"
            );
        }
        FlowControl::IndirectCall => {
            ensure!(
                i.is_ip_rel_memory_operand(),
                "indirect call not through a pointer slot"
            );
            let slot = i.ip_rel_memory_address();
            let target = image.relative_pointer(slot)?;
            ensure!(
                code.function_starting_at(target).is_some() || target == code.panic_entry.vaddr,
                "call through {slot:#x} goes to {target:#x}, outside the carved code"
            );
        }
        other => bail!("{other:?} control flow"),
    }
    Ok(())
}

fn fixed_ref(info: &mut InstructionInfoFactory, i: &Instruction) -> Result<Option<FixedRef>> {
    let rip_target = i
        .is_ip_rel_memory_operand()
        .then(|| i.ip_rel_memory_address());
    let mut read = None;
    for memory in info.info(i).used_memory() {
        // Through argument pointers or the stack pointer.
        if memory.base() != Register::None || memory.index() != Register::None {
            continue;
        }
        // iced resolves rip-relative operands to their target and drops the base.
        let target = memory.displacement();
        ensure!(
            rip_target == Some(target),
            "absolute memory address {target:#x}"
        );
        ensure!(
            memory.access() == OpAccess::Read,
            "{:?} access to fixed memory",
            memory.access()
        );
        read = Some(RefUse::Read {
            size: memory.memory_size().size() as u64,
        });
    }

    let Some(target) = rip_target else {
        return Ok(None);
    };
    let use_ = match read {
        Some(read) => read,
        // lea computes an address without accessing memory, so iced lists no access.
        None if i.mnemonic() == Mnemonic::Lea => RefUse::AddressOnly,
        None => bail!("rip-relative operand {target:#x} is neither read nor lea'd"),
    };
    Ok(Some(FixedRef { target, use_ }))
}
