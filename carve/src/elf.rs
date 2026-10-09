//! The source binary as the loader would see it: bytes at virtual addresses,
//! symbols, and the relocations applied at load time.
//!
//! Load base 0 is assumed throughout. At base `B` every address, and the value
//! of every relocated word, is shifted by `B`.

use {
    anyhow::{Context, Result, bail, ensure},
    object::{Object, ObjectSegment, ObjectSymbol, RelocationFlags, SymbolKind, elf},
    std::{collections::BTreeMap, fs, path::Path},
};

pub struct Image {
    pub bytes: &'static [u8],
    file: object::File<'static>,
    /// Address of each relocated 8-byte word -> relocation.
    relocations: BTreeMap<u64, Reloc>,
}

#[derive(Clone, Copy)]
enum Reloc {
    /// R_X86_64_RELATIVE: the loader writes `B + value`.
    Relative { value: u64 },
    /// Anything that needs symbol resolution, e.g. an import from libc.
    Other { r_type: u32 },
}

/// A relocated word inside a range read with [`Image::read_relocated`].
pub struct Relocation {
    pub offset: u64,
    pub value: u64,
}

pub struct Symbol {
    pub name: String,
    pub vaddr: u64,
    pub size: u64,
}

impl Image {
    pub fn load(path: &Path) -> Result<Self> {
        let bytes = fs::read(path).with_context(|| format!("reading {}", path.display()))?;
        // Kept for the whole run, so object::File can borrow it as 'static.
        let bytes: &'static [u8] = Box::leak(bytes.into_boxed_slice());
        let file = object::File::parse(bytes)?;
        ensure!(
            file.format() == object::BinaryFormat::Elf
                && file.architecture() == object::Architecture::X86_64,
            "{} is not an x86-64 ELF",
            path.display()
        );

        let mut relocations = BTreeMap::new();
        for (address, relocation) in file.dynamic_relocations().into_iter().flatten() {
            let reloc = match relocation.flags() {
                RelocationFlags::Elf {
                    r_type: elf::R_X86_64_RELATIVE,
                } => Reloc::Relative {
                    value: relocation.addend() as u64,
                },
                RelocationFlags::Elf { r_type } => Reloc::Other { r_type },
                flags => bail!("unexpected relocation {flags:?} at {address:#x}"),
            };
            relocations.insert(address, reloc);
        }
        Ok(Self {
            bytes,
            file,
            relocations,
        })
    }

    /// Bytes as stored in the file. Relocated words are not filled in.
    pub fn read(&self, vaddr: u64, len: u64) -> Result<&'static [u8]> {
        for segment in self.file.segments() {
            if let Some(bytes) = segment.data_range(vaddr, len)? {
                return Ok(bytes);
            }
        }
        bail!("{vaddr:#x}..{:#x} is not backed by the file", vaddr + len)
    }

    /// Bytes as they are in memory after loading at base 0.
    pub fn read_relocated(&self, vaddr: u64, len: u64) -> Result<(Vec<u8>, Vec<Relocation>)> {
        let mut bytes = self.read(vaddr, len)?.to_vec();
        let mut applied = Vec::new();
        // A word starting up to 7 bytes before the range would overlap it.
        for (&address, &reloc) in self.relocations.range(vaddr.saturating_sub(7)..vaddr + len) {
            ensure!(
                address >= vaddr && address + 8 <= vaddr + len,
                "relocated word at {address:#x} straddles {vaddr:#x}..{:#x}",
                vaddr + len
            );
            let Reloc::Relative { value } = reloc else {
                bail!("{address:#x} needs symbol resolution ({reloc:?})");
            };
            let offset = address - vaddr;
            bytes[offset as usize..][..8].copy_from_slice(&value.to_le_bytes());
            applied.push(Relocation { offset, value });
        }
        Ok((bytes, applied))
    }

    /// Value of the pointer the loader writes at `vaddr`, minus the load base.
    pub fn relative_pointer(&self, vaddr: u64) -> Result<u64> {
        match self.relocations.get(&vaddr) {
            Some(Reloc::Relative { value }) => Ok(*value),
            Some(reloc) => bail!("{vaddr:#x} needs symbol resolution ({reloc:?})"),
            None => bail!("{vaddr:#x} is not a relocated pointer"),
        }
    }

    /// `[start, end)` from the lowest `p_vaddr` to the highest `p_vaddr +
    /// p_memsz` over the `PT_LOAD` segments: everything the loader reserves.
    pub fn loaded_span(&self) -> Result<(u64, u64)> {
        let spans: Vec<(u64, u64)> = self
            .file
            .segments()
            .map(|s| (s.address(), s.address() + s.size()))
            .collect();
        ensure!(!spans.is_empty(), "no PT_LOAD segments");
        let start = spans.iter().map(|s| s.0).min().unwrap_or_default();
        let end = spans.iter().map(|s| s.1).max().unwrap_or_default();
        Ok((start, end))
    }

    pub fn is_relocated(&self, vaddr: u64) -> bool {
        self.relocations.contains_key(&vaddr)
    }

    /// The function symbol of a non-generic Rust item, e.g.
    /// `["solana_svm", "account_loader", "validate_fee_payer"]`.
    ///
    /// rustc's v0 mangling ends in the length-prefixed path components, after
    /// the `_` that terminates the crate's hash. Matching that suffix avoids
    /// depending on the hash.
    pub fn rust_fn(&self, path: &[&str]) -> Result<Symbol> {
        let suffix: String = path
            .iter()
            .map(|part| format!("{}{part}", part.len()))
            .collect();
        let suffix = format!("_{suffix}");
        let matches: Vec<Symbol> = self
            .file
            .symbols()
            .filter(|s| s.kind() == SymbolKind::Text)
            .filter_map(|s| {
                let name = s.name().ok()?;
                (name.starts_with("_R") && name.ends_with(&suffix)).then(|| Symbol {
                    name: name.to_owned(),
                    vaddr: s.address(),
                    size: s.size(),
                })
            })
            .collect();
        let [symbol] = <[Symbol; 1]>::try_from(matches).map_err(|m| {
            anyhow::anyhow!(
                "{}: {} matching symbols, expected 1",
                path.join("::"),
                m.len()
            )
        })?;
        Ok(symbol)
    }
}

impl std::fmt::Debug for Reloc {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Reloc::Relative { value } => write!(f, "R_X86_64_RELATIVE {value:#x}"),
            Reloc::Other { r_type } => write!(f, "relocation type {r_type}"),
        }
    }
}
