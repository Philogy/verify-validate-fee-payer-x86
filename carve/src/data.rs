//! Identifies and copies out the fixed memory the carved code references.
//!
//! Bytes the code reads are carved exactly as wide as they are read. Objects
//! whose address is only passed on (the panic arguments) are carved whole.
//! Every object must be recognised by its contents or by what it points to.

use {
    crate::{
        code::{Code, RefUse},
        elf::{Image, Relocation},
        hex,
    },
    anyhow::{Context, Result, bail, ensure},
    std::{collections::BTreeSet, panic::Location},
};

pub struct DataObject {
    pub name: String,
    pub vaddr: u64,
    /// As in memory after loading at base 0.
    pub bytes: Vec<u8>,
    pub relocations: Vec<Relocation>,
    pub read_by_code: bool,
    pub description: String,
}

impl DataObject {
    fn end(&self) -> u64 {
        self.vaddr + self.bytes.len() as u64
    }
}

struct Known {
    name: &'static str,
    bytes: Vec<u8>,
    description: &'static str,
}

fn read_constants() -> Vec<Known> {
    vec![
        Known {
            name: "system_program_id",
            bytes: solana_sdk_ids::system_program::ID.to_bytes().to_vec(),
            description: "solana_sdk_ids::system_program::ID, compared against the account owner",
        },
        Known {
            name: "u64_to_f64_exponents",
            bytes: u32s(&[0x4330_0000, 0x4530_0000, 0, 0]),
            description: "u64 -> f64: high words of 2^52 and 2^84, spliced onto the u64's halves",
        },
        Known {
            name: "u64_to_f64_bias",
            bytes: f64s(&[2f64.powi(52), 2f64.powi(84)]),
            description: "u64 -> f64: subtracted to recover each half as an f64",
        },
        Known {
            name: "f64_2pow63",
            bytes: f64s(&[2f64.powi(63)]),
            description: "f64 -> u64: values >= 2^63 are converted after subtracting 2^63",
        },
        Known {
            name: "f64_max_below_2pow64",
            bytes: f64s(&[2f64.powi(64) - 2f64.powi(11)]),
            description: "f64 -> u64: the cast saturates above the largest f64 below 2^64",
        },
    ]
}

fn address_only_constants() -> Vec<Known> {
    vec![Known {
        name: "panic_msg",
        bytes: b"Maximum permitted data length exceeded".to_vec(),
        description: "message of the expect() in Rent::minimum_balance",
    }]
}

pub fn carve(image: &Image, code: &Code) -> Result<Vec<DataObject>> {
    let mut objects = Vec::new();
    for (start, end) in read_ranges(code) {
        objects.push(read_object(image, code, start, end).with_context(|| format!("{start:#x}"))?);
    }
    let address_only: BTreeSet<u64> = code
        .fixed_refs
        .iter()
        .filter(|r| r.use_ == RefUse::AddressOnly)
        .map(|r| r.target)
        .collect();
    for target in address_only {
        if !objects.iter().any(|o| (o.vaddr..o.end()).contains(&target)) {
            objects.extend(
                address_only_objects(image, target).with_context(|| format!("{target:#x}"))?,
            );
        }
    }

    objects.sort_by_key(|o| o.vaddr);
    for pair in objects.windows(2) {
        ensure!(
            pair[0].end() <= pair[1].vaddr,
            "{} overlaps {}",
            pair[0].name,
            pair[1].name
        );
    }
    let names: BTreeSet<_> = objects.iter().map(|o| &o.name).collect();
    ensure!(
        names.len() == objects.len(),
        "two objects with the same name"
    );
    Ok(objects)
}

/// Byte ranges the code reads, with overlapping or adjacent reads merged, e.g.
/// the two 16-byte halves of a Pubkey.
fn read_ranges(code: &Code) -> Vec<(u64, u64)> {
    let mut reads: Vec<(u64, u64)> = code
        .fixed_refs
        .iter()
        .filter_map(|r| match r.use_ {
            RefUse::Read { size } => Some((r.target, r.target + size)),
            RefUse::AddressOnly => None,
        })
        .collect();
    reads.sort();
    let mut merged: Vec<(u64, u64)> = Vec::new();
    for (start, end) in reads {
        match merged.last_mut() {
            Some(last) if start <= last.1 => last.1 = last.1.max(end),
            _ => merged.push((start, end)),
        }
    }
    merged
}

fn read_object(image: &Image, code: &Code, start: u64, end: u64) -> Result<DataObject> {
    let (bytes, relocations) = image.read_relocated(start, end - start)?;

    if let [Relocation { offset: 0, value }] = relocations[..]
        && bytes.len() == 8
    {
        let (name, target) = if value == code.panic_entry.vaddr {
            ("expect_failed", "core::option::expect_failed".to_owned())
        } else if let Some(f) = code.function_starting_at(value) {
            (f.name, f.name.to_owned())
        } else {
            bail!("pointer slot holding {value:#x}, which is not a carved function");
        };
        return Ok(DataObject {
            name: format!("got_{name}"),
            vaddr: start,
            bytes,
            relocations,
            read_by_code: true,
            description: format!("pointer slot, loaded with B + {value:#x} ({target})"),
        });
    }

    ensure!(relocations.is_empty(), "relocated words inside a constant");
    let Some(known) = read_constants().into_iter().find(|k| k.bytes == bytes) else {
        bail!("unrecognised constant {}", hex::bytes(&bytes));
    };
    Ok(DataObject {
        name: known.name.to_owned(),
        vaddr: start,
        bytes,
        relocations,
        read_by_code: true,
        description: known.description.to_owned(),
    })
}

fn address_only_objects(image: &Image, target: u64) -> Result<Vec<DataObject>> {
    if image.is_relocated(target) {
        return panic_location(image, target);
    }
    for known in address_only_constants() {
        if image
            .read(target, known.bytes.len() as u64)
            .is_ok_and(|b| b == known.bytes)
        {
            return Ok(vec![DataObject {
                name: known.name.to_owned(),
                vaddr: target,
                bytes: known.bytes,
                relocations: vec![],
                read_by_code: false,
                description: format!("{}; passed to expect_failed", known.description),
            }]);
        }
    }
    bail!(
        "unrecognised object {}",
        hex::bytes(image.read(target, 32)?)
    )
}

/// A `core::panic::Location { file: &str, line: u32, col: u32 }` and the file
/// name it points to. The field order is this toolchain's; it is confirmed by
/// the file pointer being the relocated word and pointing at a `.rs` path.
fn panic_location(image: &Image, vaddr: u64) -> Result<Vec<DataObject>> {
    let size = size_of::<Location<'static>>() as u64;
    let (bytes, relocations) = image.read_relocated(vaddr, size)?;
    let [
        Relocation {
            offset: 0,
            value: file_ptr,
        },
    ] = relocations[..]
    else {
        bail!("relocated object that is not a panic Location");
    };
    let file_len = u64::from_le_bytes(bytes[8..16].try_into()?);
    let line = u32::from_le_bytes(bytes[16..20].try_into()?);
    let col = u32::from_le_bytes(bytes[20..24].try_into()?);
    let file_bytes = image.read(file_ptr, file_len)?;
    let file = std::str::from_utf8(file_bytes)?;
    ensure!(
        file.ends_with(".rs"),
        "Location file {file:?} is not a Rust source path"
    );

    Ok(vec![
        DataObject {
            name: "panic_location".to_owned(),
            vaddr,
            bytes,
            relocations,
            read_by_code: false,
            description: format!(
                "core::panic::Location {{ {file}, line {line}, col {col} }}; passed to expect_failed"
            ),
        },
        DataObject {
            name: "panic_location_file".to_owned(),
            vaddr: file_ptr,
            bytes: file_bytes.to_vec(),
            relocations: vec![],
            read_by_code: false,
            description: "file name referenced by panic_location".to_owned(),
        },
    ])
}

fn u32s(values: &[u32]) -> Vec<u8> {
    values.iter().flat_map(|v| v.to_le_bytes()).collect()
}

fn f64s(values: &[f64]) -> Vec<u8> {
    values.iter().flat_map(|v| v.to_le_bytes()).collect()
}
