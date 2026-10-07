//! `manifest.json`: everything needed to rebuild the memory image and the
//! argument layout without reading the ELF.

use {
    crate::{
        code::Code,
        data::DataObject,
        elf::Image,
        hex::{self, Hex},
        layout::Layout,
    },
    serde::Serialize,
    sha2::{Digest, Sha256},
    std::collections::BTreeMap,
};

#[derive(Serialize)]
pub struct Manifest<'a> {
    source_sha256: String,
    load_base: &'static str,
    functions: Vec<FunctionEntry>,
    data: Vec<DataEntry>,
    panic_entry: PanicEntry,
    mnemonics: BTreeMap<String, usize>,
    layout: &'a Layout,
}

#[derive(Serialize)]
struct FunctionEntry {
    name: &'static str,
    symbol: String,
    vaddr: Hex,
    size: Hex,
    sha256: String,
    file: String,
}

#[derive(Serialize)]
struct DataEntry {
    name: String,
    vaddr: Hex,
    size: Hex,
    bytes: String,
    read_by_code: bool,
    relocations: Vec<RelocationEntry>,
    description: String,
}

#[derive(Serialize)]
struct RelocationEntry {
    offset: Hex,
    value: Hex,
}

#[derive(Serialize)]
struct PanicEntry {
    symbol: String,
    vaddr: Hex,
}

pub fn build<'a>(
    image: &Image,
    code: &Code,
    data: &[DataObject],
    layout: &'a Layout,
) -> Manifest<'a> {
    let mut mnemonics = BTreeMap::new();
    for i in code.instructions() {
        *mnemonics
            .entry(format!("{:?}", i.mnemonic()).to_lowercase())
            .or_default() += 1;
    }
    Manifest {
        source_sha256: sha256(image.bytes),
        load_base: "addresses assume load base 0; at base B add B to every address and to every relocation value",
        functions: code
            .functions
            .iter()
            .map(|f| FunctionEntry {
                name: f.name,
                symbol: f.symbol.clone(),
                vaddr: Hex(f.vaddr),
                size: Hex(f.bytes.len() as u64),
                sha256: sha256(f.bytes),
                file: format!("{}.bin", f.name),
            })
            .collect(),
        data: data
            .iter()
            .map(|o| DataEntry {
                name: o.name.clone(),
                vaddr: Hex(o.vaddr),
                size: o.bytes.len().into(),
                bytes: hex::bytes(&o.bytes),
                read_by_code: o.read_by_code,
                relocations: o
                    .relocations
                    .iter()
                    .map(|r| RelocationEntry {
                        offset: Hex(r.offset),
                        value: Hex(r.value),
                    })
                    .collect(),
                description: o.description.clone(),
            })
            .collect(),
        panic_entry: PanicEntry {
            symbol: code.panic_entry.name.clone(),
            vaddr: Hex(code.panic_entry.vaddr),
        },
        mnemonics,
        layout,
    }
}

pub fn sha256(bytes: &[u8]) -> String {
    hex::bytes(&Sha256::digest(bytes))
}
