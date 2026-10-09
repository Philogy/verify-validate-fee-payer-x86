//! Carves `validate_fee_payer` out of an `agave-validator` ELF and measures the
//! layout of the values it works on. See ../README.md.
//!
//! Usage: vfp-carve <agave-validator> <output dir> <Image.lean>

mod code;
mod data;
mod elf;
mod hex;
mod layout;
mod lean;
mod manifest;
mod standalone;

use {
    anyhow::{Result, bail},
    std::{env, fs, path::Path},
};

fn main() -> Result<()> {
    let args: Vec<_> = env::args_os().skip(1).collect();
    let [binary, out, lean_module] = &args[..] else {
        bail!("usage: vfp-carve <agave-validator> <output dir> <Image.lean>");
    };
    let out = Path::new(out);

    let image = elf::Image::load(Path::new(binary))?;
    let code = code::carve(&image)?;
    let data = data::carve(&image, &code)?;
    let layout = layout::measure()?;
    layout::check_result_tags(&layout, &code)?;

    fs::create_dir_all(out)?;
    for function in &code.functions {
        fs::write(out.join(format!("{}.bin", function.name)), function.bytes)?;
    }
    fs::write(out.join("standalone.S"), standalone::assembly(&code, &data))?;
    fs::write(
        out.join("standalone.ld"),
        standalone::linker_script(&code, &data),
    )?;
    let manifest = manifest::build(&image, &code, &data, &layout);
    fs::write(
        out.join("manifest.json"),
        serde_json::to_string_pretty(&manifest)? + "\n",
    )?;
    let source_sha256 = manifest::sha256(image.bytes);
    fs::write(
        lean_module,
        lean::module(&source_sha256, &code, &data, &layout, image.loaded_span()?)?,
    )?;
    Ok(())
}
