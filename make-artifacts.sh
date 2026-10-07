#!/usr/bin/env bash
# Carves validate_fee_payer out of the binary build.sh produced, into artifacts/.
#
# Re-runs itself inside the CI image: the carve tool measures Rust layouts,
# which has to happen on the validator's target (x86_64-linux), and that
# image's binutils assemble and check the standalone ELF.
set -euo pipefail

if [[ -z ${VFP_IN_CI_IMAGE:-} ]]; then
  source "$(dirname "$0")/ci-image.sh"
  check_pins
  run_in_ci_image --env VFP_IN_CI_IMAGE=1 -- /vfp/make-artifacts.sh
  exit
fi

# In the container: this repository is /vfp, agave and build.sh's output /solana.
cd /vfp
binary=/solana/target/install/bin/agave-validator
out=artifacts

rm -rf "$out"
cargo run --locked --release --quiet \
  --manifest-path carve/Cargo.toml --target-dir /solana/target/carve \
  -- "$binary" "$out" lean/ValidateFeePayer/Image.lean
cd "$out"

as --64 -o standalone.o standalone.S
ld -T standalone.ld -static --build-id=none -z max-page-size=4096 -z noexecstack \
  -o validate_fee_payer.elf standalone.o
rm standalone.o

# llvm-objdump prints negative displacements as such ([rip - 0x2502520]).
for syntax in intel att; do
  llvm-objdump-14 -d --print-imm-hex --x86-asm-syntax="$syntax" validate_fee_payer.elf | sed '/file format/d' \
    > "validate_fee_payer.$syntax.s"
done

# Each carved function must disassemble exactly as in the source binary,
# addresses and rip-relative targets included. GNU objdump is used here as a
# decoder independent of both LLVM (which compiled the code) and iced (which
# the carve tool uses). Symbol names are dropped: the
# source labels its data with compiler-generated names.
instructions() {
  objdump -d -M intel --disassemble="$2" "$1" | sed -E 's/ *<[^>]*>//g' | grep -E '^ +[0-9a-f]+:'
}
functions=$(jq -r '.functions[] | "\(.name) \(.symbol)"' manifest.json)
[[ $(wc -l <<< "$functions") -eq 2 ]] || { echo "expected 2 carved functions" >&2; exit 1; }
while read -r name symbol; do
  expected=$(instructions "$binary" "$symbol")
  [[ -n $expected && $expected == "$(instructions validate_fee_payer.elf "$name")" ]] ||
    { echo "$name: carved code differs from $binary" >&2; exit 1; }
done <<< "$functions"

sha256sum -- * > SHA256SUMS
echo "artifacts written to $out"
