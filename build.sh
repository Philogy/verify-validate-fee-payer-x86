#!/usr/bin/env bash
# Builds agave-validator with the release build script, inside the CI image.
# Output: $VFP_CACHE/target/install/bin/agave-validator.
#
# Deviations from a release build, none of which affect code generation:
#   - dcou dev tools, platform-tools and spl-token are not built;
#   - CARGO_PROFILE_RELEASE_STRIP=none keeps the symbol table, which the
#     carve tool uses to find functions;
#   - SOURCE_DATE_EPOCH is the commit time. Otherwise OpenSSL embeds the
#     wall-clock build time, which shifts .rodata and with it the rip-relative
#     displacements in unrelated code.
set -euo pipefail
cd "$(dirname "$0")/.."
source verify-validate-fee-payer/ci-image.sh
check_pins

run_in_ci_image \
  --env CARGO_PROFILE_RELEASE_STRIP=none \
  --env "SOURCE_DATE_EPOCH=$(git log -1 --format=%ct)" \
  -- \
  scripts/cargo-install-all.sh --no-build-dcou-bins --no-build-platform-tools --no-spl-token \
  /solana/target/install
