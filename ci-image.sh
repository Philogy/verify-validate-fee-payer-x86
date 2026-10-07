# Sourced by build.sh and make-artifacts.sh, from the repository root.

GIT_COMMIT=5770743629fb9e4d5c2e9ef0009c155f7787b57f
# The tag ci/docker/env.sh selects for GIT_COMMIT, pinned by digest.
CI_IMAGE_TAG=anzaxyz/ci:ubuntu-22.04_rust-1.98.1_nightly-2026-07-16_3e0cd9be
CI_IMAGE=anzaxyz/ci@sha256:c555c86cc007a2e48503d6875b84c40b15c8e75bcaae642d3042320e1b269903

# Everything the container writes outside the repository: cargo's target dir
# (mounted at /solana/target) and the crate registry cache. Kept apart from the
# host's own target/ so host and container builds never share a cache.
VFP_CACHE="${VFP_CACHE:-$PWD/target/vfp-docker}"

fail() {
  echo "${0##*/}: $*" >&2
  exit 1
}

check_pins() {
  command -v docker > /dev/null || fail "docker not on PATH (Docker Desktop installs it in ~/.docker/bin)"
  [[ $(git rev-parse HEAD) == "$GIT_COMMIT" ]] || fail "HEAD is not $GIT_COMMIT"
  git diff --quiet HEAD -- . ':!verify-validate-fee-payer' || fail "tracked files are modified"
  [[ $(source ci/docker/env.sh && echo "$CI_DOCKER_IMAGE") == "$CI_IMAGE_TAG" ]] ||
    fail "ci/docker/env.sh no longer selects $CI_IMAGE_TAG; update the pin"
}

# run_in_ci_image [docker run options]... -- command [args]...
#
# Runs command from /solana (the repository) through ci/docker-run.sh, the
# wrapper CI uses. docker-run.sh splits EXTRA_DOCKER_RUN_ARGS on whitespace,
# so neither the options nor VFP_CACHE may contain spaces.
run_in_ci_image() {
  local options=()
  while [[ $1 != -- ]]; do
    options+=("$1")
    shift
  done
  shift

  mkdir -p "$VFP_CACHE/target" "$VFP_CACHE/cargo-registry"
  docker image inspect "$CI_IMAGE" > /dev/null 2>&1 || docker pull --platform linux/amd64 "$CI_IMAGE"
  EXTRA_DOCKER_RUN_ARGS="--platform linux/amd64 \
    --volume $VFP_CACHE/target:/solana/target \
    --volume $VFP_CACHE/cargo-registry:/usr/local/cargo/registry \
    ${options[*]}" \
    ci/docker-run.sh --nopull "$CI_IMAGE" "$@"
}
