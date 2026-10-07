# Sourced by build.sh and make-artifacts.sh.

GIT_COMMIT=5770743629fb9e4d5c2e9ef0009c155f7787b57f
# The tag ci/docker/env.sh selects for GIT_COMMIT, pinned by digest.
CI_IMAGE_TAG=anzaxyz/ci:ubuntu-22.04_rust-1.98.1_nightly-2026-07-16_3e0cd9be
CI_IMAGE=anzaxyz/ci@sha256:c555c86cc007a2e48503d6875b84c40b15c8e75bcaae642d3042320e1b269903

REPO=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
# The agave submodule, at GIT_COMMIT.
AGAVE=$REPO/agave

# Everything the container writes outside the two mounted repositories:
# cargo's target dir (mounted at /solana/target) and the crate registry cache.
VFP_CACHE="${VFP_CACHE:-$REPO/cache}"

fail() {
  echo "${0##*/}: $*" >&2
  exit 1
}

check_pins() {
  command -v docker > /dev/null || fail "docker not on PATH (Docker Desktop installs it in ~/.docker/bin)"
  [[ $(git -C "$AGAVE" rev-parse HEAD 2> /dev/null) == "$GIT_COMMIT" ]] ||
    fail "agave/ is not at $GIT_COMMIT (git submodule update --init)"
  git -C "$AGAVE" diff --quiet HEAD || fail "tracked files in agave/ are modified"
  [[ $(cd "$AGAVE" && source ci/docker/env.sh && echo "$CI_DOCKER_IMAGE") == "$CI_IMAGE_TAG" ]] ||
    fail "ci/docker/env.sh no longer selects $CI_IMAGE_TAG; update the pin"
}

# run_in_ci_image [docker run options]... -- command [args]...
#
# Runs command through agave's ci/docker-run.sh, the wrapper CI uses, which
# mounts agave/ at /solana and starts there. This repository is mounted at
# /vfp. docker-run.sh splits EXTRA_DOCKER_RUN_ARGS on whitespace, so neither
# the options nor the paths may contain spaces.
#
# Git is disabled in the container (GIT_DIR points nowhere), so agave's
# version/build.rs does not embed the commit hash and the binary does not
# depend on how agave/ was checked out. The pinned binary was built this way;
# with the hash embedded its sha256 differs.
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
    --volume $REPO:/vfp \
    --volume $VFP_CACHE/target:/solana/target \
    --volume $VFP_CACHE/cargo-registry:/usr/local/cargo/registry \
    --env GIT_DIR=/nonexistent \
    ${options[*]}" \
    "$AGAVE/ci/docker-run.sh" --nopull "$CI_IMAGE" "$@"
}
