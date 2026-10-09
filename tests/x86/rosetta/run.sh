#!/bin/sh
# Runs the vectors under Rosetta (Docker's linux/amd64 on Apple silicon) and
# compares the model with the outcomes, AF and Rosetta's known artefacts set
# aside. A quick local reference point; CI's CPU remains the oracle.
#   tests/x86/rosetta/run.sh [outcomes dir, default /tmp/x86-rosetta]
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
out=${1:-/tmp/x86-rosetta}
image=vfp-x86-oracle
docker image inspect "$image" >/dev/null 2>&1 || docker build --platform linux/amd64 -t "$image" - <<'DOCKERFILE'
FROM debian:bookworm-slim
RUN apt-get update -q && apt-get install -y -q --no-install-recommends gcc libc6-dev && rm -rf /var/lib/apt/lists/*
DOCKERFILE
mkdir -p "$out"
docker run --rm --platform linux/amd64 -v "$here:/x86:ro" -v "$out:/out" "$image" sh -ec '
  grep -q VirtualApple /proc/cpuinfo || echo "warning: not running under Rosetta" >&2
  gcc -O2 -Wall -Werror -o /tmp/oracle /x86/rosetta/oracle_signals.c
  for f in /x86/vectors/*.txt; do /tmp/oracle < "$f" > "/out/$(basename "$f")"; done'
"$here/../../lean/.lake/build/bin/x86-test" rosetta "$here" "$out"
