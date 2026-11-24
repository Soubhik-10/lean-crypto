#!/usr/bin/env bash
set -Eeuo pipefail
ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)
cd -- "$ROOT"
exec cargo "+${RUST_TOOLCHAIN:-1.97.1}" run --release --locked -p lean-verifier \
    --example seed_aggregate_fuzz -- "$@"
