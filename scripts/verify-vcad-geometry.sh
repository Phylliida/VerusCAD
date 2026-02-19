#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/lib/sanitize-rust-env.sh"

ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
VERUS_ROOT="${VERUS_ROOT:-$ROOT_DIR/../verus}"
VERUS_SOURCE="$VERUS_ROOT/source"
TOOLCHAIN="${VERUS_TOOLCHAIN:-1.93.0-x86_64-unknown-linux-gnu}"

if [[ ! -x "$VERUS_SOURCE/target-verus/release/cargo-verus" ]]; then
  echo "error: cargo-verus is not built yet."
  echo "run ./scripts/setup-verus.sh first."
  exit 1
fi

if [[ ! -x "$VERUS_SOURCE/z3" ]]; then
  echo "error: expected patched z3 at $VERUS_SOURCE/z3"
  echo "run ./scripts/setup-verus.sh first."
  exit 1
fi

nix-shell -p rustup --run "
  set -euo pipefail
  rustup default $TOOLCHAIN >/dev/null
  export PATH='$VERUS_SOURCE/target-verus/release':\$PATH
  export VERUS_Z3_PATH='$VERUS_SOURCE/z3'
  cd '$ROOT_DIR'
  cargo verus verify --manifest-path crates/vcad-geometry/Cargo.toml -p vcad-geometry --features verus-proofs -- --triggers-mode silent
"
