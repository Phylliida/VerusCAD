#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_ROOT="${VERUS_ROOT:-$ROOT_DIR/../verus}"
VERUS_SOURCE="$VERUS_ROOT/source"
TOOLCHAIN="${VERUS_TOOLCHAIN:-1.93.0-x86_64-unknown-linux-gnu}"

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  cat <<'EOF'
usage: ./scripts/verify-vcad-geometry-fast.sh [module] [function_pattern]

examples:
  ./scripts/verify-vcad-geometry-fast.sh
  ./scripts/verify-vcad-geometry-fast.sh runtime_orientation_predicates_refinement
  ./scripts/verify-vcad-geometry-fast.sh runtime_sidedness_refinement runtime_segment_crosses_plane_from_opposite_sides
EOF
  exit 0
fi

if [[ $# -gt 2 ]]; then
  echo "error: expected at most 2 args: [module] [function_pattern]"
  exit 1
fi

MODULE="${1:-runtime_orientation_predicates_refinement}"
FUNCTION_PATTERN="${2:-}"

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

if [[ -n "$FUNCTION_PATTERN" ]]; then
  VERIFY_SCOPE="--verify-only-module '$MODULE' --verify-function '$FUNCTION_PATTERN'"
else
  VERIFY_SCOPE="--verify-only-module '$MODULE'"
fi

nix-shell -p rustup --run "
  set -euo pipefail
  rustup default $TOOLCHAIN >/dev/null
  export PATH='$VERUS_SOURCE/target-verus/release':\$PATH
  export VERUS_Z3_PATH='$VERUS_SOURCE/z3'
  cd '$ROOT_DIR'
  cargo verus verify --manifest-path crates/vcad-geometry/Cargo.toml -p vcad-geometry --features verus-proofs -- $VERIFY_SCOPE --triggers-mode silent
"
