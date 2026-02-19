#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  cat <<'EOF'
usage: ./scripts/test-vcad-geometry-verus-proofs.sh [cargo_test_args...]

Runs:
  cargo test -p vcad-geometry --features verus-proofs

with a sanitized environment to avoid accidental ghost/proof cfg leakage from:
  RUSTFLAGS
  CARGO_ENCODED_RUSTFLAGS

examples:
  ./scripts/test-vcad-geometry-verus-proofs.sh
  ./scripts/test-vcad-geometry-verus-proofs.sh segment_intersection::tests::segment_intersection_proper_crossing
  ./scripts/test-vcad-geometry-verus-proofs.sh -- --nocapture
EOF
  exit 0
fi

source "$SCRIPT_DIR/lib/sanitize-rust-env.sh"

ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT_DIR"

cargo test -p vcad-geometry --features verus-proofs "$@"
