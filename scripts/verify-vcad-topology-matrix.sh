#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/lib/sanitize-rust-env.sh"

ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  cat <<'USAGE'
usage: ./scripts/verify-vcad-topology-matrix.sh

Runs the full vcad-topology verification/test matrix:
  1) trust-surface guard
  2) fast topology verification
  3) full topology verification
  4) cargo test -p vcad-topology
  5) cargo test -p vcad-topology --features geometry-checks
  6) cargo test -p vcad-topology --features "geometry-checks,verus-proofs"
USAGE
  exit 0
fi

if [[ $# -ne 0 ]]; then
  echo "error: expected zero arguments"
  exit 1
fi

cd "$ROOT_DIR"

echo "==> [1/6] Trust-surface guard"
"$ROOT_DIR/scripts/check-vcad-topology-trust-surface.sh"

echo "==> [2/6] Fast topology verification"
"$ROOT_DIR/scripts/verify-vcad-topology-fast.sh"

echo "==> [3/6] Full topology verification"
"$ROOT_DIR/scripts/verify-vcad-topology.sh"

echo "==> [4/6] cargo test -p vcad-topology"
cargo test -p vcad-topology

echo "==> [5/6] cargo test -p vcad-topology --features geometry-checks"
cargo test -p vcad-topology --features geometry-checks

echo "==> [6/6] cargo test -p vcad-topology --features \"geometry-checks,verus-proofs\""
cargo test -p vcad-topology --features "geometry-checks,verus-proofs"

echo "==> vcad-topology matrix complete"
