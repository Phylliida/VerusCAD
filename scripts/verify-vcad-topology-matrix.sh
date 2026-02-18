#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_ROOT="${VERUS_ROOT:-$ROOT_DIR/../verus}"
VERUS_SOURCE="$VERUS_ROOT/source"
TOOLCHAIN="${VERUS_TOOLCHAIN:-1.93.0-x86_64-unknown-linux-gnu}"

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

NIX_SHELL_USABLE=0
if command -v nix-shell >/dev/null 2>&1; then
  if nix-shell -p rustup --run "true" >/dev/null 2>&1; then
    NIX_SHELL_USABLE=1
  fi
fi

SHIM_DIR=""
cleanup() {
  if [[ -n "$SHIM_DIR" && -d "$SHIM_DIR" ]]; then
    rm -rf "$SHIM_DIR"
  fi
}
trap cleanup EXIT

setup_rustup_shim() {
  if [[ -n "$SHIM_DIR" && -x "$SHIM_DIR/rustup" ]]; then
    return
  fi

  local rustup_home="${RUSTUP_HOME:-$HOME/.rustup}"
  local toolchain_root="$rustup_home/toolchains/$TOOLCHAIN"
  local host_triple="x86_64-unknown-linux-gnu"
  local rustc_bin="$toolchain_root/bin/rustc"
  local cargo_bin="$toolchain_root/bin/cargo"
  local rustlib_dir="$toolchain_root/lib/rustlib/$host_triple/lib"

  if [[ ! -x "$VERUS_SOURCE/target-verus/release/cargo-verus" ]]; then
    echo "error: cargo-verus is not built yet at $VERUS_SOURCE/target-verus/release/cargo-verus"
    exit 1
  fi
  if [[ ! -x "$VERUS_SOURCE/z3" ]]; then
    echo "error: expected patched z3 at $VERUS_SOURCE/z3"
    exit 1
  fi
  if [[ ! -x "$rustc_bin" || ! -x "$cargo_bin" ]]; then
    echo "error: required rust toolchain binaries missing under $toolchain_root"
    echo "install toolchain $TOOLCHAIN or run with a working nix-shell environment."
    exit 1
  fi

  SHIM_DIR="$(mktemp -d)"
  cat > "$SHIM_DIR/rustup" <<EOF
#!/usr/bin/env bash
set -euo pipefail
TOOLCHAIN="$TOOLCHAIN"
TOOLCHAIN_ROOT="$toolchain_root"
RUSTC_BIN="$rustc_bin"
CARGO_BIN="$cargo_bin"
RUSTLIB_DIR="$rustlib_dir"

cmd="\${1:-}"
case "\$cmd" in
  toolchain)
    if [[ "\${2:-}" == "list" ]]; then
      echo "\$TOOLCHAIN (default)"
      exit 0
    fi
    ;;
  show)
    if [[ "\${2:-}" == "active-toolchain" ]]; then
      echo "\$TOOLCHAIN (default)"
      exit 0
    fi
    ;;
  default)
    exit 0
    ;;
  which)
    if [[ "\${2:-}" == "rustc" ]]; then
      echo "\$RUSTC_BIN"
      exit 0
    fi
    if [[ "\${2:-}" == "cargo" ]]; then
      echo "\$CARGO_BIN"
      exit 0
    fi
    ;;
  run)
    req_toolchain="\${2:-}"
    shift 2
    if [[ -z "\$req_toolchain" || "\$req_toolchain" != "\$TOOLCHAIN" ]]; then
      echo "rustup shim: unsupported toolchain '\$req_toolchain'" >&2
      exit 1
    fi
    if [[ \$# -eq 0 ]]; then
      echo "rustup shim: missing command for run" >&2
      exit 1
    fi
    export PATH="\$TOOLCHAIN_ROOT/bin:\$PATH"
    export LD_LIBRARY_PATH="\$TOOLCHAIN_ROOT/lib:\$RUSTLIB_DIR:\${LD_LIBRARY_PATH:-}"
    exec "\$@"
    ;;
esac

echo "rustup shim: unsupported command: \$*" >&2
exit 1
EOF
  chmod +x "$SHIM_DIR/rustup"
}

run_fast_verify() {
  if [[ $NIX_SHELL_USABLE -eq 1 ]]; then
    "$ROOT_DIR/scripts/verify-vcad-topology-fast.sh"
  else
    echo "note: nix-shell unavailable; using direct cargo-verus fallback for fast pass"
    setup_rustup_shim
    PATH="$SHIM_DIR:$VERUS_SOURCE/target-verus/release:$PATH" \
      VERUS_Z3_PATH="$VERUS_SOURCE/z3" \
      cargo verus verify \
      --manifest-path crates/vcad-topology/Cargo.toml \
      -p vcad-topology \
      --features verus-proofs \
      -- --verify-module runtime_halfedge_mesh_refinement --triggers-mode silent
  fi
}

run_full_verify() {
  if [[ $NIX_SHELL_USABLE -eq 1 ]]; then
    "$ROOT_DIR/scripts/verify-vcad-topology.sh"
  else
    echo "note: nix-shell unavailable; using direct cargo-verus fallback for full pass"
    setup_rustup_shim
    PATH="$SHIM_DIR:$VERUS_SOURCE/target-verus/release:$PATH" \
      VERUS_Z3_PATH="$VERUS_SOURCE/z3" \
      cargo verus verify \
      --manifest-path crates/vcad-topology/Cargo.toml \
      -p vcad-topology \
      --features verus-proofs \
      -- --triggers-mode silent
  fi
}

echo "==> [1/6] Trust-surface guard"
"$ROOT_DIR/scripts/check-vcad-topology-trust-surface.sh"

echo "==> [2/6] Fast topology verification"
run_fast_verify

echo "==> [3/6] Full topology verification"
run_full_verify

echo "==> [4/6] cargo test -p vcad-topology"
cargo test -p vcad-topology

echo "==> [5/6] cargo test -p vcad-topology --features geometry-checks"
cargo test -p vcad-topology --features geometry-checks

echo "==> [6/6] cargo test -p vcad-topology --features \"geometry-checks,verus-proofs\""
cargo test -p vcad-topology --features "geometry-checks,verus-proofs"

echo "==> vcad-topology matrix complete"
