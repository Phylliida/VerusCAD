#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_ROOT="${VERUS_ROOT:-$ROOT_DIR/../verus}"
VERUS_SOURCE="$VERUS_ROOT/source"
TOOLCHAIN="${VERUS_TOOLCHAIN:-1.93.0-x86_64-unknown-linux-gnu}"
RUSTUP_HOME_DIR="${RUSTUP_HOME:-$HOME/.rustup}"
SHIM_DIR=""

"$ROOT_DIR/scripts/check-vcad-operators-trust-surface.sh"

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

  local toolchain_root="$RUSTUP_HOME_DIR/toolchains/$TOOLCHAIN"
  local host_triple="x86_64-unknown-linux-gnu"
  local rustc_bin="$toolchain_root/bin/rustc"
  local cargo_bin="$toolchain_root/bin/cargo"
  local rustlib_dir="$toolchain_root/lib/rustlib/$host_triple/lib"

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

NIX_SHELL_USABLE=0
if command -v nix-shell >/dev/null 2>&1; then
  if nix-shell -p rustup --run "true" >/dev/null 2>&1; then
    NIX_SHELL_USABLE=1
  fi
fi

if [[ $NIX_SHELL_USABLE -eq 1 ]]; then
  nix-shell -p rustup --run "
    set -euo pipefail
    rustup default $TOOLCHAIN >/dev/null
    export PATH='$VERUS_SOURCE/target-verus/release':\$PATH
    export VERUS_Z3_PATH='$VERUS_SOURCE/z3'
    cd '$ROOT_DIR'
    cargo verus verify --manifest-path crates/vcad-operators/Cargo.toml -p vcad-operators --features verus-proofs -- --triggers-mode silent
  "
else
  echo "note: nix-shell unavailable; using direct cargo-verus fallback"
  setup_rustup_shim
  PATH="$SHIM_DIR:$VERUS_SOURCE/target-verus/release:$PATH" \
    VERUS_Z3_PATH="$VERUS_SOURCE/z3" \
    cargo verus verify \
    --manifest-path crates/vcad-operators/Cargo.toml \
    -p vcad-operators \
    --features verus-proofs \
    -- --triggers-mode silent
fi
