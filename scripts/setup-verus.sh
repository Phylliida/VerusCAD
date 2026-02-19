#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/lib/sanitize-rust-env.sh"

ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
VERUS_ROOT="${VERUS_ROOT:-$ROOT_DIR/../verus}"
VERUS_SOURCE="$VERUS_ROOT/source"
TOOLCHAIN="${VERUS_TOOLCHAIN:-1.93.0-x86_64-unknown-linux-gnu}"

if ! command -v nix-shell >/dev/null 2>&1; then
  echo "error: nix-shell is required for this setup script."
  exit 1
fi

if [[ ! -d "$VERUS_SOURCE" ]]; then
  echo "error: expected Verus source checkout at: $VERUS_SOURCE"
  echo "set VERUS_ROOT to override."
  exit 1
fi

echo "[1/4] Building Verus tools (vargo, verus, cargo-verus)"
nix-shell -p rustup --run "
  set -euo pipefail
  rustup toolchain install $TOOLCHAIN >/dev/null 2>&1 || true
  rustup default $TOOLCHAIN >/dev/null
  cd '$VERUS_SOURCE'
  source ../tools/activate
  vargo build --release --vstd-no-verify
"

echo "[2/4] Downloading Z3 4.12.5 locally into verus/source/z3"
nix-shell -p rustup --run "
  set -euo pipefail
  cd '$VERUS_SOURCE'
  if [[ ! -f z3 ]]; then
    bash ./tools/get-z3.sh
  fi
"

echo "[3/4] Patching local z3 binary for NixOS dynamic linker"
nix-shell -p patchelf stdenv.cc.cc.lib --run "
  set -euo pipefail
  z3bin='$VERUS_SOURCE/z3'
  dyn=\$(cat \"\$NIX_CC\"/nix-support/dynamic-linker)
  gcc_lib=''
  for tok in \$NIX_LDFLAGS; do
    case \"\$tok\" in
      -L*) gcc_lib=\"\${tok#-L}\"; break ;;
    esac
  done
  glibc_lib=\$(dirname \"\$dyn\")
  patchelf --set-interpreter \"\$dyn\" --set-rpath \"\$gcc_lib:\$glibc_lib\" \"\$z3bin\"
  \"\$z3bin\" -version
"

echo "[4/4] Final Verus build using patched z3"
nix-shell -p rustup --run "
  set -euo pipefail
  rustup default $TOOLCHAIN >/dev/null
  export VERUS_Z3_PATH='$VERUS_SOURCE/z3'
  cd '$VERUS_SOURCE'
  source ../tools/activate
  vargo build --release --vstd-no-verify
"

echo "setup complete:"
echo "  - verus binary:       $VERUS_SOURCE/target-verus/release/verus"
echo "  - cargo-verus binary: $VERUS_SOURCE/target-verus/release/cargo-verus"
echo "  - z3 binary:          $VERUS_SOURCE/z3"
