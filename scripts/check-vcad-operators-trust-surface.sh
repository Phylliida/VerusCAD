#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OPERATORS_SRC_DIR="$ROOT_DIR/crates/vcad-operators/src"
TRUST_PATTERN='assume_specification|external_fn_specification|\buninterpreted\b|admit\(|assume\('
EXTERNAL_BODY_PATTERN='\[verifier::external_body\]'
EXTERNAL_TYPE_PATTERN='\[verifier::external_type_specification\]'

echo "Running vcad-operators trust-surface scans..."

if rg -n "$TRUST_PATTERN" "$OPERATORS_SRC_DIR"; then
  echo "error: found forbidden trusted/interpreted-spec tokens in vcad-operators src"
  exit 1
fi

if rg -n "$EXTERNAL_BODY_PATTERN" "$OPERATORS_SRC_DIR"; then
  echo "error: found forbidden verifier external_body markers in vcad-operators src"
  exit 1
fi

if rg -n "$EXTERNAL_TYPE_PATTERN" "$OPERATORS_SRC_DIR"; then
  echo "error: found forbidden verifier external_type_specification markers in vcad-operators src"
  exit 1
fi

echo "trust-surface scan passed; no forbidden markers found in vcad-operators/src"
