#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOPOLOGY_SRC_DIR="$ROOT_DIR/crates/vcad-topology/src"
TRUST_PATTERN='assume_specification|external_fn_specification|\buninterpreted\b|admit\(|assume\('
EXTERNAL_BODY_PATTERN='\[verifier::external_body\]'
EXTERNAL_TYPE_PATTERN='\[verifier::external_type_specification\]'
EXPECTED_EXTERNAL_TYPE_FILE="$TOPOLOGY_SRC_DIR/runtime_halfedge_mesh_refinement.rs"
EXPECTED_EXTERNAL_TYPE_COUNT=6

echo "Running vcad-topology trust-surface scans..."

if rg -n "$TRUST_PATTERN" "$TOPOLOGY_SRC_DIR"; then
  echo "error: found forbidden trusted/interpreted-spec tokens in vcad-topology src"
  exit 1
fi

if rg -n "$EXTERNAL_BODY_PATTERN" "$TOPOLOGY_SRC_DIR"; then
  echo "error: found forbidden verifier external_body markers in vcad-topology src"
  exit 1
fi

external_type_files="$(
  rg -l "$EXTERNAL_TYPE_PATTERN" "$TOPOLOGY_SRC_DIR" 2>/dev/null || true
)"

if [[ -n "$external_type_files" ]]; then
  while IFS= read -r f; do
    [[ -z "$f" ]] && continue
    if [[ "$f" != "$EXPECTED_EXTERNAL_TYPE_FILE" ]]; then
      echo "error: external_type_specification found outside expected file:"
      printf '  %s\n' "$external_type_files"
      exit 1
    fi
  done <<< "$external_type_files"
fi

external_type_count="$(rg --no-filename -c "$EXTERNAL_TYPE_PATTERN" "$EXPECTED_EXTERNAL_TYPE_FILE" || true)"
external_type_count="${external_type_count:-0}"
if [[ "$external_type_count" -ne "$EXPECTED_EXTERNAL_TYPE_COUNT" ]]; then
  echo "error: expected $EXPECTED_EXTERNAL_TYPE_COUNT external_type_specification markers in $EXPECTED_EXTERNAL_TYPE_FILE, found $external_type_count"
  exit 1
fi

echo "trust-surface scan passed; external_type_specification markers are constrained to runtime_halfedge_mesh_refinement.rs (count=$external_type_count)"
