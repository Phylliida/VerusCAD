#!/usr/bin/env bash
# shellcheck shell=bash

# Shared script prelude for Rust/Verus commands:
# - strips leaked ghost cfg flags that break stable cargo flows
# - repairs TMPDIR if it points to a missing/unwritable path

if [[ "${RUSTFLAGS:-}" == *"verus_keep_ghost"* || "${CARGO_ENCODED_RUSTFLAGS:-}" == *"verus_keep_ghost"* ]]; then
  echo "note: clearing verus_keep_ghost Rust flags for script-managed Rust flow"
fi
unset RUSTFLAGS
unset CARGO_ENCODED_RUSTFLAGS

if [[ -z "${TMPDIR:-}" || ! -d "${TMPDIR:-/nonexistent}" || ! -w "${TMPDIR:-/nonexistent}" ]]; then
  export TMPDIR="/tmp"
fi
