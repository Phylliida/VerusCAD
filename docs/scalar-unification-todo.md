# Scalar Unification TODO (`vcad-math`)

Goal:
- keep `vcad-math` focused on one proof/spec scalar model for now,
- add a practical runtime scalar backend via `rug::Rational`,
- keep proof model semantics explicit via `ScalarModel`.

## Closure Checklist
- [x] Add explicit proof-model naming (`ScalarModel`) so future runtime refinement can target a stable model name.
- [x] Export `ScalarModel` from the crate root.
- [x] Remove old `exec_scalar` runtime bridge module from crate surface and source tree.
- [x] Replace `ScalarKey` helper with `RuntimeScalar` backed by `rug::Rational`.
- [x] Update docs to reflect the `rug` runtime backend decision.
- [x] Verify crate after cleanup.

## Status
This TODO is complete for the current decision (`ScalarModel` proof type + `RuntimeScalar` exec type backed by `rug`).

Follow-up completed:
- [x] Added `RuntimeScalar` refinement bridge (`src/runtime_scalar_refinement.rs`) with Verus `view` and operation-level contracts for:
  - `from_int`
  - `from_fraction`
  - `add`
  - `sub`
  - `mul`
  - `neg`
  - `normalize`
