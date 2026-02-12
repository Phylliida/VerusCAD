# vcad-math Backup Snapshot (2026-02-12)

This snapshot was created before continuing rational migration proof refactors.

Contents:
- `current-in-progress/src/`: current working tree files during rational migration.
- `pre-rational-head/src/`: last committed (`HEAD`) files with the full integer-backed proof set.

Captured files:
- `src/lib.rs`
- `src/scalar.rs`
- `src/vec2.rs`
- `src/point2.rs`
- `src/orientation.rs`

Intent:
- Preserve both migration branches so we can restore/compare while rebuilding lemmas.
