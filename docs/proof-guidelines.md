# Proof Guidelines
Conventions for writing VerusCAD code and proofs.

## Core rules
1. Every non-trivial exec function should have a corresponding spec-level statement.
2. Preconditions (`requires`) should express mathematical domain constraints clearly.
3. Postconditions (`ensures`) should connect runtime output to spec meaning.
4. Keep lemmas small and composable; avoid one giant proof.

## Modeling style
1. Encode structural invariants in constructors and validation functions.
2. Prefer total functions. If partial behavior is necessary, use explicit preconditions.
3. Separate data definition files from lemma files when proofs become dense.

## Performance and trust
1. Keep the trusted computing base narrow: verified core in library crates, thin wrappers elsewhere.
2. Avoid introducing floating point in verified kernel code until exact arithmetic path is stable.
3. Add proof regression tests when fixing bugs to prevent proof drift.

## Naming suggestions
1. `spec_*` for spec helpers.
2. `lemma_*` for proof lemmas.
3. `proof_*` for larger proof routines.
4. `is_valid_*` for runtime validity predicates tied to explicit invariants.
