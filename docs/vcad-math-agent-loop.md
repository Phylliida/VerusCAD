# vcad-math Agent Loop

Requested workflow (2026-02-12):

1. Stay scoped to `vcad-math` only.
2. Before each pass, update `docs/vcad-math-todo.md` with anything still missing.
3. Execute unchecked TODO items in order.
4. After TODO is exhausted, run a "cheating" audit:
   - find lemmas whose proofs/contracts are weaker than claims,
   - strengthen/fix proofs and contracts.
5. Only report vcad-math complete when TODO + cheating audit are both complete and verified.

Operational rule:
- Every proof change must end with `./scripts/verify-vcad-math.sh` green.
