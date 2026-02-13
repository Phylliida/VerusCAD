# vcad-geometry
Verified geometric predicate layer built on `vcad-math`.

Current scope (initial scaffold):
1. Orientation predicate wrappers over runtime `vcad-math` APIs.
2. Plane sidedness and segment/plane strict-crossing helpers.
3. Collinearity/coplanarity runtime wrappers.
4. Point-in-convex-polygon (2D) runtime predicate.
5. Verus refinement modules connecting runtime wrappers to `vcad-math` specs:
   - `runtime_orientation_predicates_refinement`
   - `runtime_sidedness_refinement`
   - `runtime_collinearity_coplanarity_refinement`

Design rule:
1. Reuse `vcad-math` theorem/model surface wherever possible.
2. Do not duplicate determinant/vector algebra proofs in this crate.

Planning document:
1. `docs/phase3-predicates.md`
