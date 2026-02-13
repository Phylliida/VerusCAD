# Crates
Planned crate split for a layered verified CAD kernel.

1. `vcad-math`: exact arithmetic, points/vectors, fundamental predicates.
2. `vcad-geometry`: geometric predicate layer (orientation/sidedness/intersection/containment) reusing `vcad-math`.
3. `vcad-sketch`: 2D sketch entities and geometric checks.
4. `vcad-topology`: topological structures and incidence invariants.
5. `vcad-kernel`: modeling operations built on lower verified layers.
6. `vcad-cli`: small executable for examples and local experiments.

Dependency direction should remain one-way:
`vcad-math -> vcad-geometry -> vcad-sketch -> vcad-topology -> vcad-kernel -> vcad-cli`.
