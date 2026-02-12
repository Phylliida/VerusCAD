# Crates
Planned crate split for a layered verified CAD kernel.

1. `vcad-math`: exact arithmetic, points/vectors, fundamental predicates.
2. `vcad-sketch`: 2D sketch entities and geometric checks.
3. `vcad-topology`: topological structures and incidence invariants.
4. `vcad-kernel`: modeling operations built on lower verified layers.
5. `vcad-cli`: small executable for examples and local experiments.

Dependency direction should remain one-way:
`vcad-math -> vcad-sketch -> vcad-topology -> vcad-kernel -> vcad-cli`.
