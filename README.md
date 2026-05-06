# LeanC2

Lean 4 + Mathlib formalization of the C2 framework, focused on the off-axis
chain, the continuation interface, numerical-certificate hooks, and the public
endpoints connected to the C2 -> RH package.

## Build

```bash
lake exe cache get
lake build
```

## Quick Structure

- `LeanC2/` contains the main formalization graph.
- `LeanC2/PublicAPI.lean` exposes the public surface of the project.
- `LeanC2/Numerical/Generated/` contains Lean artifacts generated from the
  external certificates used by the canonical verification flow.

## References

- Architecture: `c2_lean_architecture.md`
- Legacy reuse map: `legacy_reuse_map.md`
- Preserved legacy code: `Antigo_Lean_C2/`

## Citation

Citation and release metadata are provided in `CITATION.cff`, `.zenodo.json`,
and `ZENODO_RELEASE_2026-05-06.1.md`.

