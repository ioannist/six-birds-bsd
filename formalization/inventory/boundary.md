# Formalization Boundary

This inventory defines the source contract for the BSD Lean 4
mechanization. The authoritative target corpus is the set of
theorem-like environments in:

- `paper/apparatus/sections/*.tex` (apparatus axis, Paper A) and
  `paper/closure/sections/*.tex` (closure axis, Paper B); targets are also
  recorded in the consolidated mathematical source records
  `anti_loc/extracted_math/apparatus_master.md` and
  `anti_loc/extracted_math/closure_master.md` respectively

There are no external dependency papers in this repository.
Foundations I/II/III declarations are not source items; they are tracked
separately via `imported_foundations.yml` and the vendored trees under
`vendor/foundations/`.

Recognition sources are handled two ways, depending on axis:

- **`out_of_scope_recognition_source`** (e.g. the apparatus axis's five
  `obl:apparatus:rho-*` per-column transports): recorded in the paper
  inventory with that `intended_status`; they **do not appear in Lean**.
- **`mechanize_now` recognition carriers** (the closure axis's three
  `Γ_BSD^*` sources, `def:closure:gamma-*`): these **do appear in Lean**
  as typed `structure` carriers (`recognition_source` lean_coverage),
  whose arithmetic `Prop` content is a carried hypothesis, never an
  axiom. "Recognition source" therefore does not imply "absent from
  Lean"; only the `out_of_scope_recognition_source` items are absent.
