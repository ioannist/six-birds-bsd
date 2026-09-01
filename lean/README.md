# BSD — Lean Project

This directory holds the Lean 4 mechanization for the six-birds-bsd
project. Two paper axes are tracked: the apparatus axis (Paper A) under
`SixBirdsBSD/Apparatus/` and the closure axis (Paper B, flagship) under
`SixBirdsBSD/Closure/` (the latter including `AORPrimitives.lean` and
`AORInstance.lean` for the "BSD as an AOR instance" landing). The
alignment trio (`ImportedFoundations`, `FoundationsICompat`,
`Terminology`) sits at the top of the namespace and pulls in the
vendored Foundations I/II/III.

## Toolchain

Pinned to `leanprover/lean4:v4.28.0` in `lean-toolchain`. Matches the
three vendored foundations under `../vendor/foundations/`. No version
drift across the project.

## No mathlib

This Lean project is deliberately mathlib-free, matching the
foundations and the sibling projects in the series. Any
finite-dimensional linear algebra used by the apparatus is defined
locally as mechanization proceeds; deep arithmetic (elliptic-curve /
L-function / Selmer / Iwasawa content) enters the closure axis only as
imported proof-carrying structures and typed recognition-source
carriers, never as mechanized analysis.
See `../paper/notation_and_terminology.md` for the governance contract.

## Build

```bash
cd lean
lake build
```

This builds the umbrella `SixBirdsBSD`, which transitively builds the
alignment trio and the two axis umbrellas (`SixBirdsBSD/Apparatus.lean`,
`SixBirdsBSD/Closure.lean`) together with their per-section modules.

## Full check

From the repo root:

```bash
python scripts/check_lean.py
```

Runs the structural prechecks (required files, forbidden tokens,
external-ref grep), the Phase A python validator chain, and
`lake build`. Use `--skip-build` if the Lean toolchain is not
available, or `--skip-prechecks` to run only the lake build.

## Forbidden Lean tokens

The validator rejects any occurrence of `sorry`, `admit`, `axiom`,
`opaque`, or `constant` in `SixBirdsBSD/*`. Out-of-scope obligations
(e.g. structural recognition sources that are not Lean-derivable) live
in the paper inventory under `../formalization/inventory/` with
`intended_status = out_of_scope_*`; they do not appear in Lean as
axioms.

## Pointers

- Cross-walk to canonical Foundations names:
  `../formalization/inventory/imported_foundations.yml`
- Generated drift canary:
  `SixBirdsBSD/ImportedFoundations.lean`
  (regenerate with `scripts/generate_imported_foundations.py`)
- Notation/terminology governance: `../paper/notation_and_terminology.md`
- Mechanization queues:
  `../formalization/traceability/queue_{apparatus,closure}.csv`
