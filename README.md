# Six Birds BSD

This repository contains the public support surface for two papers in the
Six Birds series: modular LaTeX sources, tracked flattened manuscripts,
Lean 4 mechanization, inventories, manifests, validators, and vendored
Foundations dependencies.

## Papers

- **Decomposing the Bloch--Kato Fundamental Line: Adequacy and No-Go
  Results for the BSD Invariants**:
  DOI: [10.5281/zenodo.20713981](https://doi.org/10.5281/zenodo.20713981)
- **A Conditional Proof of the Strong Birch--Swinnerton-Dyer
  Conjecture**:
  DOI: [10.5281/zenodo.20713968](https://doi.org/10.5281/zenodo.20713968)

The first paper develops a typed five-column decomposition of the
Bloch--Kato fundamental line, adequacy diagnostics, and a suite of
information-loss no-go results. The second builds a conditional Strong-BSD
closure from explicit recognition sources and imported arithmetic theorem
stacks. It is a conditional result and does not claim an unconditional proof
of BSD.

## What This Repository Provides

- Modular LaTeX sources under `paper/apparatus/` and `paper/closure/`.
- Tracked flattened manuscript sources at the repository root.
- Lean 4 mechanization under `lean/`, split into apparatus and closure axes.
- Paper inventories, traceability queues, and validation manifests under
  `formalization/` and `lean/manifests/`.
- Deterministic validation and build-support scripts under `scripts/`.
- Vendored Six Birds Foundations dependencies under `vendor/foundations/`.
- Consolidated mathematical source records under `anti_loc/extracted_math/`.

The formal corpus covers 51 of the papers' 69 labeled statements: 30 on the
apparatus axis and 21 on the closure axis. Deep arithmetic inputs are carried
as explicit proof-bearing hypotheses or recognition-source records, not as
project-local axioms.

## Build and Validate

Build both PDFs:

```bash
make paper-build
```

Run the complete paper preflight and static registry checks:

```bash
make paper-preflight
```

Run the static validator suite and its tests:

```bash
make validate
make test
```

Check that the tracked snapshot contains no local credentials, agent/session
state, private runbooks, or machine-specific paths:

```bash
make public-audit
```

Build the Lean project and run the live axiom-closure probe:

```bash
make verify-lean
```

The paper PDFs are emitted as `paper/apparatus/build/main.pdf` and
`paper/closure/build/main.pdf`. Each LaTeX build also generates a flattened
source as `build/main_flat.tex`; release copies of those flattened sources are
tracked at the repository root.

## Repository Layout

- `paper/apparatus/` and `paper/closure/` - modular manuscript sources.
- Repository-root `Tsiokos_2026_*.tex` files - flattened manuscript sources.
- `paper/notes/` - cross-paper terminology, scope, claim, and release records.
- `lean/` - the pinned Lean 4 project and validation manifests.
- `formalization/` - inventories, boundaries, and traceability records.
- `scripts/` - deterministic validators and release-support utilities.
- `vendor/foundations/` - vendored upstream Foundations dependencies.
- `anti_loc/extracted_math/` - consolidated mathematical source records used
  by the formalization inventories.

## Notes

- The LaTeX toolchain requires `latexmk`, `latexpand`, and a TeX distribution
  containing the packages used by the manuscripts.
- The Lean toolchain is pinned in `lean/lean-toolchain`.
- Third-party vendored code remains under its upstream license terms.
