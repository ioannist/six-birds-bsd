# BSD Formalization Architecture and Status

This document records the completed Lean 4 formalization supporting the two
BSD papers in this repository:

1. the typed Bloch--Kato decomposition and adequacy apparatus; and
2. the conditional Strong-BSD closure and its non-eliminative AOR instance.

It is a technical scope and reproducibility record, not a claim that the deep
arithmetic of BSD has been formalized.

## Formalization boundary

The Lean development mechanizes the framework-structural content:

- the five-column typed atlas and its component maps;
- Schur-collapse adequacy statements;
- the information-loss no-go suite;
- the virtual-source calibration and normalization bridge;
- proof-carrying import structures;
- typed recognition-source carriers;
- the saturated BSD trace shell and readout algebra; and
- the conditional landing and local AOR-instance bookkeeping.

It does not mechanize elliptic-curve arithmetic, analytic continuation,
Selmer theory, Iwasawa theory, the rank-at-least-two Gross--Zagier input, or an
unconditional proof of BSD. Those inputs are represented as explicit
hypothesis fields or recognition-source records. They are never introduced as
project-local Lean axioms.

The project is deliberately mathlib-free and uses only the pinned Lean
toolchain plus the vendored Six Birds Foundations sources.

## Source-of-truth chain

The maintained dependency chain is:

```text
consolidated mathematical source records
  -> modular LaTeX statements of record
  -> formalization inventories and queues
  -> Lean manifests and declarations
  -> paper disclosure appendices
```

The consolidated records are:

- `anti_loc/extracted_math/apparatus_master.md`
- `anti_loc/extracted_math/closure_master.md`

The binding public registry is
`paper/notes/statements-of-record.yml`. Per-axis inventories live under
`formalization/inventory/`, and Lean declaration manifests live under
`lean/manifests/`.

## Trust model

The validator rejects active Lean uses of `sorry`, `admit`, `axiom`, `opaque`,
or `constant`. Imported arithmetic appears in proof-carrying structures whose
fields are hypotheses. Recognition sources are likewise explicit typed data.

The accepted dependency closure is recorded in
`lean/manifests/trust_base.txt` and checked both statically and through the
live Lean axiom probe.

## Coverage

The papers contain 69 labeled statements of record:

- apparatus: 41 total, 30 mechanized;
- closure: 28 total, 21 mechanized; and
- combined: 51 mechanized, 18 intentionally outside the Lean theorem corpus.

The remaining statements are classified as sourced arithmetic obligations,
recognition content, support-only audit statements, remarks, or nonclaims.

## Validation

From the repository root:

```bash
make validate
make test
make verify-lean
make paper-preflight
```

These commands check registry consistency, manifest coverage, Foundations
provenance, semantic alignment, validator tests, the Lean build and axiom
closure, and both manuscript builds.

## Completion status

The two-axis formalization, disclosure appendices, manuscript integration,
and validation infrastructure are complete. The current release sources are
the modular manuscripts under `paper/` and the flattened TeX files at the
repository root.
