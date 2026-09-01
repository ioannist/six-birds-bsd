# Scope fence (both papers)

*Phase 6 deliverable. Closed 2026-05-29. The required nonclaims + the
mandated wording for each. Every drafting dispatch that touches a fenced
topic uses the wording here.*

## Paper B (closure) nonclaims (from proposal §10; mechanization-confirmed)

- **NC-1 — Not unconditional BSD.** Required wording: "This is **not** an
  unconditional classical proof of BSD (scalar or strong). The result is
  theorem-grade *within the Six Birds closure discipline*, conditional on
  the named recognition sources and imported theorem stacks. Outside the
  framework it reads as the conditional theorem
  `(Γ_BSD^{padic-descent} ∧ Γ_BSD^{Sha-persistence} ∧
  Γ_BSD^{higher-GZ-fixity} ∧ χ_{CT,p}-imports ∧ A_E-imports ∧
  Beilinson-imports) ⟹ Strong BSD`."
- **NC-2 — Recognition sources not derived.** "No recognition source is
  derived from framework primitives. Each `Γ_BSD^*` is closure content of
  the formed BSD layer, encoded in Lean as a typed structure carrier —
  **not a Lean axiom** (the forbidden-tokens rule bans `axiom`/`opaque`/
  `constant`/`sorry`/`admit`)."
- **NC-3 — Rank-≥2 GZ open.** "We do **not** prove the rank-≥2 generalized
  Gross–Zagier identity (`T_E12_REFINED`); it is stated as an
  audit-result typed no-go, genuinely open in the audited literature."
- **NC-4 — Additive `p≤3` IMC open.** "We do **not** prove the additive
  `p≤3` Iwasawa main conjecture (`T_BAD_REFINED`); audit-result no-go."
- **NC-5 — Imports not eliminated.** "The `χ_{CT,p}` comparison remains
  conditional on its imported stack (T_E1–T_E8); the import structures
  are sourced assumptions, not results of this paper."
- **NC-6 — Anchor-level evidence is not family-level.** "The OC `η`-formula
  sub-residual is verified at anchors (49a1@7, 36a1@3, 121b1@11), not as a
  uniform family-level statement."
- **NC-7 — AOR non-eliminative.** "The AOR-instance reading is
  non-eliminative: it reclassifies the closure records (recognition
  discharges are `bridged`, never `zero`), it does **not** discharge the
  open obligations. Only the local syntactic `RefStableAOR` predicate is
  mechanized, not the full TsiokosAOR2026 meta-theory."

## Paper A (apparatus) nonclaims

- **A-NC-1 — No-gos are audit results, not non-existence claims.** "The
  no-go suite (NG-1…NG-5, higher-rank, global, support-prime) records
  where theorem-grade Mode-A literature does **not** reach; it is **not**
  a claim that the missing identities cannot exist."
- **A-NC-2 — Finite typed level.** "Adequacy collapses are proved at the
  finite, mathlib-free, typed level (identity-matrix action; ℚ rank-1
  projector traces); operator/motivic full generality is not claimed."
- **A-NC-3 — `vsrc` structural narrowing.** "The `vsrc` exterior-product
  relations are represented structurally on the `2^r` coordinate space
  (`narrowed_surrogate`); the dimension/calibration content is faithful,
  full axiomatization is not claimed."
- **A-NC-4 — Recognition-source transports are carriers.** "The five
  `obl:apparatus:*` per-column transports are recognition sources
  (carriers), not derived theorems."

## Wording discipline

- Never say "we prove BSD" / "we prove the IMC" / "we prove
  Gross–Zagier." Use "we land Strong BSD as a conditional closure" /
  "audit-result no-go."
- Always pair the headline with its conditional reading on first
  statement and in the scope section.
- The recognition sources and imports are "supplied" / "imported" /
  "carried as hypotheses," never "established."
