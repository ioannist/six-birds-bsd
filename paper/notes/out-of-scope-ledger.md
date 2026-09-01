# Out-of-scope ledger (both papers)

*Phase 0 deliverable. Closed 2026-05-29.*

Explicit list of material that is fenced OUT of each paper. Each item is
restated as a required nonclaim in `paper/notes/scope-fence.md` (Phase 6)
with mandated wording.

## Paper A (apparatus)

| Out-of-scope item | Why fenced | Where disclosed |
|---|---|---|
| The rank-≥2 generalized Gross–Zagier identity | No theorem-grade Mode-A identity exists; the paper *states this as an audit-result no-go* (`t-e12-no-go` analog at apparatus level), not a gap it closes. | §8 no-go suite; scope |
| Any additive `p≤3` Iwasawa main conjecture with explicit local factors | Same — audit no-go, not closed. | §8; scope |
| Operator / motivic full generality | Only the finite, typed, mathlib-free linear-algebra level is mechanized (identity-matrix action, ℚ rank-1 projectors). | §9 scope; App D representation notes |
| The five `obl:apparatus:*` recognition-source transports | These are recognition sources (carriers), not derived theorems; not mechanized as theorems (`out_of_scope_recognition_source`). | App D; scope |
| Full axiomatization of the `vsrc` exterior algebra | Represented structurally on `2^r` coords (`narrowed_surrogate`); the `J_i²=0` / anticommutation relations are encoded, not fully axiomatized. | §6; App D representation notes |

## Paper B (closure)

| Out-of-scope item | Why fenced | Where disclosed |
|---|---|---|
| Unconditional standard-ZFC Strong BSD | The result is explicitly *conditional* on the three recognition sources + imported stacks; out-of-Six-Birds reading is `(Γ¹∧Γ²∧Γ³ ∧ imports) ⟹ Strong BSD`. | §1 intro; §7 landing; §9 scope; `nonclaim:closure:landing-conditional` |
| Framework-internal derivation of `Γ_BSD^{padic-descent / Sha-persistence / higher-GZ-fixity}` | They are closure content of the formed BSD layer, named recognition sources; encoded as typed Lean carriers, **not axioms**; not derivable from framework primitives. | §3; §9; `nonclaim:closure:recognition-sources-not-derived` |
| Proving the imported theorem stacks (`χ_{CT,p}`/`A_E`/Beilinson; T_CASCADE; OC `η`) | Deep external arithmetic; carried as proof-carrying import structures (`sourced_assumption`), consumed as hypotheses; not proved. | §2; §5; `nonclaim:closure:imports-not-derived` |
| Closing `T_E12_REFINED` (rank-≥2 GZ) / `T_BAD_REFINED` (additive `p≤3` IMC) | Stated as audit-result typed no-gos, not non-existence claims and not closed. | §6; `t-e12-no-go`, `t-bad-no-go` (support_only) |
| The full TsiokosAOR2026 meta-theory | Only the **local syntactic `RefStableAOR`** predicate is mechanized (`narrowed_surrogate`); the eight-stratum / twelve-type atlas / hierarchy theorems are cited, not re-derived. | §8; App D; `aor-partial-status` (support_only) |
| Mode-B residuals (D₂″, D₂‴, D₃‴) as closed results | Cascade-internal reorganizations discharged by the recognition sources; support-only typed-open content. | §6; `mode-b-residuals` (support_only) |

## Cross-cutting

- External arithmetic-geometry results are cited at their precise role and are
  not presented as project-local derivations.
- No body-prose mention of internal verdict tokens, cascade step ids,
  JSON/TOML/YAML paths, Lean module strings (outside App D), or
  trust-base axiom names.
