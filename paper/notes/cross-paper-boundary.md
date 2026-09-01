# Cross-paper boundary (apparatus ↔ closure)

*Phase 0 deliverable. Closed 2026-05-29.*

The dependency is **one-way: the closure article depends on the
apparatus article**.  The apparatus article is self-contained and drafts
first; the closure article consumes its normalization and adequacy
framing through standard bibliographic citation.

## What the apparatus article supplies

| Forwarded item | Apparatus locus | How the closure article uses it |
|---|---|---|
| `κ_r` normalization equivalence | `thm:apparatus:kappa-r-normalization-equivalence` (`KappaNormalization.kappaRNormalizationEquivalence`) | Reused **in Lean** by `Closure.AORInstance.aorMechanicalRecords` (imported, not redefined) and cited in body prose for the cascade-form ↔ standard-BSD-form equivalence. |
| Adequacy-residual framing (`Ξ_C`, five columns) | `Decomposition`, `HeightRegulator`, … | The closure article's `Sel!_BSD` residual `ρ_E` and master-theorem applicability narrative rest on the apparatus diagnostic layer; cited as `\citet{TsiokosBSDApparatus2026}`. |
| The higher-rank generalized-Gross–Zagier no-go | `thm:apparatus:*` higher-rank no-go suite | The closure article's `Γ_BSD^{higher-GZ-fixity}` recognition source is precisely what discharges (as recognition content) the rank-≥2 gap marked by the apparatus no-go. |

## What the closure article imports

- The `κ_r` normalization (Lean import + verbatim citation where
  invoked).
- The adequacy / five-column framing (standard citation
  `\citet{TsiokosBSDApparatus2026}`).

The closure article reproduces the `κ_r` equivalence statement (or names
it precisely) where invoked in `sec:aor-instance`, with citation to
`\citet{TsiokosBSDApparatus2026}`; it does **not** silently paraphrase.
No `\Cref` to internal labels of the cited article: those labels are not
visible in the closure article's `\Cref` namespace.

## Sanctioned forward references in the apparatus article

The apparatus article is otherwise self-contained. Exactly **two**
forward-reference paragraphs are allowed, both using the standard
bibliographic citation `\citet{TsiokosBSDClosure2026}`:

1. In the `κ_r`-normalization section (`sec:kappa-normalization`): name
   the cited closure article as the conditional Strong-BSD closure that
   consumes this normalization.
2. In the higher-rank no-go section (`sec:higher-rank-no-go`): name the
   cited closure article as where the rank-≥2 generalized-Gross–Zagier
   gap is handled as a recognition source rather than a closed theorem.

No `\Cref` to internal closure-article labels from the apparatus article.

## Logical order

The apparatus article precedes the closure article logically because the
closure prose reuses and cites the apparatus `κ_r` normalization and adequacy
framing.
