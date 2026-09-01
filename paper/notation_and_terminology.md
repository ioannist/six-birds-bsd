# Notation and Terminology — BSD Articles

Status: populated 2026-05-29. The shared foundations aliases and the
local (paper-specific) BSD reserved-symbol registry are filled (see
"Reserved symbols" below); macros mirror
`paper/<axis>/includes/paper_macros.tex` and `paper/notes/macro-audit.md`.

This is the **single source of truth** for paper-facing names. Every
symbol used in the paper must be either:

1. Inherited from a vendored Foundations layer (F1/F2/F3) — listed
   in the "Inherited" section below with its canonical name and the
   alias used in the paper; or
2. Introduced locally in this repo — declared in the "Local" section
   below with definition, role, and the Lean module it lives in.

No silent vocabulary. If a new term is added in the paper, it must
also be added here and in `Terminology.lean` in the same change.

## Governance

- `lean/SixBirdsBSD/Terminology.lean` declares the Lean side of the
  foundations alias surface.
- This file declares the paper side.
- Each paper `\input`s its own `paper/<axis>/includes/paper_macros.tex`
  (`<axis>` = `apparatus` or `closure`), which defines the LaTeX
  commands rendering the symbols.
- Reserved-symbol policy: every reserved symbol below carries the
  meaning declared here. Local proofs MUST NOT repurpose a reserved
  symbol for a different role.

## Inherited from Foundations (alias surface)

| Concept | Canonical decl (foundations) | Paper-side alias | Foundation layer |
| --- | --- | --- | --- |
| Closure operator | `ClosureOp` | `F1ClosureOp` | Foundations I |
| Closure ladder strict extension | `ClosureLadder` | `F1ClosureLadder` | Foundations I |
| Idempotent endomap | `ClosureLadder.IdempotentEndo` | `F1IdempotentEndo` | Foundations I |
| Quotient packaging | `ClosureLadder.MetaPackaging.pack` | `F1PackagingPack` | Foundations I |
| Primitive roles (P1–P6) | `SixBirds.Role` | `F2Role` | Foundations II |
| FATCD host | `SixBirds.FATCD` | `F2FATCD` | Foundations II |
| Channel status | `SixBirds.ChannelStatus` | `F2ChannelStatus` | Foundations II |
| Scoped exact six | `SixBirds.scoped_exact_six` | `F2ScopedExactSix` | Foundations II |
| Typed non-collapse | `SixBirds.typed_non_collapse` | `F2TypedNonCollapse` | Foundations II |
| BirdInt audited finite calculus | `SixBirdsIII.BirdIntDomain` | `F3BirdIntDomain` | Foundations III |
| Primitive labels | `SixBirdsIII.Primitive` | `F3Primitive` | Foundations III |
| Promotion status family | `SixBirdsIII.PromotionStatus` | `F3PromotionStatus` | Foundations III |
| Claim status family | `SixBirdsIII.ClaimStatus` | `F3ClaimStatus` | Foundations III |
| Gate status family | `SixBirdsIII.GateStatus` | `F3GateStatus` | Foundations III |
| Strict gate status family | `SixBirdsIII.StrictGateStatus` | `F3StrictGateStatus` | Foundations III |
| Square status family | `SixBirdsIII.SqStatus` | `F3SqStatus` | Foundations III |
| Promotion bridge record | `SixBirdsIII.PromotionBridgeRecord` | `F3PromotionBridgeRecord` | Foundations III |
| Claim record | `SixBirdsIII.ClaimRecord` | `F3ClaimRecord` | Foundations III |
| Defect record | `SixBirdsIII.DefectRecord` | `F3DefectRecord` | Foundations III |
| Directed cell record | `SixBirdsIII.DirectedCellRecord` | `F3DirectedCellRecord` | Foundations III |
| Top-down channel record | `SixBirdsIII.TopDownChannelRecord` | `F3TopDownChannelRecord` | Foundations III |
| Visibility tag | `SixBirdsIII.VisibilityTag` | `F3VisibilityTag` | Foundations III |
| Threshold tag | `SixBirdsIII.ThresholdTag` | `F3ThresholdTag` | Foundations III |
| Level trichotomy | `SixBirdsIII.Level` | `F3Level` | Foundations III |
| Host taxonomy | `SixBirdsIII.Host` | `F3Host` | Foundations III |

Paper-side body prose typically refers to these concepts by plain
mathematical description and only invokes the alias when the discussion
is at the foundations-vocabulary level (typically in App D or the
introduction).

## Local to the BSD papers (apparatus + closure axes)

### Reserved symbols

Populated 2026-05-29. Each entry records: symbol, meaning, LaTeX macro
(defined in `paper/<axis>/includes/paper_macros.tex`; see
`paper/notes/macro-audit.md`), and the Lean module under
`SixBirdsBSD.Apparatus.*` / `SixBirdsBSD.Closure.*` that hosts it. Body
prose uses the symbol; the Lean module appears only in App~D / footnotes
(companion form, `paper/notes/proof-presentation-policy.md`).

**Shared (classical BSD quantities).**

| Symbol | Meaning | LaTeX macro | Lean module |
| --- | --- | --- | --- |
| Ш | Tate–Shafarevich group | `\Sha` | (classical; used in both axes) |
| Reg | regulator | `\Reg` | (classical) |
| ∏ c_v | Tamagawa product | `\Tam` | (classical) |
| E(ℚ)_tors | torsion | `\tors` | (classical) |
| κ_r | cascade/Strong-BSD normalization constant | `\kapr` | `SixBirdsBSD.Apparatus.KappaNormalization` |

**Apparatus axis.**

| Symbol | Meaning | LaTeX macro | Lean module |
| --- | --- | --- | --- |
| Ξ_C(D∣L) | adequacy / Schur-complement residual | `\XiC` | `SixBirdsBSD.Apparatus.Decomposition` |
| K_{DD}, K_{DL}, K_{LL} | Gram blocks | `\KDD` `\KDL` `\KLL` | `SixBirdsBSD.Apparatus.Decomposition` |
| K_{LL}^† | pseudo-inverse block | `\Kdagger` | `SixBirdsBSD.Apparatus.Decomposition` |
| M_C^φ | typed column | `\MCphi` | `SixBirdsBSD.Apparatus.Decomposition` |
| vsrc; J_1, J_2, J_{12} | rank-2 exterior-algebra calibrator | `\vsrc` `\Jone` `\Jtwo` `\Jtwelve` | `SixBirdsBSD.Apparatus.Vsrc` |
| A_E | analytic leading coefficient $L^{(r_{\mathrm{an}})}(E,1)/r_{\mathrm{an}}!$ | (raw `A_E`; no macro) | `SixBirdsBSD.Apparatus.AnalyticPeriod` |

> **Per-axis `A_E` (collision resolved).** In the **apparatus** paper `A_E` is the
> analytic leading coefficient $L^{(r_{\mathrm{an}})}(E,1)/r_{\mathrm{an}}!$ (defined on
> first use in `sec:introduction` / `sec:analytic-period`). In the **closure** paper the
> Selmer-complex pairing substrate is written `\mathcal{A}_E` (macro `\AofE`), a distinct
> calligraphic symbol, so the two documents do not reuse `A_E` for different objects.
> The closure's imports section states the contrast explicitly on first use.

**Closure axis.**

| Symbol | Meaning | LaTeX macro | Lean module |
| --- | --- | --- | --- |
| Sel!_BSD | saturated BSD trace shell | `\SelBSD` | `SixBirdsBSD.Closure.SelShell` |
| ρ_E | shell residual | `\rhoE` | `SixBirdsBSD.Closure.SelShell` |
| Π_BSD | recognition predicate | `\PiBSD` | `SixBirdsBSD.Closure.SelShell` |
| Γ_BSD^{padic-descent}, ^{Sha-persistence}, ^{higher-GZ-fixity} | the three recognition sources | `\GammaPD` `\GammaSP` `\GammaGZ` | `SixBirdsBSD.Closure.RecognitionSources` |
| χ_{CT,p} | Cassels–Tate comparison | `\chiCTp` | `SixBirdsBSD.Closure.ChiCTp` |
| 𝒜_E | Selmer-complex pairing substrate | `\AofE` (renders `\mathcal{A}_E`) | `SixBirdsBSD.Closure.Imports` |
| η_p | OC eta | `\etap` | `SixBirdsBSD.Closure.EtaFormula` |
| RefStable AOR | AOR membership predicate | `\RefStable` | `SixBirdsBSD.Closure.AORInstance` |
