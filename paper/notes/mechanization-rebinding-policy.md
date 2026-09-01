# Mechanization rebinding policy (both papers)

*Phase 7 deliverable. Closed 2026-05-29; reauthored 2026-05-29 to the
companion form. Maps each manifest tuple `(paper_label, lean_decl,
status)` to its disclosure mode, keyed to `statements-of-record.yml`. Per
the companion form (`proof-presentation-policy.md`), the disclosure mode
fixes (a) the **one-footnote** wording after the theorem/def in the body
and (b) the App~D table row; it does **not** put any of this in body
prose. This table is the App~D source-of-truth and the per-label
assignment the drafting dispatches consult.*

## Representation-disclosure notes (these live in App~D, not body prose)

- **Identity-matrix action** (apparatus Schur collapses): the collapse
  `Ξ_C = 0` is the proven identity-matrix action of the admitted native
  family (`sumFinKronecker`, `mulVec I = id`), not a projection set equal
  to `K_DD`.
- **ℚ rank-1 projector traces** (apparatus residual figures): residual
  trace/rank figures are derived from explicit `Rat` rank-1 projectors
  (`traceRat`), not asserted as literals.
- **`vsrc` structural encoding** (`narrowed_surrogate`): rank-2 exterior
  algebra on the `2^r` coordinate space; relations encoded, dimension
  faithful, full axiomatization not claimed.
- **Import structures** (`typed_structure_carrier`): proof-carrying
  structures bundling external theorems as `Prop` fields + their
  consequence; consumed as hypotheses; never axioms.
- **Recognition carriers** (`recognition_source` / `narrowed_surrogate`):
  typed carriers whose arithmetic `Prop` content is a hypothesis; index
  fields tied to the shell (`g.p`, `g.E`, `g.L`, rank).
- **Projection-packaged conditionals**: `chi/eta/t-cascade/landing/composite`
  project their conclusion from explicit proof-carrying records; the
  landing routes the readout through the framework master theorem
  (`gzFixityForcesResidualZero`).
- **Cross-paper `κ_r` reuse**: `aorMechanicalRecords` imports Paper A's
  `kappaRNormalizationEquivalence` (cited, not redefined).
- **Local `RefStableAOR`** (`aor-instance`, `narrowed_surrogate`): local
  syntactic predicate (`zero` = non-closed status; bridged discharges),
  not the full TsiokosAOR2026 meta-theory.

## Per-label disclosure assignment

| paper_label | lean_coverage | alignment | disclosure mode | lean_decl |
|---|---|---|---|---|
| **apparatus** | | | | |
| `def:apparatus:bk-component-map` | definition | faithful | lean_substantive | `SixBirdsBSD.Apparatus.Decomposition.bkComponentMap` |
| `def:apparatus:bridge-defect-equation` | definition | faithful | lean_substantive | `SixBirdsBSD.Apparatus.Decomposition.bridgeDefectEquation` |
| `thm:apparatus:component-killing` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.Decomposition.componentKilling` |
| `thm:apparatus:finite-scalar-public-shadow` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.Decomposition.finiteScalarPublicShadow` |
| `nonclaim:apparatus:decomposition-scope` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `def:apparatus:height-regulator-map` | definition | faithful | lean_substantive | `SixBirdsBSD.Apparatus.HeightRegulator.heightRegulatorMap` |
| `thm:apparatus:height-schur-collapse` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.HeightRegulator.heightSchurCollapse` |
| `obl:apparatus:rho-ht-reg-transport` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `warn:apparatus:571a1-carrier` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `def:apparatus:analytic-period-map` | definition | faithful | lean_substantive | `SixBirdsBSD.Apparatus.AnalyticPeriod.analyticPeriodMap` |
| `thm:apparatus:analytic-period-schur-collapse` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.AnalyticPeriod.analyticPeriodSchurCollapse` |
| `obl:apparatus:rho-an-period-transport` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `def:apparatus:finite-source-map` | definition | faithful | lean_substantive | `SixBirdsBSD.Apparatus.FiniteSource.finiteSourceMap` |
| `thm:apparatus:finite-source-schur-collapse` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.FiniteSource.finiteSourceSchurCollapse` |
| `thm:apparatus:scalar-finite-shadow` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.FiniteSource.scalarFiniteShadow` |
| `thm:apparatus:dim-sha-shadow` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.FiniteSource.dimShaShadow` |
| `obl:apparatus:rho-finite-transport` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `def:apparatus:p-adic-map` | definition | faithful | lean_substantive | `SixBirdsBSD.Apparatus.PAdic.pAdicMap` |
| `thm:apparatus:ordinary-schur-collapse` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.PAdic.ordinarySchurCollapse` |
| `thm:apparatus:signed-schur-collapse` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.PAdic.signedSchurCollapse` |
| `obl:apparatus:rho-p-transport` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `def:apparatus:det-assembly-map` | definition | faithful | lean_substantive | `SixBirdsBSD.Apparatus.DetAssembly.detAssemblyMap` |
| `thm:apparatus:cascade-completion-signature` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.DetAssembly.cascadeCompletionSignature` |
| `obl:apparatus:rho-det-assembly` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `rmk:apparatus:five-column-literature-gap` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `def:apparatus:five-column-tensor` | definition | faithful | lean_substantive | `SixBirdsBSD.Apparatus.Comparison.fiveColumnTensor` |
| `thm:apparatus:five-col-bk-comparison` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.Comparison.fiveColBkComparison` |
| `def:apparatus:rank-two-kummer-source` | definition | faithful | lean_substantive | `SixBirdsBSD.Apparatus.HigherRankNoGo.rankTwoKummerSource` |
| `thm:apparatus:rank-two-height-schur-collapse` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.HigherRankNoGo.rankTwoHeightSchurCollapse` |
| `thm:apparatus:gram-matrix-shadow` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.HigherRankNoGo.gramMatrixShadow` |
| `thm:apparatus:finite-window-no-go` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.GlobalAuditNoGo.finiteWindowNoGo` |
| `thm:apparatus:finite-prime-cover-no-go` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.SupportPrimeNoGo.finitePrimeCoverNoGo` |
| `def:apparatus:support-prime-truncation-residual` | definition | faithful | lean_substantive | `SixBirdsBSD.Apparatus.SupportPrimeNoGo.supportPrimeTruncationResidual` |
| `rmk:apparatus:support-prime-atlas` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `def:apparatus:vsrc-algebra` | definition | narrowed_surrogate | narrowed_surrogate | `SixBirdsBSD.Apparatus.Vsrc.vsrcAlgebra` |
| `thm:apparatus:vsrc-stage-i-consistency` | theorem | narrowed_surrogate | narrowed_surrogate | `SixBirdsBSD.Apparatus.Vsrc.vsrcStageIConsistency` |
| `rmk:apparatus:vsrc-no-licensed-descent` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `thm:apparatus:vsrc-stage-ii-gz-partial` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.Vsrc.vsrcStageIIGzPartial` |
| `thm:apparatus:vsrc-stage-iii-translation` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.Vsrc.vsrcStageIIITranslation` |
| `rmk:apparatus:vsrc-rank-r-stronger` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `thm:apparatus:kappa-r-normalization-equivalence` | theorem | faithful | lean_substantive | `SixBirdsBSD.Apparatus.KappaNormalization.kappaRNormalizationEquivalence` |
| **closure** | | | | |
| `def:closure:chi-ct-p-import` | definition | faithful | typed_structure_carrier | `SixBirdsBSD.Closure.Imports.chiCTpImport` |
| `def:closure:a-e-import` | definition | faithful | typed_structure_carrier | `SixBirdsBSD.Closure.Imports.aEImport` |
| `def:closure:beilinson-import` | definition | faithful | typed_structure_carrier | `SixBirdsBSD.Closure.Imports.beilinsonImport` |
| `nonclaim:closure:imports-not-derived` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `def:closure:gamma-padic-descent` | recognition_source | narrowed_surrogate | typed_structure_carrier | `SixBirdsBSD.Closure.RecognitionSources.gammaPadicDescent` |
| `def:closure:gamma-sha-persistence` | recognition_source | narrowed_surrogate | typed_structure_carrier | `SixBirdsBSD.Closure.RecognitionSources.gammaShaPersistence` |
| `def:closure:gamma-higher-gz-fixity` | recognition_source | narrowed_surrogate | typed_structure_carrier | `SixBirdsBSD.Closure.RecognitionSources.gammaHigherGZFixity` |
| `nonclaim:closure:recognition-sources-not-derived` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `def:closure:sel-bsd-shell` | definition | faithful | lean_substantive | `SixBirdsBSD.Closure.SelShell.selBSDShell` |
| `def:closure:pi-bsd` | definition | faithful | lean_substantive | `SixBirdsBSD.Closure.SelShell.piBSD` |
| `thm:closure:pi-bsd-iff-strong-bsd` | theorem | faithful | lean_substantive | `SixBirdsBSD.Closure.SelShell.piBSDIffStrongBSD` |
| `thm:closure:master-theorem-applicability` | theorem | faithful | lean_substantive | `SixBirdsBSD.Closure.SelShell.masterTheoremApplicability` |
| `thm:closure:composite-signature` | theorem | projection_packaged | projection_packaged | `SixBirdsBSD.Closure.SelShell.compositeSignature` |
| `thm:closure:chi-ct-p-comparison` | theorem | projection_packaged | projection_packaged | `SixBirdsBSD.Closure.ChiCTp.chiCTpComparison` |
| `def:closure:eta-published-imports` | definition | faithful | typed_structure_carrier | `SixBirdsBSD.Closure.EtaFormula.etaPublishedImports` |
| `thm:closure:oc-eta-formula` | theorem | projection_packaged | projection_packaged | `SixBirdsBSD.Closure.EtaFormula.ocEtaFormula` |
| `def:closure:t-cascade-import` | definition | faithful | typed_structure_carrier | `SixBirdsBSD.Closure.TCascade.tCascadeImport` |
| `thm:closure:t-cascade-rank-le-1` | theorem | projection_packaged | projection_packaged | `SixBirdsBSD.Closure.TCascade.tCascadeRankLeOne` |
| `thm:closure:t-e12-no-go` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `thm:closure:t-bad-no-go` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `rmk:closure:mode-b-residuals` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `thm:closure:strong-bsd-conditional` | theorem | projection_packaged | projection_packaged | `SixBirdsBSD.Closure.Landing.strongBSDConditional` |
| `nonclaim:closure:landing-conditional` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
| `def:closure:aor-sel-instance` | definition | faithful | lean_substantive | `SixBirdsBSD.Closure.AORInstance.aorSelInstance` |
| `thm:closure:aor-mechanical-records` | theorem | faithful | lean_substantive | `SixBirdsBSD.Closure.AORInstance.aorMechanicalRecords` |
| `thm:closure:aor-recognition-discharge` | theorem | faithful | lean_substantive | `SixBirdsBSD.Closure.AORInstance.aorRecognitionDischarge` |
| `thm:closure:aor-instance` | theorem | narrowed_surrogate | narrowed_surrogate | `SixBirdsBSD.Closure.AORInstance.aorInstance` |
| `rmk:closure:aor-partial-status` | not_mechanized | not_applicable | support_only / nonclaim | `—` |
