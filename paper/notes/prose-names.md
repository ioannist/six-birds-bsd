# Prose names for mechanized objects (both papers)

*Phase 1 deliverable. Closed 2026-05-29. Lean decl → paper-prose name.
The prose name is what body text uses; the Lean decl appears only in
App D. Proposed names below (humanized from the label short-name);
refine during drafting.*

## apparatus (30 mechanized)

| paper_label | proposed prose name | lean_decl |
|---|---|---|
| `def:apparatus:bk-component-map` | bk component map | `SixBirdsBSD.Apparatus.Decomposition.bkComponentMap` |
| `def:apparatus:bridge-defect-equation` | bridge defect equation | `SixBirdsBSD.Apparatus.Decomposition.bridgeDefectEquation` |
| `thm:apparatus:component-killing` | component killing | `SixBirdsBSD.Apparatus.Decomposition.componentKilling` |
| `thm:apparatus:finite-scalar-public-shadow` | finite scalar public shadow | `SixBirdsBSD.Apparatus.Decomposition.finiteScalarPublicShadow` |
| `def:apparatus:height-regulator-map` | height regulator map | `SixBirdsBSD.Apparatus.HeightRegulator.heightRegulatorMap` |
| `thm:apparatus:height-schur-collapse` | height schur collapse | `SixBirdsBSD.Apparatus.HeightRegulator.heightSchurCollapse` |
| `def:apparatus:analytic-period-map` | analytic period map | `SixBirdsBSD.Apparatus.AnalyticPeriod.analyticPeriodMap` |
| `thm:apparatus:analytic-period-schur-collapse` | analytic period schur collapse | `SixBirdsBSD.Apparatus.AnalyticPeriod.analyticPeriodSchurCollapse` |
| `def:apparatus:finite-source-map` | finite source map | `SixBirdsBSD.Apparatus.FiniteSource.finiteSourceMap` |
| `thm:apparatus:finite-source-schur-collapse` | finite source schur collapse | `SixBirdsBSD.Apparatus.FiniteSource.finiteSourceSchurCollapse` |
| `thm:apparatus:scalar-finite-shadow` | scalar finite shadow | `SixBirdsBSD.Apparatus.FiniteSource.scalarFiniteShadow` |
| `thm:apparatus:dim-sha-shadow` | dim sha shadow | `SixBirdsBSD.Apparatus.FiniteSource.dimShaShadow` |
| `def:apparatus:p-adic-map` | p adic map | `SixBirdsBSD.Apparatus.PAdic.pAdicMap` |
| `thm:apparatus:ordinary-schur-collapse` | ordinary schur collapse | `SixBirdsBSD.Apparatus.PAdic.ordinarySchurCollapse` |
| `thm:apparatus:signed-schur-collapse` | signed schur collapse | `SixBirdsBSD.Apparatus.PAdic.signedSchurCollapse` |
| `def:apparatus:det-assembly-map` | det assembly map | `SixBirdsBSD.Apparatus.DetAssembly.detAssemblyMap` |
| `thm:apparatus:cascade-completion-signature` | cascade completion signature | `SixBirdsBSD.Apparatus.DetAssembly.cascadeCompletionSignature` |
| `def:apparatus:five-column-tensor` | five column tensor | `SixBirdsBSD.Apparatus.Comparison.fiveColumnTensor` |
| `thm:apparatus:five-col-bk-comparison` | five col bk comparison | `SixBirdsBSD.Apparatus.Comparison.fiveColBkComparison` |
| `def:apparatus:rank-two-kummer-source` | rank two kummer source | `SixBirdsBSD.Apparatus.HigherRankNoGo.rankTwoKummerSource` |
| `thm:apparatus:rank-two-height-schur-collapse` | rank two height schur collapse | `SixBirdsBSD.Apparatus.HigherRankNoGo.rankTwoHeightSchurCollapse` |
| `thm:apparatus:gram-matrix-shadow` | gram matrix shadow | `SixBirdsBSD.Apparatus.HigherRankNoGo.gramMatrixShadow` |
| `thm:apparatus:finite-window-no-go` | finite window no go | `SixBirdsBSD.Apparatus.GlobalAuditNoGo.finiteWindowNoGo` |
| `thm:apparatus:finite-prime-cover-no-go` | finite prime cover no go | `SixBirdsBSD.Apparatus.SupportPrimeNoGo.finitePrimeCoverNoGo` |
| `def:apparatus:support-prime-truncation-residual` | support prime truncation residual | `SixBirdsBSD.Apparatus.SupportPrimeNoGo.supportPrimeTruncationResidual` |
| `def:apparatus:vsrc-algebra` | vsrc algebra | `SixBirdsBSD.Apparatus.Vsrc.vsrcAlgebra` |
| `thm:apparatus:vsrc-stage-i-consistency` | vsrc stage i consistency | `SixBirdsBSD.Apparatus.Vsrc.vsrcStageIConsistency` |
| `thm:apparatus:vsrc-stage-ii-gz-partial` | vsrc stage ii gz partial | `SixBirdsBSD.Apparatus.Vsrc.vsrcStageIIGzPartial` |
| `thm:apparatus:vsrc-stage-iii-translation` | vsrc stage iii translation | `SixBirdsBSD.Apparatus.Vsrc.vsrcStageIIITranslation` |
| `thm:apparatus:kappa-r-normalization-equivalence` | kappa r normalization equivalence | `SixBirdsBSD.Apparatus.KappaNormalization.kappaRNormalizationEquivalence` |

## closure (21 mechanized)

| paper_label | proposed prose name | lean_decl |
|---|---|---|
| `def:closure:chi-ct-p-import` | chi ct p import | `SixBirdsBSD.Closure.Imports.chiCTpImport` |
| `def:closure:a-e-import` | a e import | `SixBirdsBSD.Closure.Imports.aEImport` |
| `def:closure:beilinson-import` | beilinson import | `SixBirdsBSD.Closure.Imports.beilinsonImport` |
| `def:closure:gamma-padic-descent` | gamma padic descent | `SixBirdsBSD.Closure.RecognitionSources.gammaPadicDescent` |
| `def:closure:gamma-sha-persistence` | gamma sha persistence | `SixBirdsBSD.Closure.RecognitionSources.gammaShaPersistence` |
| `def:closure:gamma-higher-gz-fixity` | gamma higher gz fixity | `SixBirdsBSD.Closure.RecognitionSources.gammaHigherGZFixity` |
| `def:closure:sel-bsd-shell` | sel bsd shell | `SixBirdsBSD.Closure.SelShell.selBSDShell` |
| `def:closure:pi-bsd` | pi bsd | `SixBirdsBSD.Closure.SelShell.piBSD` |
| `thm:closure:pi-bsd-iff-strong-bsd` | pi bsd iff strong bsd | `SixBirdsBSD.Closure.SelShell.piBSDIffStrongBSD` |
| `thm:closure:master-theorem-applicability` | master theorem applicability | `SixBirdsBSD.Closure.SelShell.masterTheoremApplicability` |
| `thm:closure:composite-signature` | composite signature | `SixBirdsBSD.Closure.SelShell.compositeSignature` |
| `thm:closure:chi-ct-p-comparison` | chi ct p comparison | `SixBirdsBSD.Closure.ChiCTp.chiCTpComparison` |
| `def:closure:eta-published-imports` | eta published imports | `SixBirdsBSD.Closure.EtaFormula.etaPublishedImports` |
| `thm:closure:oc-eta-formula` | oc eta formula | `SixBirdsBSD.Closure.EtaFormula.ocEtaFormula` |
| `def:closure:t-cascade-import` | t cascade import | `SixBirdsBSD.Closure.TCascade.tCascadeImport` |
| `thm:closure:t-cascade-rank-le-1` | t cascade rank le 1 | `SixBirdsBSD.Closure.TCascade.tCascadeRankLeOne` |
| `thm:closure:strong-bsd-conditional` | strong bsd conditional | `SixBirdsBSD.Closure.Landing.strongBSDConditional` |
| `def:closure:aor-sel-instance` | aor sel instance | `SixBirdsBSD.Closure.AORInstance.aorSelInstance` |
| `thm:closure:aor-mechanical-records` | aor mechanical records | `SixBirdsBSD.Closure.AORInstance.aorMechanicalRecords` |
| `thm:closure:aor-recognition-discharge` | aor recognition discharge | `SixBirdsBSD.Closure.AORInstance.aorRecognitionDischarge` |
| `thm:closure:aor-instance` | aor instance | `SixBirdsBSD.Closure.AORInstance.aorInstance` |

