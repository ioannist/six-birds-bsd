# Statements of record (review rendering)

*Phase 2 deliverable. Closed 2026-05-29. Human-readable rendering of
`statements-of-record.yml` (the binding data). Regenerate if the YAML
changes. 69 rows: 41 apparatus + 28 closure; 51 mechanized.*

## apparatus (41 rows)

| label | kind | section | dest | coverage | alignment | lean_decl |
|---|---|---|---|---|---|---|
| `def:apparatus:bk-component-map` | definition | Decomposition | body | definition | faithful | `SixBirdsBSD.Apparatus.Decomposition.bkComponentMap` |
| `def:apparatus:bridge-defect-equation` | definition | Decomposition | body | definition | faithful | `SixBirdsBSD.Apparatus.Decomposition.bridgeDefectEquation` |
| `thm:apparatus:component-killing` | theorem | Decomposition | body | theorem | faithful | `SixBirdsBSD.Apparatus.Decomposition.componentKilling` |
| `thm:apparatus:finite-scalar-public-shadow` | theorem | Decomposition | body | theorem | faithful | `SixBirdsBSD.Apparatus.Decomposition.finiteScalarPublicShadow` |
| `nonclaim:apparatus:decomposition-scope` | nonclaim | Decomposition | appendix | not_mechanized | not_applicable | `—` |
| `def:apparatus:height-regulator-map` | definition | HeightRegulator | body | definition | faithful | `SixBirdsBSD.Apparatus.HeightRegulator.heightRegulatorMap` |
| `thm:apparatus:height-schur-collapse` | theorem | HeightRegulator | body | theorem | faithful | `SixBirdsBSD.Apparatus.HeightRegulator.heightSchurCollapse` |
| `obl:apparatus:rho-ht-reg-transport` | obligation | HeightRegulator | appendix | not_mechanized | not_applicable | `—` |
| `warn:apparatus:571a1-carrier` | warning | HeightRegulator | appendix | not_mechanized | not_applicable | `—` |
| `def:apparatus:analytic-period-map` | definition | AnalyticPeriod | body | definition | faithful | `SixBirdsBSD.Apparatus.AnalyticPeriod.analyticPeriodMap` |
| `thm:apparatus:analytic-period-schur-collapse` | theorem | AnalyticPeriod | body | theorem | faithful | `SixBirdsBSD.Apparatus.AnalyticPeriod.analyticPeriodSchurCollapse` |
| `obl:apparatus:rho-an-period-transport` | obligation | AnalyticPeriod | appendix | not_mechanized | not_applicable | `—` |
| `def:apparatus:finite-source-map` | definition | FiniteSource | body | definition | faithful | `SixBirdsBSD.Apparatus.FiniteSource.finiteSourceMap` |
| `thm:apparatus:finite-source-schur-collapse` | theorem | FiniteSource | body | theorem | faithful | `SixBirdsBSD.Apparatus.FiniteSource.finiteSourceSchurCollapse` |
| `thm:apparatus:scalar-finite-shadow` | theorem | FiniteSource | body | theorem | faithful | `SixBirdsBSD.Apparatus.FiniteSource.scalarFiniteShadow` |
| `thm:apparatus:dim-sha-shadow` | theorem | FiniteSource | body | theorem | faithful | `SixBirdsBSD.Apparatus.FiniteSource.dimShaShadow` |
| `obl:apparatus:rho-finite-transport` | obligation | FiniteSource | appendix | not_mechanized | not_applicable | `—` |
| `def:apparatus:p-adic-map` | definition | PAdic | body | definition | faithful | `SixBirdsBSD.Apparatus.PAdic.pAdicMap` |
| `thm:apparatus:ordinary-schur-collapse` | theorem | PAdic | body | theorem | faithful | `SixBirdsBSD.Apparatus.PAdic.ordinarySchurCollapse` |
| `thm:apparatus:signed-schur-collapse` | theorem | PAdic | body | theorem | faithful | `SixBirdsBSD.Apparatus.PAdic.signedSchurCollapse` |
| `obl:apparatus:rho-p-transport` | obligation | PAdic | appendix | not_mechanized | not_applicable | `—` |
| `def:apparatus:det-assembly-map` | definition | DetAssembly | body | definition | faithful | `SixBirdsBSD.Apparatus.DetAssembly.detAssemblyMap` |
| `thm:apparatus:cascade-completion-signature` | theorem | DetAssembly | body | theorem | faithful | `SixBirdsBSD.Apparatus.DetAssembly.cascadeCompletionSignature` |
| `obl:apparatus:rho-det-assembly` | obligation | DetAssembly | appendix | not_mechanized | not_applicable | `—` |
| `rmk:apparatus:five-column-literature-gap` | remark | Comparison | appendix | not_mechanized | not_applicable | `—` |
| `def:apparatus:five-column-tensor` | definition | Comparison | body | definition | faithful | `SixBirdsBSD.Apparatus.Comparison.fiveColumnTensor` |
| `thm:apparatus:five-col-bk-comparison` | theorem | Comparison | body | theorem | faithful | `SixBirdsBSD.Apparatus.Comparison.fiveColBkComparison` |
| `def:apparatus:rank-two-kummer-source` | definition | HigherRankNoGo | body | definition | faithful | `SixBirdsBSD.Apparatus.HigherRankNoGo.rankTwoKummerSource` |
| `thm:apparatus:rank-two-height-schur-collapse` | theorem | HigherRankNoGo | body | theorem | faithful | `SixBirdsBSD.Apparatus.HigherRankNoGo.rankTwoHeightSchurCollapse` |
| `thm:apparatus:gram-matrix-shadow` | theorem | HigherRankNoGo | body | theorem | faithful | `SixBirdsBSD.Apparatus.HigherRankNoGo.gramMatrixShadow` |
| `thm:apparatus:finite-window-no-go` | theorem | GlobalAuditNoGo | body | theorem | faithful | `SixBirdsBSD.Apparatus.GlobalAuditNoGo.finiteWindowNoGo` |
| `thm:apparatus:finite-prime-cover-no-go` | theorem | SupportPrimeNoGo | body | theorem | faithful | `SixBirdsBSD.Apparatus.SupportPrimeNoGo.finitePrimeCoverNoGo` |
| `def:apparatus:support-prime-truncation-residual` | definition | SupportPrimeNoGo | body | definition | faithful | `SixBirdsBSD.Apparatus.SupportPrimeNoGo.supportPrimeTruncationResidual` |
| `rmk:apparatus:support-prime-atlas` | remark | SupportPrimeNoGo | appendix | not_mechanized | not_applicable | `—` |
| `def:apparatus:vsrc-algebra` | definition | Vsrc | body | definition | narrowed_surrogate | `SixBirdsBSD.Apparatus.Vsrc.vsrcAlgebra` |
| `thm:apparatus:vsrc-stage-i-consistency` | theorem | Vsrc | body | theorem | narrowed_surrogate | `SixBirdsBSD.Apparatus.Vsrc.vsrcStageIConsistency` |
| `rmk:apparatus:vsrc-no-licensed-descent` | remark | Vsrc | appendix | not_mechanized | not_applicable | `—` |
| `thm:apparatus:vsrc-stage-ii-gz-partial` | theorem | Vsrc | body | theorem | faithful | `SixBirdsBSD.Apparatus.Vsrc.vsrcStageIIGzPartial` |
| `thm:apparatus:vsrc-stage-iii-translation` | theorem | Vsrc | body | theorem | faithful | `SixBirdsBSD.Apparatus.Vsrc.vsrcStageIIITranslation` |
| `rmk:apparatus:vsrc-rank-r-stronger` | remark | Vsrc | appendix | not_mechanized | not_applicable | `—` |
| `thm:apparatus:kappa-r-normalization-equivalence` | theorem | KappaNormalization | body | theorem | faithful | `SixBirdsBSD.Apparatus.KappaNormalization.kappaRNormalizationEquivalence` |

## closure (28 rows)

| label | kind | section | dest | coverage | alignment | lean_decl |
|---|---|---|---|---|---|---|
| `def:closure:chi-ct-p-import` | definition | Imports | body | definition | faithful | `SixBirdsBSD.Closure.Imports.chiCTpImport` |
| `def:closure:a-e-import` | definition | Imports | body | definition | faithful | `SixBirdsBSD.Closure.Imports.aEImport` |
| `def:closure:beilinson-import` | definition | Imports | body | definition | faithful | `SixBirdsBSD.Closure.Imports.beilinsonImport` |
| `nonclaim:closure:imports-not-derived` | nonclaim | Imports | appendix | not_mechanized | not_applicable | `—` |
| `def:closure:gamma-padic-descent` | definition | RecognitionSources | body | recognition_source | narrowed_surrogate | `SixBirdsBSD.Closure.RecognitionSources.gammaPadicDescent` |
| `def:closure:gamma-sha-persistence` | definition | RecognitionSources | body | recognition_source | narrowed_surrogate | `SixBirdsBSD.Closure.RecognitionSources.gammaShaPersistence` |
| `def:closure:gamma-higher-gz-fixity` | definition | RecognitionSources | body | recognition_source | narrowed_surrogate | `SixBirdsBSD.Closure.RecognitionSources.gammaHigherGZFixity` |
| `nonclaim:closure:recognition-sources-not-derived` | nonclaim | RecognitionSources | appendix | not_mechanized | not_applicable | `—` |
| `def:closure:sel-bsd-shell` | definition | SelShell | body | definition | faithful | `SixBirdsBSD.Closure.SelShell.selBSDShell` |
| `def:closure:pi-bsd` | definition | SelShell | body | definition | faithful | `SixBirdsBSD.Closure.SelShell.piBSD` |
| `thm:closure:pi-bsd-iff-strong-bsd` | theorem | SelShell | body | theorem | faithful | `SixBirdsBSD.Closure.SelShell.piBSDIffStrongBSD` |
| `thm:closure:master-theorem-applicability` | theorem | SelShell | body | theorem | faithful | `SixBirdsBSD.Closure.SelShell.masterTheoremApplicability` |
| `thm:closure:composite-signature` | theorem | SelShell | body | theorem | projection_packaged | `SixBirdsBSD.Closure.SelShell.compositeSignature` |
| `thm:closure:chi-ct-p-comparison` | theorem | ChiCTp | body | theorem | projection_packaged | `SixBirdsBSD.Closure.ChiCTp.chiCTpComparison` |
| `def:closure:eta-published-imports` | definition | EtaFormula | body | definition | faithful | `SixBirdsBSD.Closure.EtaFormula.etaPublishedImports` |
| `thm:closure:oc-eta-formula` | theorem | EtaFormula | body | theorem | projection_packaged | `SixBirdsBSD.Closure.EtaFormula.ocEtaFormula` |
| `def:closure:t-cascade-import` | definition | TCascade | body | definition | faithful | `SixBirdsBSD.Closure.TCascade.tCascadeImport` |
| `thm:closure:t-cascade-rank-le-1` | theorem | TCascade | body | theorem | projection_packaged | `SixBirdsBSD.Closure.TCascade.tCascadeRankLeOne` |
| `thm:closure:t-e12-no-go` | theorem | Obstructions | appendix | not_mechanized | not_applicable | `—` |
| `thm:closure:t-bad-no-go` | theorem | Obstructions | appendix | not_mechanized | not_applicable | `—` |
| `rmk:closure:mode-b-residuals` | remark | Obstructions | appendix | not_mechanized | not_applicable | `—` |
| `thm:closure:strong-bsd-conditional` | theorem | Landing | body | theorem | projection_packaged | `SixBirdsBSD.Closure.Landing.strongBSDConditional` |
| `nonclaim:closure:landing-conditional` | nonclaim | Landing | appendix | not_mechanized | not_applicable | `—` |
| `def:closure:aor-sel-instance` | definition | AORInstance | body | definition | faithful | `SixBirdsBSD.Closure.AORInstance.aorSelInstance` |
| `thm:closure:aor-mechanical-records` | theorem | AORInstance | body | theorem | faithful | `SixBirdsBSD.Closure.AORInstance.aorMechanicalRecords` |
| `thm:closure:aor-recognition-discharge` | theorem | AORInstance | body | theorem | faithful | `SixBirdsBSD.Closure.AORInstance.aorRecognitionDischarge` |
| `thm:closure:aor-instance` | theorem | AORInstance | body | theorem | narrowed_surrogate | `SixBirdsBSD.Closure.AORInstance.aorInstance` |
| `rmk:closure:aor-partial-status` | remark | AORInstance | appendix | not_mechanized | not_applicable | `—` |

