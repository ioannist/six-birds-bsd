import SixBirdsBSD.Apparatus.Decomposition
import SixBirdsBSD.Apparatus.HeightRegulator
import SixBirdsBSD.Apparatus.AnalyticPeriod
import SixBirdsBSD.Apparatus.FiniteSource
import SixBirdsBSD.Apparatus.PAdic
import SixBirdsBSD.Apparatus.DetAssembly
import SixBirdsBSD.Apparatus.Comparison
import SixBirdsBSD.Apparatus.NormalizationChecks
import SixBirdsBSD.Apparatus.FinitePresentation
import SixBirdsBSD.Apparatus.HigherRankNoGo
import SixBirdsBSD.Apparatus.GlobalAuditNoGo
import SixBirdsBSD.Apparatus.SupportPrimeNoGo
import SixBirdsBSD.Apparatus.Vsrc
import SixBirdsBSD.Apparatus.KappaNormalization

/-!
Apparatus-axis umbrella module (Paper A). Re-exports the per-section
modules under `SixBirdsBSD/Apparatus/`: the typed five-column Bloch–Kato
decomposition, the per-column Schur-collapse adequacy theorems, the
`Φ_5col↔BK` comparison, the NG-1…NG-5 no-go suite, the `vsrc_r`
calibration, and the `κ_r` normalization equivalence. The consolidated
mathematical source record is
`anti_loc/extracted_math/apparatus_master.md`.
-/
