import SixBirdsBSD.Closure.Imports
import SixBirdsBSD.Closure.RecognitionSources
import SixBirdsBSD.Closure.ChiCTp
import SixBirdsBSD.Closure.CTInstanceChecks
import SixBirdsBSD.Closure.CTSignTransport
import SixBirdsBSD.Closure.EtaFormula
import SixBirdsBSD.Closure.EtaApplicability
import SixBirdsBSD.Closure.TCascade
import SixBirdsBSD.Closure.Obstructions
import SixBirdsBSD.Closure.SelShell
import SixBirdsBSD.Closure.Landing
import SixBirdsBSD.Closure.CoupledFactors
import SixBirdsBSD.Closure.RationalLocalGlobal
import SixBirdsBSD.Closure.LocalUnitSupport
import SixBirdsBSD.Closure.ShaDescent
import SixBirdsBSD.Closure.ShaDimensionPair
import SixBirdsBSD.Closure.ShaFourNormalization
import SixBirdsBSD.Closure.OddPrimaryBridge
import SixBirdsBSD.Closure.AdditiveFrobeniusDescent
import SixBirdsBSD.Closure.TameComponentReturn
import SixBirdsBSD.Closure.GlobalTameProduct
import SixBirdsBSD.Closure.CoverBetaRefinement
import SixBirdsBSD.Closure.KummerComponentErasure
import SixBirdsBSD.Closure.CTDerivedTransport
import SixBirdsBSD.Closure.CTPfaffianRoot
import SixBirdsBSD.Closure.StarkCoreVertices
import SixBirdsBSD.Closure.StarkInverseLimit
import SixBirdsBSD.Closure.StarkCoefficientNaturality
import SixBirdsBSD.Closure.AORPrimitives
import SixBirdsBSD.Closure.AORInstance

/-!
Closure-axis umbrella module (Paper B, flagship).

Re-exports the per-section closure Lean modules under
`SixBirdsBSD/Closure/`: the
imported theorem-record structures (`χ_{CT,p}`/T_E1–T_E8, `A_E`,
Beilinson rank-≥2), the three recognition-source carriers
(`Γ_BSD^padic-descent`, `Γ_BSD^Sha-persistence`,
`Γ_BSD^higher-GZ-fixity`), the `Sel!_BSD` closure architecture, the
scalar readout of `Π_BSD` and residual-zero equivalence, the supporting conditional theorems
(`χ_{CT,p}` comparison, the OC `η`-formula, rank-≤1 `T_CASCADE`), the
local AOR register instance, and the conditional Strong BSD landing.

The two AOR modules provide the local, non-eliminative AOR surface. The
consolidated mathematical source record is
`anti_loc/extracted_math/closure_master.md`.
-/
