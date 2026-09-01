import SixBirdsBSD.Apparatus.HeightRegulator

/-!
`SixBirdsBSD.Apparatus.AnalyticPeriod` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § AnalyticPeriod.
-/

namespace SixBirdsBSD.Apparatus.AnalyticPeriod

universe u

/-- The real analytic/period map sends `(A_E, Omega_E^+)` to `(A_E/Omega_E^+) e`. -/
def analyticPeriodMap {Scalar Line : Type u}
    (div : Scalar → Scalar → Scalar)
    (smul : Scalar → Line → Line)
    (e_an_per : Line) : Scalar × Scalar → Line
  | (A_E, Omega_E_pos) => smul (div A_E Omega_E_pos) e_an_per

/-- The two-coordinate analytic/period tangent Schur residual collapses to zero. -/
theorem analyticPeriodSchurCollapse :
    let d : Fin 2 → Int := fun i => if i = 0 then 1 else -1
    let xA : Fin 2 → Int := fun i => if i = 0 then 1 else 0
    let K_DD := HeightRegulator.dot d d
    let fullProjection := HeightRegulator.dot d
      (HeightRegulator.mulVec HeightRegulator.heightKLL d)
    let Xi_full := K_DD - fullProjection
    let noSourceResidual := K_DD
    let xAOnlyResidual := K_DD -
      (HeightRegulator.dot d xA) * (HeightRegulator.dot d xA)
    K_DD = 2 ∧ fullProjection = 2 ∧ Xi_full = 0 ∧
      noSourceResidual = 2 ∧ xAOnlyResidual = 1 := by
  let d : Fin 2 → Int := fun i => if i = 0 then 1 else -1
  have hproj :
      HeightRegulator.mulVec HeightRegulator.heightKLL d = d :=
    HeightRegulator.heightKLLMulVec d
  dsimp only
  constructor
  · decide
  · constructor
    · rw [hproj]
      decide
    · constructor
      · rw [hproj]
        decide
      · constructor
        · decide
        · decide

end SixBirdsBSD.Apparatus.AnalyticPeriod
