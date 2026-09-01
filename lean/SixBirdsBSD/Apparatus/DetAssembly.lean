import SixBirdsBSD.Apparatus.FiniteSource

/-!
`SixBirdsBSD.Apparatus.DetAssembly` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § DetAssembly.
-/

namespace SixBirdsBSD.Apparatus.DetAssembly

open SixBirdsBSD.Apparatus.HeightRegulator

universe u

/-- The real determinant-assembly map multiplies the local tensor by its orientation. -/
def detAssemblyMap {Ht An Finite PAdic Orientation LocalTensor Target : Type u}
    (assembleLocal : Ht → An → Finite → PAdic → LocalTensor)
    (mulOrientation : LocalTensor → Orientation → Target) :
    Ht × An × Finite × PAdic × Orientation → Target
  | (ht, an, finite, padic, orientation) =>
      mulOrientation (assembleLocal ht an finite padic) orientation

def cascadeSourceRow : Fin 5 → Int :=
  fun i => if i = 4 then 0 else 1

def cascadeTargetRow : Fin 5 → Int :=
  fun _ => 1

def determinantOrientationRow : Fin 5 → Int :=
  fun i => if i = 4 then 1 else 0

/-- The four constructed rows leave exactly the determinant-orientation residual. -/
theorem cascadeCompletionSignature :
    let ell := cascadeSourceRow
    let d := cascadeTargetRow
    let K_DD := dot d d
    let K_LL := dot ell ell
    let K_DL := dot d ell
    let schurProjection := (K_DL * K_DL) / K_LL
    let Xi_C := K_DD - schurProjection
    K_DD = 5 ∧ K_LL = 4 ∧ K_DL = 4 ∧ schurProjection = 4 ∧ Xi_C = 1 ∧
      (fun i => d i - ell i) = determinantOrientationRow := by
  dsimp only
  constructor
  · decide
  · constructor
    · decide
    · constructor
      · decide
      · constructor
        · decide
        · constructor
          · decide
          · funext i
            by_cases h : i = 4
            · simp [cascadeTargetRow, cascadeSourceRow, determinantOrientationRow, h]
            · simp [cascadeTargetRow, cascadeSourceRow, determinantOrientationRow, h]

end SixBirdsBSD.Apparatus.DetAssembly
