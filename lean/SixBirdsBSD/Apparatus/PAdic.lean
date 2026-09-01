import SixBirdsBSD.Apparatus.FiniteSource

/-!
`SixBirdsBSD.Apparatus.PAdic` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § PAdic.
-/

namespace SixBirdsBSD.Apparatus.PAdic

open SixBirdsBSD.Apparatus.HeightRegulator
open SixBirdsBSD.Apparatus.FiniteSource

universe u

/-- The real p-adic map has ordinary and signed local branches. -/
def pAdicMap {Tplus Hf Exp Hplus Hminus Target : Type u}
    (rhoOrd : Tplus → Hf → Exp → Target)
    (rhoSigned : Hplus → Hminus → Exp → Target) :
    Sum (Tplus × Hf × Exp) (Hplus × Hminus × Exp) → Target
  | Sum.inl (tplus, hf, expStar) => rhoOrd tplus hf expStar
  | Sum.inr (hplus, hminus, expStar) => rhoSigned hplus hminus expStar

def omitOrdProjector : Fin 3 → Fin 3 → Int :=
  fun i j => if i = j then if i = 0 then 0 else 1 else 0

def omitOrdXi : Fin 3 → Fin 3 → Int :=
  matSub heightKLL omitOrdProjector

def unsignedProjection (y : Fin 3 → Int) : Int × Int :=
  (y 0 + y 1, y 2)

def signedPlusWitness : Fin 3 → Int :=
  fun i => if i = 0 then 1 else 0

def signedMinusWitness : Fin 3 → Int :=
  fun i => if i = 1 then 1 else 0

def ratDot {n : Nat} (u v : Fin n → Rat) : Rat :=
  sumFinRat (fun i => u i * v i)

def unsignedU1 : Fin 3 → Rat :=
  fun i => if i = 0 then 1 else if i = 1 then 1 else 0

def unsignedU2 : Fin 3 → Rat :=
  fun i => if i = 2 then 1 else 0

def unsignedProjector : Fin 3 → Fin 3 → Rat :=
  fun i j => (unsignedU1 i * unsignedU1 j) / 2 + (unsignedU2 i * unsignedU2 j) / 1

theorem ratOneDivOne : ((1 : Rat) / 1) = 1 := by
  rw [show ((1 : Rat) / 1) = Rat.divInt 1 1 by
    exact (Rat.divInt_eq_div 1 1).symm]
  exact Rat.divInt_self' (by decide : (1 : Int) ≠ 0)

theorem ratOneHalfAddOneHalf : ((1 : Rat) / 2 + 1 / 2) = 1 := by
  rw [show ((1 : Rat) / 2) = Rat.divInt 1 2 by
    exact (Rat.divInt_eq_div 1 2).symm]
  simp
  exact Rat.divInt_self' (by decide : (4 : Int) ≠ 0)

theorem ratTwoDivTwo : ((2 : Rat) / 2) = 1 := by
  rw [show ((2 : Rat) / 2) = Rat.divInt 2 2 by
    exact (Rat.divInt_eq_div 2 2).symm]
  exact Rat.divInt_self' (by decide : (2 : Int) ≠ 0)

theorem ratOneAddOne : ((1 : Rat) + 1) = 2 := by
  rw [Rat.add_def, Rat.normalize_eq_mkRat]
  unfold mkRat
  simp [Rat.normalize_eq_mk']

theorem ratThreeSubTwo : ((3 : Rat) - 2) = 1 := by
  rw [Rat.sub_def, Rat.normalize_eq_mkRat]
  unfold mkRat
  simp [Rat.normalize_eq_mk']

theorem unsignedSourceDotProducts :
    ratDot unsignedU1 unsignedU1 = 2 ∧
      ratDot unsignedU2 unsignedU2 = 1 ∧
      ratDot unsignedU1 unsignedU2 = 0 := by
  constructor
  · simp [ratDot, sumFinRat, unsignedU1]
    rw [show ((0 : Rat) + 1) = 1 by exact Rat.zero_add 1]
    rw [ratOneAddOne]
    exact Rat.add_zero 2
  · constructor
    · simp [ratDot, sumFinRat, unsignedU2]
      rw [show ((0 : Rat) + 0) = 0 by exact Rat.zero_add 0]
      rw [show ((0 : Rat) + 0) = 0 by exact Rat.zero_add 0]
      exact Rat.zero_add 1
    · simp [ratDot, sumFinRat, unsignedU1, unsignedU2]
      rw [show ((0 : Rat) + 0) = 0 by exact Rat.zero_add 0]
      rw [show ((0 : Rat) + 0) = 0 by exact Rat.zero_add 0]
      exact Rat.zero_add 0

theorem unsignedProjectorTrace :
    traceRat unsignedProjector =
        ratDot unsignedU1 unsignedU1 / 2 + ratDot unsignedU2 unsignedU2 / 1 ∧
      traceRat unsignedProjector = 2 := by
  have hdot := unsignedSourceDotProducts
  have hleft : traceRat unsignedProjector = 2 := by
    simp [traceRat, unsignedProjector, sumFinRat, unsignedU1, unsignedU2]
    rw [show ((0 : Rat) / 1) = 0 by
      rw [Rat.div_def]
      simp]
    rw [show ((0 : Rat) / 2) = 0 by
      rw [Rat.div_def]
      simp]
    rw [show ((1 : Rat) / 1) = 1 by exact ratOneDivOne]
    rw [show ((1 : Rat) / 2 + 0) = 1 / 2 by exact Rat.add_zero _]
    rw [show ((0 : Rat) + 1 / 2) = 1 / 2 by exact Rat.zero_add _]
    rw [ratOneHalfAddOneHalf]
    rw [show ((0 : Rat) + 1) = 1 by exact Rat.zero_add 1]
    rw [ratOneAddOne]
  have hright :
      ratDot unsignedU1 unsignedU1 / 2 + ratDot unsignedU2 unsignedU2 / 1 = 2 := by
    rw [hdot.1, hdot.2.1]
    rw [ratTwoDivTwo, ratOneDivOne]
    exact ratOneAddOne
  constructor
  · rw [hleft, hright]
  · exact hleft

/-- Good-ordinary full local data collapses, while omitting `x_ord` leaves residual one. -/
theorem ordinarySchurCollapse :
    let I3 : Fin 3 → Fin 3 → Int := heightKLL
    let I3dagger : Fin 3 → Fin 3 → Int := I3
    let projection := matMul (matMul I3 I3dagger) I3
    let Xi_C := matSub I3 projection
    projection = I3 ∧ Xi_C = zeroMatrix ∧ trace omitOrdXi = 1 := by
  dsimp only
  have hmul : matMul heightKLL heightKLL = (heightKLL : Fin 3 → Fin 3 → Int) :=
    heightKLLMatMul
  constructor
  · rw [hmul, hmul]
  · constructor
    · rw [hmul, hmul]
      funext i j
      simp [matSub, zeroMatrix]
    · decide

/-- Signed full local data collapses, while unsigned aggregation forgets the difference row. -/
theorem signedSchurCollapse :
    let I3 : Fin 3 → Fin 3 → Int := heightKLL
    let I3dagger : Fin 3 → Fin 3 → Int := I3
    let projection := matMul (matMul I3 I3dagger) I3
    let Xi_C := matSub I3 projection
    let unsignedProjectorTrace := traceRat unsignedProjector
    let unsignedResidualTrace : Rat := 3 - unsignedProjectorTrace
    projection = I3 ∧ Xi_C = zeroMatrix ∧ unsignedProjectorTrace = 2 ∧
      unsignedResidualTrace = 1 ∧
      unsignedProjection signedPlusWitness = unsignedProjection signedMinusWitness ∧
      signedPlusWitness ≠ signedMinusWitness := by
  dsimp only
  have hmul : matMul heightKLL heightKLL = (heightKLL : Fin 3 → Fin 3 → Int) :=
    heightKLLMatMul
  have hTrace : traceRat unsignedProjector = 2 := unsignedProjectorTrace.2
  constructor
  · rw [hmul, hmul]
  · constructor
    · rw [hmul, hmul]
      funext i j
      simp [matSub, zeroMatrix]
    · constructor
      · exact hTrace
      · constructor
        · rw [hTrace]
          exact ratThreeSubTwo
        · constructor
          · decide
          · intro h
            have h0 : signedPlusWitness 0 = signedMinusWitness 0 := congrFun h 0
            exact (by decide : ¬ signedPlusWitness 0 = signedMinusWitness 0) h0

end SixBirdsBSD.Apparatus.PAdic
