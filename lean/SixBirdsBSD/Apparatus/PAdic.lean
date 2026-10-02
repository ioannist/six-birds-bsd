import SixBirdsBSD.Apparatus.FiniteSource

/-!
`SixBirdsBSD.Apparatus.PAdic` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § PAdic.
-/

namespace SixBirdsBSD.Apparatus.PAdic

open SixBirdsBSD.Apparatus.HeightRegulator
open SixBirdsBSD.Apparatus.FiniteSource

universe u

/-- A finite-lane exponential and its inverse logarithm. Applicability of
this isomorphism is an explicit input: it is not asserted for every de Rham
representation. In arithmetic the quotient is D_dR(V)/Fil⁰, and the
exponential must have image H_f and zero kernel to give this interface. -/
structure FiniteExponentialComparison (Hf DeRhamQuotient : Type u) where
  exp : DeRhamQuotient → Hf
  log : Hf → DeRhamQuotient
  log_exp : ∀ q, log (exp q) = q
  exp_log : ∀ h, exp (log h) = h

theorem finiteLogInjective {Hf DeRhamQuotient : Type u}
    (comparison : FiniteExponentialComparison Hf DeRhamQuotient) :
    Function.Injective comparison.log := by
  intro a b h
  have he := congrArg comparison.exp h
  simpa only [comparison.exp_log] using he

/-- Typed reciprocity and finite-lane orthogonality for the dual exponential.
Its target is Fil⁰ D_dR(V), not D_dR(V)/Fil⁰. Here DualQuotient and DualH1
belong to V*(1). These algebraic pairing properties must be instantiated
from local duality; they are not definitions of the desired vanishing. -/
structure DualExponentialReciprocity
    (H1 Hf FilZero DualQuotient DualH1 PairValue : Type u) where
  includeFinite : Hf → H1
  dualExp : DualQuotient → DualH1
  expStar : H1 → FilZero
  cup : H1 → DualH1 → PairValue
  deRhamPair : FilZero → DualQuotient → PairValue
  zeroPair : PairValue
  zeroFil : FilZero
  reciprocity : ∀ h q, deRhamPair (expStar h) q = cup h (dualExp q)
  finiteOrthogonal : ∀ h q, cup (includeFinite h) (dualExp q) = zeroPair
  deRhamNondegenerate : ∀ f, (∀ q, deRhamPair f q = zeroPair) → f = zeroFil

/-- The dual exponential kills the finite local condition. Therefore it
cannot be used as the finite-lane logarithm in an invertible comparison. -/
theorem dualExpKillsFinite {H1 Hf FilZero DualQuotient DualH1 PairValue : Type u}
    (comparison : DualExponentialReciprocity
      H1 Hf FilZero DualQuotient DualH1 PairValue) (h : Hf) :
    comparison.expStar (comparison.includeFinite h) = comparison.zeroFil := by
  apply comparison.deRhamNondegenerate
  intro q
  rw [comparison.reciprocity, comparison.finiteOrthogonal]

theorem dualExpFiniteNotInjective
    {H1 Hf FilZero DualQuotient DualH1 PairValue : Type u}
    (comparison : DualExponentialReciprocity
      H1 Hf FilZero DualQuotient DualH1 PairValue)
    (a b : Hf) (hab : a ≠ b) :
    ¬ Function.Injective (fun h => comparison.expStar (comparison.includeFinite h)) := by
  intro hinj
  exact hab (hinj ((dualExpKillsFinite comparison a).trans
    (dualExpKillsFinite comparison b).symm))

/-- Ordinary comparison uses a finite-lane logarithm. The signed branch has
its own supplied comparison carrier: finite-lane and signed/Iwasawa maps
are not silently identified. Determinant-line assembly remains supplied. -/
def pAdicMap {Tplus Hf DeRhamQuotient Hplus Hminus SignedComparison Target : Type u}
    (rhoOrd : Tplus → Hf → (Hf → DeRhamQuotient) → Target)
    (rhoSigned : Hplus → Hminus → SignedComparison → Target) :
    Sum (Tplus × Hf × FiniteExponentialComparison Hf DeRhamQuotient)
      (Hplus × Hminus × SignedComparison) → Target
  | Sum.inl (tplus, hf, comparison) => rhoOrd tplus hf comparison.log
  | Sum.inr (hplus, hminus, comparison) => rhoSigned hplus hminus comparison

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
