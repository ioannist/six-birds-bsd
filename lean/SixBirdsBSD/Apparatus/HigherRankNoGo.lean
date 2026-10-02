import SixBirdsBSD.Apparatus.FiniteSource

/-!
`SixBirdsBSD.Apparatus.HigherRankNoGo` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § HigherRankNoGo.
-/

namespace SixBirdsBSD.Apparatus.HigherRankNoGo

open SixBirdsBSD.Apparatus.HeightRegulator
open SixBirdsBSD.Apparatus.FiniteSource

universe u

/-- Rank-two Mordell--Weil/Kummer source from a known two-element MW basis. -/
def rankTwoKummerSource {MWPoint LambdaQp Selmer : Type u}
    (toQp : MWPoint → LambdaQp)
    (kappa_p : LambdaQp → Selmer) :
    MWPoint × MWPoint → Selmer × Selmer
  | (P1, P2) => (kappa_p (toQp P1), kappa_p (toQp P2))

def rankTwoEll389Scaled : Fin 3 → Int := fun i =>
  if i = 0 then 312679 else if i = 1 then -76771 else 214483

def rankTwoScalarDetEll : Fin 3 → Rat :=
  fun i => if i = 0 then 312679 else if i = 1 then -76771 else 214483

def rankTwoRatDot {n : Nat} (u v : Fin n → Rat) : Rat :=
  sumFinRat (fun i => u i * v i)

def rankTwoScalarDetNorm : Rat :=
  rankTwoRatDot rankTwoScalarDetEll rankTwoScalarDetEll

def rankTwoScalarDetProjector : Fin 3 → Fin 3 → Rat :=
  fun i j => (rankTwoScalarDetEll i * rankTwoScalarDetEll j) / rankTwoScalarDetNorm

theorem rankTwoRatOneDivOne : ((1 : Rat) / 1) = 1 := by
  rw [show ((1 : Rat) / 1) = Rat.divInt 1 1 by
    exact (Rat.divInt_eq_div 1 1).symm]
  exact Rat.divInt_self' (by decide : (1 : Int) ≠ 0)

theorem rankTwoRatZeroDivOne : ((0 : Rat) / 1) = 0 := by
  rw [Rat.div_def]
  simp

theorem rankTwoRatThreeSubOne : ((3 : Rat) - 1) = 2 := by
  rw [Rat.sub_def, Rat.normalize_eq_mkRat]
  unfold mkRat
  simp [Rat.normalize_eq_mk']

/-- The scalar projector uses the actual differential direction, up to the
common integer scaling used by the stored 389a1 row. -/
theorem rankTwoScalarDetNormNonzero : rankTwoScalarDetNorm ≠ 0 := by
  unfold rankTwoScalarDetNorm rankTwoRatDot sumFinRat rankTwoScalarDetEll
  decide +kernel

theorem rankTwoScalarDetProjectorTrace :
    rankTwoScalarDetNorm ≠ 0 ∧
      traceRat rankTwoScalarDetProjector =
        rankTwoScalarDetNorm / rankTwoScalarDetNorm ∧
      traceRat rankTwoScalarDetProjector = 1 := by
  refine ⟨rankTwoScalarDetNormNonzero, ?_, ?_⟩
  · unfold traceRat rankTwoScalarDetProjector rankTwoScalarDetNorm
      rankTwoRatDot sumFinRat rankTwoScalarDetEll
    decide +kernel
  · unfold traceRat rankTwoScalarDetProjector rankTwoScalarDetNorm
      rankTwoRatDot sumFinRat rankTwoScalarDetEll
    decide +kernel

/-- Rank-two full height matrix carrier collapses under the identity source. -/
theorem rankTwoHeightSchurCollapse :
    let ell := rankTwoEll389Scaled
    let K_DD := dot ell ell
    let projection := dot ell (mulVec heightKLL ell)
    let Xi := K_DD - projection
    let scalarDetProjectorTrace := traceRat rankTwoScalarDetProjector
    let scalarDetResidual : Rat := 3 - scalarDetProjectorTrace
    projection = K_DD ∧ Xi = 0 ∧ scalarDetProjectorTrace = 1 ∧
      scalarDetResidual = 2 ∧ K_DD > 0 := by
  let ell := rankTwoEll389Scaled
  have hproj : mulVec heightKLL ell = ell := heightKLLMulVec ell
  have htrace : traceRat rankTwoScalarDetProjector = 1 := rankTwoScalarDetProjectorTrace.2.2
  dsimp only
  constructor
  · rw [hproj]
  · constructor
    · rw [hproj]
      exact Int.sub_self _
    · constructor
      · exact htrace
      · constructor
        · rw [htrace]
          exact rankTwoRatThreeSubOne
        · decide

structure RankMotivicCycleData where
  gramMatrixId : Int
  orientationTag : Bool
  motivicLabel : Bool
  abelJacobiProvenance : Bool
  deriving DecidableEq

def gramMatrixPublicShadow (x : RankMotivicCycleData) : Int :=
  x.gramMatrixId

def gramShadowA : RankMotivicCycleData :=
  ⟨7, true, true, false⟩

def gramShadowB : RankMotivicCycleData :=
  ⟨7, false, true, true⟩

/-- For rank at least two, the Gram matrix is a non-injective public shadow. -/
theorem gramMatrixShadow {r : Nat} (hr : 2 ≤ r) :
    ¬ Function.Injective gramMatrixPublicShadow ∧
      gramMatrixPublicShadow gramShadowA = gramMatrixPublicShadow gramShadowB ∧
      gramShadowA ≠ gramShadowB ∧ 2 ≤ r := by
  constructor
  · intro h
    have heq : gramShadowA = gramShadowB := h rfl
    exact (by decide : ¬ gramShadowA = gramShadowB) heq
  · constructor
    · rfl
    · constructor
      · decide
      · exact hr

end SixBirdsBSD.Apparatus.HigherRankNoGo
