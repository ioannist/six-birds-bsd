/-!
`SixBirdsBSD.Apparatus.HeightRegulator` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § HeightRegulator.
-/

namespace SixBirdsBSD.Apparatus.HeightRegulator

universe u

/-- The real height-regulator map sends the height carrier to `det(h_NT)`. -/
def heightRegulatorMap {V_E Lambda_E Scalar DetTarget : Type u}
    (det : (V_E → V_E → Scalar) → DetTarget) :
    V_E × Lambda_E × (V_E → V_E → Scalar) → DetTarget
  | (_, _, heightPairing) => det heightPairing

/-- A mathlib-free finite sum over `Fin n`. -/
def sumFin : {n : Nat} → (Fin n → Int) → Int
  | 0, _ => 0
  | Nat.succ n, f => sumFin (fun i : Fin n => f i.castSucc) + f (Fin.last n)

/-- Dot product for height-tangent rows. -/
def dot {n : Nat} (u v : Fin n → Int) : Int :=
  sumFin (fun i => u i * v i)

/-- Identity audit-energy matrix `K_LL = I`. -/
def heightKLL {n : Nat} (i j : Fin n) : Int :=
  if i = j then 1 else 0

/-- Matrix-vector multiplication using `sumFin`. -/
def mulVec {n : Nat} (M : Fin n → Fin n → Int) (v : Fin n → Int) : Fin n → Int :=
  fun i => sumFin (fun j => M i j * v j)

theorem sumFinZero {n : Nat} : sumFin (n := n) (fun _ => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumFin, ih]

theorem castSuccNeLast {n : Nat} (i : Fin n) : i.castSucc ≠ Fin.last n := by
  intro h
  have hv := congrArg Fin.val h
  simp [Fin.castSucc, Fin.last] at hv
  exact (Nat.ne_of_lt i.isLt) hv

theorem lastNeCastSucc {n : Nat} (i : Fin n) : Fin.last n ≠ i.castSucc := by
  intro h
  exact castSuccNeLast i h.symm

/-- The Kronecker-delta row sums to the selected coordinate. -/
theorem sumFinKronecker {n : Nat} (i : Fin n) (v : Fin n → Int) :
    sumFin (fun j => (if i = j then (1 : Int) else 0) * v j) = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?last ?cast i
      · have hzero :
            (fun j : Fin n =>
                (if Fin.last n = j.castSucc then (1 : Int) else 0) * v j.castSucc)
              = fun _ => (0 : Int) := by
          funext j
          simp [lastNeCastSucc]
        simp [sumFin, hzero, sumFinZero]
      · intro i'
        have hlast :
            (if i'.castSucc = Fin.last n then (1 : Int) else 0) * v (Fin.last n) = 0 := by
          simp [castSuccNeLast]
        have hrec := ih i' (fun j => v j.castSucc)
        simp [sumFin, hlast, Fin.castSucc_inj] at hrec ⊢
        exact hrec

/-- The identity audit-energy matrix acts as the identity on height tangents. -/
theorem heightKLLMulVec {n : Nat} (v : Fin n → Int) :
    mulVec heightKLL v = v := by
  funext i
  exact sumFinKronecker i v

/-- The identity-source height tangent Schur residual collapses to zero. -/
theorem heightSchurCollapse {n : Nat} (d_H : Fin n → Int) :
    let K_DD := dot d_H d_H
    let K_DL_KLLdagger_K_LD := dot d_H (mulVec heightKLL d_H)
    let Xi_C := K_DD - K_DL_KLLdagger_K_LD
    Xi_C = 0 ∧ K_DD = dot d_H d_H ∧ (d_H = (fun _ => 0) → K_DD = 0) := by
  have hproj : mulVec heightKLL d_H = d_H := heightKLLMulVec d_H
  dsimp
  constructor
  · rw [hproj]
    simp
  · constructor
    · rfl
    · intro hzero
      rw [hzero]
      simp [dot, sumFinZero]

end SixBirdsBSD.Apparatus.HeightRegulator
