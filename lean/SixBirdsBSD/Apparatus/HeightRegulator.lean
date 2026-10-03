import Init.Grind

/-!
`SixBirdsBSD.Apparatus.HeightRegulator` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § HeightRegulator.
-/

namespace SixBirdsBSD.Apparatus.HeightRegulator

universe u v

open Lean.Grind

/-- The real height-regulator map sends the height carrier to `det(h_NT)`. -/
def heightRegulatorMap {V_E Lambda_E Scalar DetTarget : Type u}
    (det : (V_E → V_E → Scalar) → DetTarget) :
    V_E × Lambda_E × (V_E → V_E → Scalar) → DetTarget
  | (_, _, heightPairing) => det heightPairing

/-- A finite sum over a lawful scalar ring. The identity-source algebra
works on the supplied real height tangent just as on integer fixtures. -/
def sumFin {R : Type v} [CommRing R] : {n : Nat} → (Fin n → R) → R
  | 0, _ => 0
  | Nat.succ n, f => sumFin (fun i : Fin n => f i.castSucc) + f (Fin.last n)

/-- Dot product for height-tangent rows. -/
def dot {R : Type v} [CommRing R] {n : Nat} (u v : Fin n → R) : R :=
  sumFin (fun i => u i * v i)

/-- Identity audit-energy matrix `K_LL = I`. -/
def heightKLL {R : Type v} [CommRing R] {n : Nat} (i j : Fin n) : R :=
  if i = j then 1 else 0

/-- Matrix-vector multiplication using `sumFin`. -/
def mulVec {R : Type v} [CommRing R] {n : Nat}
    (M : Fin n → Fin n → R) (v : Fin n → R) : Fin n → R :=
  fun i => sumFin (fun j => M i j * v j)

theorem sumFinZero {R : Type v} [CommRing R] {n : Nat} :
    sumFin (n := n) (fun _ => (0 : R)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumFin, ih, Semiring.add_zero]

theorem castSuccNeLast {n : Nat} (i : Fin n) : i.castSucc ≠ Fin.last n := by
  intro h
  have hv := congrArg Fin.val h
  simp [Fin.castSucc, Fin.last] at hv
  exact (Nat.ne_of_lt i.isLt) hv

theorem lastNeCastSucc {n : Nat} (i : Fin n) : Fin.last n ≠ i.castSucc := by
  intro h
  exact castSuccNeLast i h.symm

/-- The Kronecker-delta row sums to the selected coordinate. -/
theorem sumFinKronecker {R : Type v} [CommRing R] {n : Nat}
    (i : Fin n) (v : Fin n → R) :
    sumFin (fun j => (if i = j then (1 : R) else 0) * v j) = v i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?last ?cast i
      · have hzero :
            (fun j : Fin n =>
                (if Fin.last n = j.castSucc then (1 : R) else 0) * v j.castSucc)
              = fun _ => (0 : R) := by
          funext j
          simp [lastNeCastSucc, Semiring.zero_mul]
        simpa [sumFin, hzero, sumFinZero, Semiring.one_mul] using
          (show (0 : R) + v (Fin.last n) = v (Fin.last n) by grind)
      · intro i'
        have hlast :
            (if i'.castSucc = Fin.last n then (1 : R) else 0) * v (Fin.last n) = 0 := by
          simp [castSuccNeLast, Semiring.zero_mul]
        have hrec := ih i' (fun j => v j.castSucc)
        simp [sumFin, hlast, Fin.castSucc_inj, Semiring.add_zero] at hrec ⊢
        exact hrec

/-- The identity audit-energy matrix acts as the identity on height tangents. -/
theorem heightKLLMulVec {R : Type v} [CommRing R] {n : Nat} (v : Fin n → R) :
    mulVec heightKLL v = v := by
  funext i
  exact sumFinKronecker i v


/-- Native finite matrix multiplication for the pseudoinverse audit. -/
def heightMatrixProduct {R : Type v} [CommRing R] {n : Nat}
    (A B : Fin n → Fin n → R) : Fin n → Fin n → R :=
  fun i j => sumFin (fun k => A i k * B k j)

def heightMatrixTranspose {R : Type v} {n : Nat}
    (A : Fin n → Fin n → R) : Fin n → Fin n → R := fun i j => A j i

theorem heightKLLSymmetric {R : Type v} [CommRing R] {n : Nat}
    (i j : Fin n) : heightKLL (R := R) i j = heightKLL j i := by
  by_cases h : i=j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm h
    simp [heightKLL, h, hji]

theorem heightIdentityLeftProduct {R : Type v} [CommRing R] {n : Nat}
    (A : Fin n → Fin n → R) : heightMatrixProduct heightKLL A = A := by
  funext i j
  exact sumFinKronecker i (fun k => A k j)

theorem heightIdentityRightProduct {R : Type v} [CommRing R] {n : Nat}
    (A : Fin n → Fin n → R) : heightMatrixProduct A heightKLL = A := by
  funext i j
  change sumFin (fun k => A i k * heightKLL k j) = A i j
  have hfun : (fun k => A i k * heightKLL k j) =
      (fun k => heightKLL j k * A i k) := by
    funext k
    rw [heightKLLSymmetric k j]
    grind
  rw [hfun]
  exact sumFinKronecker j (fun k => A i k)

theorem heightIdentityTranspose {R : Type v} [CommRing R] {n : Nat} :
    heightMatrixTranspose (heightKLL : Fin n → Fin n → R) = heightKLL := by
  funext i j
  exact heightKLLSymmetric j i

/-- All four Moore-Penrose equations at the identity source. Over the real
Euclidean audit carrier, transpose is the usual adjoint. -/
def penroseAtHeightIdentity {R : Type v} [CommRing R] {n : Nat}
    (G : Fin n → Fin n → R) : Prop :=
  heightMatrixProduct (heightMatrixProduct heightKLL G) heightKLL = heightKLL ∧
  heightMatrixProduct (heightMatrixProduct G heightKLL) G = G ∧
  heightMatrixTranspose (heightMatrixProduct heightKLL G) =
    heightMatrixProduct heightKLL G ∧
  heightMatrixTranspose (heightMatrixProduct G heightKLL) =
    heightMatrixProduct G heightKLL

theorem heightIdentityPenrose {R : Type v} [CommRing R] {n : Nat} :
    penroseAtHeightIdentity (heightKLL : Fin n → Fin n → R) := by
  unfold penroseAtHeightIdentity
  simp [heightIdentityRightProduct, heightIdentityTranspose]

/-- The first Penrose equation already determines the pseudoinverse at the
identity. The calculation does not merely name I as its own pseudoinverse. -/
theorem heightIdentityPenroseUnique {R : Type v} [CommRing R] {n : Nat}
    (G : Fin n → Fin n → R) : penroseAtHeightIdentity G ↔ G = heightKLL := by
  constructor
  · intro h
    have hfirst := h.1
    rw [heightIdentityLeftProduct, heightIdentityRightProduct] at hfirst
    exact hfirst
  · intro h
    rw [h]
    exact heightIdentityPenrose

/-- The identity-source height tangent Schur residual collapses to zero. -/
theorem heightSchurCollapse {R : Type v} [CommRing R] {n : Nat}
    (d_H : Fin n → R) :
    let K_DD := dot d_H d_H
    let K_DL_KLLdagger_K_LD := dot d_H (mulVec heightKLL d_H)
    let Xi_C := K_DD - K_DL_KLLdagger_K_LD
    Xi_C = 0 ∧ K_DD = dot d_H d_H ∧ (d_H = (fun _ => 0) → K_DD = 0) := by
  have hproj : mulVec heightKLL d_H = d_H := heightKLLMulVec d_H
  dsimp
  constructor
  · rw [hproj]
    grind
  · constructor
    · rfl
    · intro hzero
      rw [hzero]
      simp [dot, sumFinZero, Semiring.zero_mul]


/-- The pre-source energy of the empty height tangent is zero. This is
separate from the rank-zero regulator convention, whose empty determinant
is one. -/
theorem heightZeroRank {R : Type v} [CommRing R] (d : Fin 0 → R) : dot d d = 0 := rfl

/-- Symmetric rank-two height data supplied by the arithmetic pairing.
The following algebra does not construct the Neron-Tate pairing. -/
structure SymmetricHeight2 (R : Type v) where
  a : R
  b : R
  c : R

def det2 {R : Type v} [CommRing R] (H : SymmetricHeight2 R) : R :=
  H.a * H.c - H.b * H.b

/-- The supplied symmetric matrix constructs a bilinear pairing on coordinates.
This is a coordinate model, not an arithmetic height-pairing construction. -/
def heightPairing2 {R : Type v} [CommRing R] (H : SymmetricHeight2 R)
    (x y : R × R) : R :=
  H.a*x.1*y.1 + H.b*(x.1*y.2+x.2*y.1) + H.c*x.2*y.2

theorem heightPairing2Symmetric {R : Type v} [CommRing R]
    (H : SymmetricHeight2 R) (x y : R × R) :
    heightPairing2 H x y = heightPairing2 H y x := by
  simp only [heightPairing2]
  grind

theorem heightPairing2Additive {R : Type v} [CommRing R]
    (H : SymmetricHeight2 R) (x y z : R × R) :
    heightPairing2 H (x.1+y.1, x.2+y.2) z =
      heightPairing2 H x z + heightPairing2 H y z := by
  simp only [heightPairing2]
  grind

theorem heightPairing2Scalar {R : Type v} [CommRing R]
    (H : SymmetricHeight2 R) (s : R) (x y : R × R) :
    heightPairing2 H (s*x.1, s*x.2) y = s*heightPairing2 H x y := by
  simp only [heightPairing2]
  grind

/-- Determinant coefficient in the fixed coordinate basis. -/
def determinantFromPairing2 {R : Type v} [CommRing R]
    (B : (R × R) → (R × R) → R) : R :=
  B (1,0) (1,0)*B (0,1) (0,1) - B (1,0) (0,1)*B (0,1) (1,0)

/-- A concrete specialization of the previously supplied determinant operation. -/
theorem heightRegulatorMapRank2 {R : Type v} [CommRing R]
    (H : SymmetricHeight2 R) (point latticeMarker : R × R) :
    heightRegulatorMap determinantFromPairing2
      (point, latticeMarker, heightPairing2 H) = det2 H := by
  simp only [heightRegulatorMap, determinantFromPairing2, heightPairing2, det2]
  grind

def heightVariation {R : Type v} [CommRing R]
    (H D : SymmetricHeight2 R) (t : R) : SymmetricHeight2 R :=
  ⟨H.a+t*D.a, H.b+t*D.b, H.c+t*D.c⟩

def mixedDetCoefficient {R : Type v} [CommRing R]
    (H D : SymmetricHeight2 R) : R :=
  H.c*D.a - 2*H.b*D.b + H.a*D.c

/-- Exact polynomial identity before any analytic differentiation. It derives
rather than supplies the first-order determinant coefficient. -/
theorem determinantVariationPolynomial {R : Type v} [CommRing R]
    (H D : SymmetricHeight2 R) (t : R) :
    det2 (heightVariation H D t) =
      det2 H + t*mixedDetCoefficient H D + t*t*det2 D := by
  simp only [det2, heightVariation, mixedDetCoefficient]
  grind

def inverse2 {R : Type v} [Field R] (H : SymmetricHeight2 R) : SymmetricHeight2 R :=
  ⟨H.c/det2 H, -H.b/det2 H, H.a/det2 H⟩

/-- The declared inverse is a genuine matrix inverse at nonsingular height
matrices. Division at zero is not silently treated as an inverse. -/
theorem inverse2Correct {R : Type v} [Field R]
    (H : SymmetricHeight2 R) (h : det2 H ≠ 0) :
    H.a*(inverse2 H).a + H.b*(inverse2 H).b = 1 ∧
    H.a*(inverse2 H).b + H.b*(inverse2 H).c = 0 ∧
    H.b*(inverse2 H).a + H.c*(inverse2 H).b = 0 ∧
    H.b*(inverse2 H).b + H.c*(inverse2 H).c = 1 := by
  unfold inverse2 det2 at *
  grind

def tangentCoordinates2 {R : Type v} (D : SymmetricHeight2 R) : Fin 3 → R :=
  fun i => if i=0 then D.a else if i=1 then D.b else D.c

/-- The normalized first-order coefficient in vech coordinates (a,b,c).
Its analytic interpretation as d(log det) requires a positive real
height determinant and ordinary real differentiation, stated in the audit. -/
def logDetRow2 {R : Type v} [Field R] (H : SymmetricHeight2 R) : Fin 3 → R :=
  fun i => if i=0 then H.c/det2 H else
    if i=1 then -(2*H.b)/det2 H else H.a/det2 H

theorem logDetRow2Correct {R : Type v} [Field R]
    (H D : SymmetricHeight2 R) (_h : det2 H ≠ 0) :
    dot (logDetRow2 H) (tangentCoordinates2 D) = mixedDetCoefficient H D/det2 H ∧
    dot (logDetRow2 H) (tangentCoordinates2 D) =
      (inverse2 H).a*D.a + (inverse2 H).b*D.b +
        (inverse2 H).b*D.b + (inverse2 H).c*D.c := by
  simp [dot, sumFin, logDetRow2, tangentCoordinates2, inverse2, mixedDetCoefficient]
  grind

/-- Return the derived normalized determinant row to the generic Schur
calculation. No arithmetic closure or vanishing certificate is introduced. -/
theorem heightDifferentialSchurCollapse {R : Type v} [Field R]
    (H : SymmetricHeight2 R) (_h : det2 H ≠ 0) :
    dot (logDetRow2 H) (logDetRow2 H) -
      dot (logDetRow2 H) (mulVec heightKLL (logDetRow2 H)) = 0 :=
  (heightSchurCollapse (logDetRow2 H)).1

/-- Congruence of the supplied height matrix by a two-column basis change. -/
def heightBasisChange {R : Type v} [CommRing R]
    (H : SymmetricHeight2 R) (u v w z : R) : SymmetricHeight2 R :=
  ⟨H.a*u*u + 2*H.b*u*w + H.c*w*w,
    H.a*u*v + H.b*(u*z+v*w) + H.c*w*z,
    H.a*v*v + 2*H.b*v*z + H.c*z*z⟩

/-- The congruence entries come from evaluating the same pairing on the new
basis columns. Thus the coefficient transformation has a pairing-level bridge. -/
theorem heightBasisChangeFromPairing {R : Type v} [CommRing R]
    (H : SymmetricHeight2 R) (u v w z : R) :
    (heightBasisChange H u v w z).a = heightPairing2 H (u,w) (u,w) ∧
    (heightBasisChange H u v w z).b = heightPairing2 H (u,w) (v,z) ∧
    (heightBasisChange H u v w z).c = heightPairing2 H (v,z) (v,z) := by
  simp only [heightBasisChange, heightPairing2]
  grind

theorem determinantBasisChange {R : Type v} [CommRing R]
    (H : SymmetricHeight2 R) (u v w z : R) :
    det2 (heightBasisChange H u v w z) = (u*z-v*w)^2 * det2 H := by
  simp only [det2, heightBasisChange]
  grind

/-- An integral unimodular change specializes to this determinant one or negative one
condition in the scalar ring. Its regulator coefficient is invariant. -/
theorem unimodularRegulatorInvariant {R : Type v} [CommRing R]
    (H : SymmetricHeight2 R) (u v w z : R)
    (h : u*z-v*w = 1 ∨ u*z-v*w = -1) :
    det2 (heightBasisChange H u v w z) = det2 H := by
  rw [determinantBasisChange]
  rcases h with h | h <;> rw [h] <;> grind

end SixBirdsBSD.Apparatus.HeightRegulator
