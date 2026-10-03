import SixBirdsBSD.Closure.ShaFourNormalization

/-!
Exact finite inputs for the ordinary three-primary Selmer-complex lane
of Cremona 1913b1. Arithmetic descent, Galois representations, and derived
Selmer-complex identifications are external imports described in the audit.
No Stark basis or arithmetic comparison is supplied as a record field here.
-/
namespace SixBirdsBSD.Closure.OddPrimaryBridge

open LocalUnitSupport
open SixBirdsBSD.Apparatus.FinitePairings
open SixBirdsBSD.Apparatus.FinitePresentation

def curve1913b1 : IntegralModel := ⟨1, 1, 0, -34, -135⟩

def onAffineEquation (e : IntegralModel) (p : Nat) (xy : Plane p) : Prop :=
  let x : Int := xy.1.val
  let y : Int := xy.2.val
  (y*y + e.a1*x*y + e.a3*y - x*x*x - e.a2*x*x - e.a4*x - e.a6) % (p : Int) = 0

instance (e : IntegralModel) (p : Nat) (xy : Plane p) :
    Decidable (onAffineEquation e p xy) := inferInstanceAs (Decidable (_ = (0 : Int)))

def pointCount (e : IntegralModel) (p : Nat) : Nat :=
  1 + ((elements p).filter fun xy => decide (onAffineEquation e p xy)).length

theorem equationAndLocalInputs :
    (c4 curve1913b1, c6 curve1913b1, discriminant curve1913b1) =
      (1657, 104275, -3659569) ∧
    discriminant curve1913b1 = -(1913^2 : Int) ∧
    discriminant curve1913b1 % 3 ≠ 0 ∧ discriminant curve1913b1 % 5 ≠ 0 ∧
    (c4 curve1913b1)^3 % discriminant curve1913b1 ≠ 0 ∧
    pointCount curve1913b1 3 = 2 ∧ pointCount curve1913b1 5 = 4 ∧
    ¬ (3 : Nat) ∣ (2 * 2 * 2 : Nat) ∧ 1913 < 5000 ∧
    (9 : Nat) = 3^2 := by decide +kernel

/-- Good ordinary reduction at two forces even residue-field order.
This obstruction cannot be repaired just by removing the odd-prime scope. -/
theorem ordinaryAtTwoIsAnomalous (a : Int) (ha : a % 2 = 1) :
    (3 - a) % 2 = 0 := by omega

theorem matchedPartnerHasLocalAnomaly :
    pointCount ShaFourNormalization.curve2045b1 2 = 2 ∧
    discriminant ShaFourNormalization.curve2045b1 % 2 ≠ 0 ∧
    2 ∣ pointCount ShaFourNormalization.curve2045b1 2 := by decide +kernel

theorem anomalousUnitRootControls :
    (∀ a : Fin 4, a.val % 2 = 1 → a*a-a+2 = 0 → a = 3) ∧
    (∀ x : Fin 4, (3-1)*x = 0 ↔ x = 0 ∨ x = 2) := by decide +kernel

def matrixAction (a b c d : Fin 3) (x : Plane 3) : Plane 3 :=
  (a*x.1 + b*x.2, c*x.1 + d*x.2)

def powerAction (f : Plane 3 → Plane 3) : Nat → Plane 3 → Plane 3
  | 0, x => x
  | k+1, x => f (powerAction f k x)

/-- The Frobenius polynomial at five has trace two and determinant two
modulo three. Every matrix with these invariants has exact order eight
and no invariant line, hence generates a nonsplit Cartan in GL_2(F_3).
The arithmetic Frobenius-characteristic-polynomial theorem is external. -/
theorem frobeniusCartanReturn : ∀ a b c d : Fin 3,
    a+d = 2 → a*d-b*c = 2 →
    (∀ x, powerAction (matrixAction a b c d) 8 x = x) ∧
    (∀ k : Fin 8, k ≠ 0 → ∃ x, powerAction (matrixAction a b c d) k.val x ≠ x) ∧
    (∀ s : Fin 3, ∀ x, x ≠ zeroPlane 3 →
      matrixAction a b c d x ≠ (s*x.1, s*x.2)) := by decide +kernel

/-- Identity Frobenius supplies no such subgroup: trace alone is not a
Cartan certificate, and determinant two is substantive. -/
theorem cartanFalseControl :
    (1+1 : Fin 3) = 2 ∧ (1*1-0*0 : Fin 3) ≠ 2 ∧
    (∀ x, matrixAction 1 0 0 1 x = x) := by decide +kernel

theorem threePresentationCohomology :
    (∀ x : IntegerPlane, presentation 3 x = (0,0) → x = (0,0)) ∧
    (cokernelElements 3).Nodup ∧
    (∀ q : Cokernel 3, q ∈ cokernelElements 3) ∧
    (cokernelElements 3).length = 9 ∧ normalizedHalfOrder 3 = 3 ∧
    normalizedFiniteFactor 3 = 9 := by
  refine ⟨?_, (determinantReturnsCokernelOrder 3).1,
    (determinantReturnsCokernelOrder 3).2.1, ?_, ?_, ?_⟩
  · intro x hx
    have h1 := congrArg Prod.fst hx
    have h2 := congrArg Prod.snd hx
    simp only [presentation] at h1 h2
    apply Prod.ext <;> omega
  · simpa [cokernelElements] using elementsLength 3
  · decide +kernel
  · decide +kernel

theorem threePairingLaws :
    AbelianGroupLaws 3 ∧ AlternatingBiadditive 3 ∧ Nondegenerate 3 ∧
    (∀ a b : Fin 3, sameClass (residueLift (a+b)) (residueLift a + residueLift b)) ∧
    (∀ a b : Fin 3, sameClass (residueLift a) (residueLift b) ↔ a = b) := by
  unfold AbelianGroupLaws AlternatingBiadditive Nondegenerate
  decide +kernel

theorem characterCoordinatesThree (chi : AdditiveCharacter 3) (x : Plane 3) :
    chi.toFun x = coordinateCharacter
      (chi.toFun (eFirst 3), chi.toFun (eSecond 3)) x := by
  have hdecomp : ∀ y : Plane 3,
      y = addPlane (smulPlane 3 y.1.val (eFirst 3))
        (smulPlane 3 y.2.val (eSecond 3)) := by decide +kernel
  have hsmul : ∀ a b : Fin 3, smulResidue 3 a.val b = b*a := by decide +kernel
  rw [hdecomp x, chi.map_add, characterOnSmul, characterOnSmul, hsmul, hsmul,
    ← hdecomp x]
  rfl

def FormLaws (B : Plane 3 → Plane 3 → Fin 3) : Prop :=
  (∀ x, B x x = 0) ∧
  (∀ x y z, B (addPlane x y) z = B x z + B y z) ∧
  (∀ x y z, B x (addPlane y z) = B x y + B x z)

def FormNondegenerate (B : Plane 3 → Plane 3 → Fin 3) : Prop :=
  ∀ x, (∀ y, B x y = 0) → x = zeroPlane 3

theorem formZero (B : Plane 3 → Plane 3 → Fin 3) (h : FormLaws B) :
    (∀ x, B (zeroPlane 3) x = 0) ∧ (∀ x, B x (zeroPlane 3) = 0) := by
  have hz : addPlane (zeroPlane 3) (zeroPlane 3) = zeroPlane 3 := by decide +kernel
  have hc : ∀ a : Fin 3, a = a+a → a = 0 := by decide +kernel
  constructor
  · intro x
    exact hc _ (by simpa only [hz] using h.2.1 (zeroPlane 3) (zeroPlane 3) x)
  · intro x
    exact hc _ (by simpa only [hz] using h.2.2 x (zeroPlane 3) (zeroPlane 3))

theorem formCoefficient (B : Plane 3 → Plane 3 → Fin 3) (h : FormLaws B) :
    ∀ x y, B x y = B (eFirst 3) (eSecond 3) * pairing x y := by
  let lc (y : Plane 3) : AdditiveCharacter 3 :=
    ⟨fun x => B x y, (formZero B h).1 y, fun x z => h.2.1 x z y⟩
  let rc (x : Plane 3) : AdditiveCharacter 3 :=
    ⟨B x, (formZero B h).2 x, h.2.2 x⟩
  have hm (x y : Plane 3) : B x y =
      (B (eFirst 3) (eFirst 3)*x.1 + B (eSecond 3) (eFirst 3)*x.2)*y.1 +
      (B (eFirst 3) (eSecond 3)*x.1 + B (eSecond 3) (eSecond 3)*x.2)*y.2 := by
    have hr := characterCoordinatesThree (rc x) y
    have hl1 := characterCoordinatesThree (lc (eFirst 3)) x
    have hl2 := characterCoordinatesThree (lc (eSecond 3)) x
    change B x y = B x (eFirst 3)*y.1 + B x (eSecond 3)*y.2 at hr
    change B x (eFirst 3) = _ at hl1
    change B x (eSecond 3) = _ at hl2
    rw [hr, hl1, hl2]
    rfl
  let u := B (eFirst 3) (eSecond 3)
  let v := B (eSecond 3) (eFirst 3)
  have hsum : v+u = 0 := by
    have ht := h.1 (addPlane (eFirst 3) (eSecond 3))
    rw [hm, h.1, h.1] at ht
    have hmul : ∀ a : Fin 3, a*1 = a := by decide +kernel
    simpa [addPlane, eFirst, eSecond, u, v, hmul] using ht
  have hv : v = -u := by
    have hc : ∀ a b : Fin 3, a+b = 0 → a = -b := by decide +kernel
    exact hc v u hsum
  have he : ∀ (a : Fin 3) (x y : Plane 3),
      (0*x.1 + (-a)*x.2)*y.1 + (a*x.1 + 0*x.2)*y.2 = a*pairing x y := by
    decide +kernel
  intro x y
  rw [hm, h.1, h.1]
  change (0*x.1+v*x.2)*y.1 + (u*x.1+0*x.2)*y.2 = u*pairing x y
  rw [hv]
  exact he u x y

def normalizeCoordinates (u : Fin 3) (x : Plane 3) : Plane 3 := (u*x.1,x.2)

theorem everyPerfectThreeFormHasIntegralReturn (B : Plane 3 → Plane 3 → Fin 3)
    (h : FormLaws B) (hnd : FormNondegenerate B) :
    ∃ f : Plane 3 → Plane 3,
      (∀ x, f (f x) = x) ∧
      (∀ x y, f (addPlane x y) = addPlane (f x) (f y)) ∧
      (∀ x y, sameClass (linkingLift 3 (liftPlane (f x)) (liftPlane (f y)))
        (residueLift (B x y))) ∧ normalizedFiniteFactor 3 = 9 := by
  let u := B (eFirst 3) (eSecond 3)
  have hu : u = 1 ∨ u = 2 := by
    by_cases hu : u = 1 ∨ u = 2
    · exact hu
    · have hz : u = 0 := by
        have hc : ∀ a : Fin 3, ¬ (a = 1 ∨ a = 2) → a = 0 := by decide +kernel
        exact hc u hu
      have he := hnd (eFirst 3) (by
        intro y
        rw [formCoefficient B h]
        change u*pairing (eFirst 3) y = 0
        rw [hz]
        have hc : ∀ a : Fin 3, (0 : Fin 3)*a = 0 := by decide +kernel
        exact hc _)
      exact False.elim ((by decide +kernel : eFirst 3 ≠ zeroPlane 3) he)
  let f := normalizeCoordinates u
  have hc : ∀ a : Fin 3, (a = 1 ∨ a = 2) →
      (∀ x, normalizeCoordinates a (normalizeCoordinates a x) = x) ∧
      (∀ x y, normalizeCoordinates a (addPlane x y) =
        addPlane (normalizeCoordinates a x) (normalizeCoordinates a y)) ∧
      (∀ x y, pairing (normalizeCoordinates a x) (normalizeCoordinates a y) =
        a*pairing x y) := by decide +kernel
  obtain ⟨hi, ha, hp⟩ := hc u hu
  refine ⟨f, hi, ha, ?_, by decide +kernel⟩
  intro x y
  have hr : ∀ x y : Plane 3, sameClass
      (linkingLift 3 (liftPlane x) (liftPlane y)) (residueLift (pairing x y)) := by
    decide +kernel
  rw [formCoefficient B h]
  change sameClass (linkingLift 3 (liftPlane (f x)) (liftPlane (f y)))
    (residueLift (u*pairing x y))
  rw [← hp x y]
  exact hr (f x) (f y)

/-- The two bases of the one-dimensional residue line are units one and
two, but only one is a square. A full determinant/Stark basis therefore
does not automatically lift through a squaring map at three. -/
theorem squareRootBasisObstruction :
    (∃ v : Fin 3, 2*v = 1) ∧ (¬ ∃ v : Fin 3, v*v = 2) ∧
    ((1 : Fin 3)*(1 : Fin 3) = (-1 : Fin 3)*(-1 : Fin 3)) ∧
    (1 : Fin 3) ≠ -1 := by decide +kernel

theorem fixedSquareMapMissesABasis : ∀ u : Fin 3, u ≠ 0 →
    (∃ v : Fin 3, (2*u)*v = 1) ∧ ¬ (∃ v : Fin 3, u*(v*v) = 2*u) := by
  decide +kernel

/-- At three the coefficients nine and eighteen have the same exact
valuation. Their unit coefficients have different square-root behavior.
Over Z_3 both are bases of the same ideal; that arithmetic interpretation
and the actual determinant-line binding are supplied by the written proof. -/
theorem unitErasedBasisLosesSquareClass :
    ExactValuation 3 2 9 ∧ ExactValuation 3 2 18 ∧
    ¬ ∃ readout : Nat → Bool,
      readout 2 = decide (∃ v : Fin 3, v*v = 1) ∧
      readout 2 = decide (∃ v : Fin 3, v*v = 2) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  rintro ⟨readout, ha, hb⟩
  have h1 : decide (∃ v : Fin 3, v*v = 1) = true := by decide +kernel
  have h2 : decide (∃ v : Fin 3, v*v = 2) = false := by decide +kernel
  rw [h1] at ha
  rw [h2] at hb
  exact (by decide +kernel : (true : Bool) ≠ false) (ha.symm.trans hb)

theorem retainedUnitReturnsSquareClass : ∀ u : Fin 3, u ≠ 0 →
    ((∃ v : Fin 3, v*v = u) ↔ u = 1) := by decide +kernel

end SixBirdsBSD.Closure.OddPrimaryBridge
