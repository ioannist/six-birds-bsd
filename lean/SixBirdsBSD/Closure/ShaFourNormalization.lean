import SixBirdsBSD.Closure.ShaDimensionPair
import SixBirdsBSD.Apparatus.FinitePresentation

/-!
The published eight-descent supplies the arithmetic stabilization input
for 1309a1. Here we prove its return to the entire two-primary subgroup,
and classify every alternating nondegenerate form on (Z/4)^2. This does
not construct the arithmetic Selmer-complex or Stark comparison maps.
-/
namespace SixBirdsBSD.Closure.ShaFourNormalization

open ShaDescent ShaDimensionPair LocalUnitSupport
open SixBirdsBSD.Apparatus.FinitePairings
open SixBirdsBSD.Apparatus.FinitePresentation

/-- Numerical prerequisites for the cited small-conductor calculation.
The local Tamagawa interpretation and optimality are external algorithms;
16 here is the analytic candidate, not an assumed arithmetic Sha order. -/
theorem millerNumericalInputs :
    1309 < 5000 ∧ discriminant curve1309a1 < 0 ∧
    discriminant curve1309a1 = -(7^6 * 11^3 * 17^2 : Int) ∧
    c4 curve1309a1 % 7 = 2 ∧ c4 curve1309a1 % 11 = 4 ∧ c4 curve1309a1 % 17 = 1 ∧
    (64 : Rat) / (2 * 1 * 2) = 16 ∧ (16 : Nat) = 2^4 ∧
    2 ∣ (2 * 1 * 2 : Nat) := by decide +kernel

def curve2045b1 : IntegralModel := ⟨1, -1, 0, -5470, -862675⟩

theorem matchedPartnerNumericalInputs :
    (c4 curve2045b1, c6 curve2045b1, discriminant curve2045b1) =
      (262569, 746532747, -312042236328125) ∧
    discriminant curve2045b1 = -(5^17 * 409 : Int) ∧
    c4 curve2045b1 % 5 = 4 ∧ c4 curve2045b1 % 409 ≠ 0 ∧
    (c4 curve2045b1)^3 % discriminant curve2045b1 ≠ 0 ∧
    2045 < 5000 ∧ discriminant curve2045b1 < 0 ∧
    (16 : Rat) / (1 * 1) = 16 ∧ (16 : Nat) = 2^4 := by decide +kernel

/-- If G[8]=G[4], every element killed by a power of two is already
killed by four. This excludes divisible tails without ambient finiteness. -/
theorem primaryCollapseToFour {G : Type} (zeroG : G) (double : G → G)
    (hzero : double zeroG = zeroG)
    (height : ∀ x, double (double (double x)) = zeroG → double (double x) = zeroG)
    (k : Nat) (x : G) (hx : doubleIterate double k x = zeroG) :
    double (double x) = zeroG := by
  induction k generalizing x with
  | zero => change x = zeroG at hx; rw [hx, hzero, hzero]
  | succ k ih =>
    apply height x
    exact ih (double x) ((iterateCommutes double k x).trans hx)

def primaryToFour {G : Type} (d : AbelianData G)
    (height : ∀ x, doubling d (doubling d (doubling d x)) = d.zero →
      doubling d (doubling d x) = d.zero) (x : Primary d) : Four d :=
  ⟨x.val, by
    obtain ⟨k, hk⟩ := x.property
    exact primaryCollapseToFour d.zero (doubling d) (doublingZero d) height k x.val hk⟩

theorem primaryFourEquivalence {G : Type} (d : AbelianData G)
    (height : ∀ x, doubling d (doubling d (doubling d x)) = d.zero →
      doubling d (doubling d x) = d.zero) :
    (∀ x : Four d, primaryToFour d height (fourToPrimary d x) = x) ∧
    (∀ x : Primary d, fourToPrimary d (primaryToFour d height x) = x) := by
  constructor <;> intro x <;> apply Subtype.ext <;> rfl

def primaryElementsFour {G : Type} (d : AbelianData G) (basis : TwoBasis d)
    (half : Two d → G) (hhalf : ∀ a, doubling d (half a) = a.val) : List (Primary d) :=
  (fourElements d basis half hhalf).map (fourToPrimary d)

theorem enumeratePrimaryFromEightStabilization {G : Type} (d : AbelianData G)
    (basis : TwoBasis d) (half : Two d → G)
    (hhalf : ∀ a, doubling d (half a) = a.val)
    (height : ∀ x, doubling d (doubling d (doubling d x)) = d.zero →
      doubling d (doubling d x) = d.zero) :
    (primaryElementsFour d basis half hhalf).Nodup ∧
    (∀ x : Primary d, x ∈ primaryElementsFour d basis half hhalf) ∧
    (primaryElementsFour d basis half hhalf).length = 16 := by
  constructor
  · apply List.pairwise_map.mpr
    apply (enumerateFourFromHalving d basis half hhalf).1.imp
    intro x y hne heq
    exact hne (fourToPrimaryInjective d x y heq)
  · constructor
    · intro x
      exact List.mem_map.mpr ⟨primaryToFour d height x,
        (enumerateFourFromHalving d basis half hhalf).2.1 _,
        (primaryFourEquivalence d height).2 x⟩
    · simpa only [primaryElementsFour, List.length_map] using
        (enumerateFourFromHalving d basis half hhalf).2.2

/-- Retaining the common Tamagawa product and torsion order as well as
the two-torsion dimension still loses the finite factor. Both orders are
derived from the respective kernel-stabilization and halving inputs. -/
theorem noFiniteFactorReadoutFromCoarseInputs {G H : Type}
    (d : AbelianData G) (e : AbelianData H) (basisG : TwoBasis d) (basisH : TwoBasis e)
    (hfour : ∀ x, doubling d (doubling d x) = d.zero → doubling d x = d.zero)
    (half : Two e → H) (hhalf : ∀ a, doubling e (half a) = a.val)
    (height : ∀ x, doubling e (doubling e (doubling e x)) = e.zero →
      doubling e (doubling e x) = e.zero) :
    ¬ ∃ readout : Nat × Nat × Nat → Nat,
      readout (1,1,2) = (collapsedPrimaryElements d basisG).length ∧
      readout (1,1,2) = (primaryElementsFour e basisH half hhalf).length := by
  have hg := (enumerateCollapsedPrimary d basisG hfour).2.2
  have hh := (enumeratePrimaryFromEightStabilization e basisH half hhalf height).2.2
  rintro ⟨readout, ha, hb⟩
  omega

/-- Unknown odd-primary factors cannot compensate for distinct two-primary
orders. This needs no computation of either odd factor. -/
theorem unequalWholeOrdersFromPrimaryLayers (a b : Nat) (ha : a % 2 = 1) :
    4 * a ≠ 16 * b := by omega

/-- Finite primary decomposition supplies odd complements arithmetically.
The unequal whole orders then follow from the derived primary counts;
an exact whole-Sha order is not a premise or a claimed output. -/
theorem noWholeFiniteFactorReadoutFromCoarseInputs {G H : Type}
    (d : AbelianData G) (e : AbelianData H) (basisG : TwoBasis d) (basisH : TwoBasis e)
    (hfour : ∀ x, doubling d (doubling d x) = d.zero → doubling d x = d.zero)
    (half : Two e → H) (hhalf : ∀ a, doubling e (half a) = a.val)
    (height : ∀ x, doubling e (doubling e (doubling e x)) = e.zero →
      doubling e (doubling e x) = e.zero)
    (a b : Nat) (ha : a % 2 = 1) :
    ¬ ∃ readout : Nat × Nat × Nat → Nat,
      readout (1,1,2) = (collapsedPrimaryElements d basisG).length * a ∧
      readout (1,1,2) = (primaryElementsFour e basisH half hhalf).length * b := by
  have hg := (enumerateCollapsedPrimary d basisG hfour).2.2
  have hh := (enumeratePrimaryFromEightStabilization e basisH half hhalf height).2.2
  rintro ⟨readout, hG, hH⟩
  have heq := hG.symm.trans hH
  rw [hg, hh] at heq
  exact unequalWholeOrdersFromPrimaryLayers a b ha heq

theorem eightStabilizationControls :
    (∀ x : Plane 4, addPlane (addPlane x x) (addPlane x x) = zeroPlane 4) ∧
    (∃ x : Plane 8,
      addPlane (addPlane (addPlane x x) (addPlane x x))
        (addPlane (addPlane x x) (addPlane x x)) = zeroPlane 8 ∧
      addPlane (addPlane x x) (addPlane x x) ≠ zeroPlane 8) := by decide +kernel

/-! Classification of forms after an additive arithmetic identification
with (Z/4)^2. The identification is an arithmetic import, not a field
asserting this classification or selecting its normalization. -/

def FormLaws (B : Plane 4 → Plane 4 → Fin 4) : Prop :=
  (∀ x, B x x = 0) ∧
  (∀ x y z, B (addPlane x y) z = B x z + B y z) ∧
  (∀ x y z, B x (addPlane y z) = B x y + B x z)

def FormNondegenerate (B : Plane 4 → Plane 4 → Fin 4) : Prop :=
  ∀ x, (∀ y, B x y = 0) → x = zeroPlane 4

theorem formZero (B : Plane 4 → Plane 4 → Fin 4) (h : FormLaws B) :
    (∀ x, B (zeroPlane 4) x = 0) ∧ (∀ x, B x (zeroPlane 4) = 0) := by
  have hz : addPlane (zeroPlane 4) (zeroPlane 4) = zeroPlane 4 := by decide +kernel
  have hc : ∀ a : Fin 4, a = a + a → a = 0 := by decide +kernel
  constructor
  · intro x
    exact hc _ (by simpa only [hz] using h.2.1 (zeroPlane 4) (zeroPlane 4) x)
  · intro x
    exact hc _ (by simpa only [hz] using h.2.2 x (zeroPlane 4) (zeroPlane 4))

def leftCharacter (B : Plane 4 → Plane 4 → Fin 4) (h : FormLaws B) (y : Plane 4) :
    AdditiveCharacter 4 := ⟨fun x => B x y, (formZero B h).1 y, fun x z => h.2.1 x z y⟩

def rightCharacter (B : Plane 4 → Plane 4 → Fin 4) (h : FormLaws B) (x : Plane 4) :
    AdditiveCharacter 4 := ⟨B x, (formZero B h).2 x, h.2.2 x⟩

theorem formMatrixCoordinates (B : Plane 4 → Plane 4 → Fin 4) (h : FormLaws B)
    (x y : Plane 4) :
    B x y =
      (B (eFirst 4) (eFirst 4) * x.1 + B (eSecond 4) (eFirst 4) * x.2) * y.1 +
      (B (eFirst 4) (eSecond 4) * x.1 + B (eSecond 4) (eSecond 4) * x.2) * y.2 := by
  have hr := characterCoordinatesFour (rightCharacter B h x) y
  have hl1 := characterCoordinatesFour (leftCharacter B h (eFirst 4)) x
  have hl2 := characterCoordinatesFour (leftCharacter B h (eSecond 4)) x
  change B x y = B x (eFirst 4) * y.1 + B x (eSecond 4) * y.2 at hr
  change B x (eFirst 4) = _ at hl1
  change B x (eSecond 4) = _ at hl2
  rw [hr, hl1, hl2]
  rfl

theorem formCoefficient (B : Plane 4 → Plane 4 → Fin 4) (h : FormLaws B) :
    ∀ x y, B x y = B (eFirst 4) (eSecond 4) * pairing x y := by
  let u := B (eFirst 4) (eSecond 4)
  let v := B (eSecond 4) (eFirst 4)
  have hsum : v + u = 0 := by
    have ht := h.1 (addPlane (eFirst 4) (eSecond 4))
    rw [formMatrixCoordinates B h, h.1, h.1] at ht
    have hm : ∀ a : Fin 4, a * 1 = a := by decide +kernel
    simpa [addPlane, eFirst, eSecond, u, v, hm] using ht
  have hv : v = -u := by
    have hc : ∀ a b : Fin 4, a + b = 0 → a = -b := by decide +kernel
    exact hc v u hsum
  have he : ∀ (a : Fin 4) (x y : Plane 4),
      (0*x.1 + (-a)*x.2)*y.1 + (a*x.1 + 0*x.2)*y.2 = a * pairing x y := by
    decide +kernel
  intro x y
  rw [formMatrixCoordinates B h, h.1, h.1]
  change (0*x.1 + v*x.2)*y.1 + (u*x.1 + 0*x.2)*y.2 = u * pairing x y
  rw [hv]
  exact he u x y

theorem nondegenerateCoefficientIsUnit (B : Plane 4 → Plane 4 → Fin 4)
    (h : FormLaws B) (hnd : FormNondegenerate B) :
    B (eFirst 4) (eSecond 4) = 1 ∨ B (eFirst 4) (eSecond 4) = 3 := by
  let u := B (eFirst 4) (eSecond 4)
  have hc : ∀ a : Fin 4, ¬ (a = 1 ∨ a = 3) → ∀ y : Plane 4,
    a * pairing (2,0) y = 0 := by decide +kernel
  by_cases hu : u = 1 ∨ u = 3
  · exact hu
  · have hz : ((2,0) : Plane 4) = zeroPlane 4 := by
      apply hnd
      intro y
      rw [formCoefficient B h]
      exact hc u hu y
    have hn : ((2,0) : Plane 4) ≠ zeroPlane 4 := by decide +kernel
    exact False.elim (hn hz)

def normalizeCoordinates (u : Fin 4) (x : Plane 4) : Plane 4 := (u*x.1, x.2)

/-- Nondegeneracy derives the needed unit. Its coordinate change is an
additive involution and repairs every such form to the actual standard
pairing. No positive scalar lift or canonical orientation is inferred. -/
theorem everyPerfectFourFormHasNormalization (B : Plane 4 → Plane 4 → Fin 4)
    (h : FormLaws B) (hnd : FormNondegenerate B) :
    let u := B (eFirst 4) (eSecond 4)
    (∀ x, normalizeCoordinates u (normalizeCoordinates u x) = x) ∧
    (∀ x y, normalizeCoordinates u (addPlane x y) =
      addPlane (normalizeCoordinates u x) (normalizeCoordinates u y)) ∧
    (∀ x y, B (normalizeCoordinates u x) (normalizeCoordinates u y) = pairing x y) := by
  dsimp only
  have hu := nondegenerateCoefficientIsUnit B h hnd
  have hc : ∀ u : Fin 4, (u = 1 ∨ u = 3) →
      (∀ x, normalizeCoordinates u (normalizeCoordinates u x) = x) ∧
      (∀ x y, normalizeCoordinates u (addPlane x y) =
        addPlane (normalizeCoordinates u x) (normalizeCoordinates u y)) ∧
      (∀ x y, u * pairing (normalizeCoordinates u x) (normalizeCoordinates u y) =
        pairing x y) := by decide +kernel
  obtain ⟨hi, ha, hp⟩ := hc _ hu
  exact ⟨hi, ha, fun x y => (formCoefficient B h _ _).trans (hp x y)⟩

/-- The actual integer presentation recovers an arbitrary perfect form
after a derived additive coordinate change. Its positive determinant is
the cokernel order, rather than a raw rational pairing coefficient. -/
theorem perfectFourFormIntegralReturn (B : Plane 4 → Plane 4 → Fin 4)
    (h : FormLaws B) (hnd : FormNondegenerate B) :
    ∃ f : Plane 4 → Plane 4,
      (∀ x, f (f x) = x) ∧
      (∀ x y, f (addPlane x y) = addPlane (f x) (f y)) ∧
      (∀ x y, sameClass (linkingLift 4 (liftPlane (f x)) (liftPlane (f y)))
        (residueLift (B x y))) ∧
      (cokernelElements 4).Nodup ∧
      (∀ q : Cokernel 4, q ∈ cokernelElements 4) ∧
      normalizedFiniteFactor 4 = (cokernelElements 4).length ∧
      normalizedFiniteFactor 4 = 16 := by
  let f := normalizeCoordinates (B (eFirst 4) (eSecond 4))
  obtain ⟨hi, ha, hp⟩ := everyPerfectFourFormHasNormalization B h hnd
  obtain ⟨hn, hc, ho⟩ := determinantReturnsCokernelOrder 4
  refine ⟨f, hi, ha, ?_, hn, hc, ho, ?_⟩
  · intro x y
    have hb := hp (f x) (f y)
    change ∀ x, f (f x) = x at hi
    change B (f (f x)) (f (f y)) = pairing (f x) (f y) at hb
    rw [hi, hi] at hb
    rw [hb]
    exact recoversPairingFour (f x) (f y)
  · exact (determinantReturnsFiniteOrder 4).1.trans enumerateFour.2.2.1

/-- Even alternating coefficients are degenerate. A nonalternating
nondegenerate form is also excluded; neither premise can be omitted from
the normalized hyperbolic return. -/
theorem formNormalizationControls :
    FormLaws pairing ∧ FormNondegenerate pairing ∧
    FormLaws (fun x y => (3 : Fin 4) * pairing x y) ∧
    FormNondegenerate (fun x y => (3 : Fin 4) * pairing x y) ∧
    FormLaws (fun x y => (2 : Fin 4) * pairing x y) ∧
    ¬ FormNondegenerate (fun x y => (2 : Fin 4) * pairing x y) ∧
    FormNondegenerate (fun x y => x.1*y.1 + x.2*y.2) ∧
    ¬ FormLaws (fun x y => x.1*y.1 + x.2*y.2) := by
  unfold FormLaws FormNondegenerate
  decide +kernel

end SixBirdsBSD.Closure.ShaFourNormalization
