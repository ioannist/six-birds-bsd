import SixBirdsBSD.Apparatus.FinitePairings
import Init.Data.Int.DivMod.Lemmas
import Init.Data.List.Pairwise

/-!
An integral presentation for a hyperbolic finite group. The cokernel of
the actual map (a,b) -> (n*b,-n*a) is identified with (Z/n)^2 for every
positive n. This constructs a normalized finite determinant readout; no
identification with an elliptic-curve Selmer complex is assumed or proved.
-/
namespace SixBirdsBSD.Apparatus.FinitePresentation

open FinitePairings

abbrev IntegerPlane := Int × Int

def presentation (n : Nat) (x : IntegerPlane) : IntegerPlane :=
  ((n : Int) * x.2, -(n : Int) * x.1)

def InImage (n : Nat) (x : IntegerPlane) : Prop :=
  ∃ z : IntegerPlane, presentation n z = x

theorem imageIffDivisibility (n : Nat) (x : IntegerPlane) :
    InImage n x ↔ (n : Int) ∣ x.1 ∧ (n : Int) ∣ x.2 := by
  constructor
  · rintro ⟨⟨a,b⟩, hx⟩
    change ((n : Int) * b, -(n : Int) * a) = x at hx
    rw [← hx]
    exact ⟨⟨b, rfl⟩, ⟨-a, by grind⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨(-b, a), ?_⟩
    apply Prod.ext <;> simp only [presentation] <;> grind

def reduceResidue (n : Nat) [NeZero n] (a : Int) : Fin n :=
  ⟨(a % (n : Int)).toNat, by
    have hn : (0 : Int) < n := by have := NeZero.ne n; omega
    have := Int.emod_nonneg a (by omega : (n : Int) ≠ 0)
    have := Int.emod_lt_of_pos a hn
    omega⟩

theorem reduceResidueEqIff (n : Nat) [NeZero n] (a b : Int) :
    reduceResidue n a = reduceResidue n b ↔ (n : Int) ∣ a - b := by
  have hn : (n : Int) ≠ 0 := by have := NeZero.ne n; omega
  have ha := Int.emod_nonneg a hn
  have hb := Int.emod_nonneg b hn
  rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero]
  constructor
  · intro h
    have hv := congrArg Fin.val h
    change (a % (n : Int)).toNat = (b % (n : Int)).toNat at hv
    omega
  · intro h
    apply Fin.ext
    exact congrArg Int.toNat h

theorem reduceResidueAdd (n : Nat) [NeZero n] (a b : Int) :
    reduceResidue n (a + b) = reduceResidue n a + reduceResidue n b := by
  have hn : (n : Int) ≠ 0 := by have := NeZero.ne n; omega
  have ha := Int.emod_nonneg a hn
  have hb := Int.emod_nonneg b hn
  apply Fin.ext
  change ((a + b) % (n : Int)).toNat =
    ((a % (n : Int)).toNat + (b % (n : Int)).toNat) % n
  rw [Int.add_emod]
  rw [Int.toNat_emod (by omega) (by omega)]
  rw [Int.toNat_add ha hb]
  rfl

def reducePlane (n : Nat) [NeZero n] (x : IntegerPlane) : Plane n :=
  (reduceResidue n x.1, reduceResidue n x.2)

def liftPlane {n : Nat} (x : Plane n) : IntegerPlane := (x.1.val, x.2.val)

theorem reducePlaneAdd (n : Nat) [NeZero n] (x y : IntegerPlane) :
    reducePlane n (x.1 + y.1, x.2 + y.2) = addPlane (reducePlane n x) (reducePlane n y) := by
  apply Prod.ext <;> exact reduceResidueAdd n _ _

theorem reduceLift (n : Nat) [NeZero n] (x : Plane n) :
    reducePlane n (liftPlane x) = x := by
  apply Prod.ext <;> apply Fin.ext
  · change ((x.1.val : Int) % (n : Int)).toNat = x.1.val
    have := x.1.isLt
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    rfl
  · change ((x.2.val : Int) % (n : Int)).toNat = x.2.val
    have := x.2.isLt
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    rfl

/-- This proves that the equivalence relation used below really is the
relation of differing by the image of the integer presentation map. -/
theorem sameResidueIffDifferenceInImage (n : Nat) [NeZero n] (x y : IntegerPlane) :
    reducePlane n x = reducePlane n y ↔ InImage n (x.1 - y.1, x.2 - y.2) := by
  rw [imageIffDivisibility]
  change (reduceResidue n x.1, reduceResidue n x.2) =
    (reduceResidue n y.1, reduceResidue n y.2) ↔ _
  rw [Prod.mk.injEq, reduceResidueEqIff, reduceResidueEqIff]

def presentationSetoid (n : Nat) [NeZero n] : Setoid IntegerPlane where
  r := fun x y => reducePlane n x = reducePlane n y
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

abbrev Cokernel (n : Nat) [NeZero n] := Quotient (presentationSetoid n)

def cokernelToPlane (n : Nat) [NeZero n] : Cokernel n → Plane n :=
  Quotient.lift (reducePlane n) (fun _ _ h => h)

def planeToCokernel (n : Nat) [NeZero n] (x : Plane n) : Cokernel n :=
  Quotient.mk (presentationSetoid n) (liftPlane x)

theorem cokernelEquivalence (n : Nat) [NeZero n] :
    (∀ x : Plane n, cokernelToPlane n (planeToCokernel n x) = x) ∧
    (∀ q : Cokernel n, planeToCokernel n (cokernelToPlane n q) = q) := by
  constructor
  · exact reduceLift n
  · intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      apply Quotient.sound
      exact reduceLift n (reducePlane n x)

def cokernelAdd (n : Nat) [NeZero n] (x y : Cokernel n) : Cokernel n :=
  planeToCokernel n (addPlane (cokernelToPlane n x) (cokernelToPlane n y))

/-- The transported operation agrees with addition of quotient
representatives, rather than being an unrelated operation on the carrier. -/
theorem cokernelAddOnRepresentatives (n : Nat) [NeZero n] (x y : IntegerPlane) :
    cokernelAdd n (Quotient.mk (presentationSetoid n) x)
      (Quotient.mk (presentationSetoid n) y) =
    Quotient.mk (presentationSetoid n) (x.1 + y.1, x.2 + y.2) := by
  apply Quotient.sound
  exact (reduceLift n _).trans (reducePlaneAdd n x y).symm

theorem cokernelEquivalenceAdditive (n : Nat) [NeZero n] (x y : Cokernel n) :
    cokernelToPlane n (cokernelAdd n x y) =
      addPlane (cokernelToPlane n x) (cokernelToPlane n y) :=
  reduceLift n _

def cokernelZero (n : Nat) [NeZero n] : Cokernel n :=
  Quotient.mk (presentationSetoid n) (0, 0)

def cokernelNeg (n : Nat) [NeZero n] : Cokernel n → Cokernel n :=
  Quotient.lift (fun x : IntegerPlane => Quotient.mk (presentationSetoid n) (-x.1, -x.2))
    (by
      intro x y h
      apply Quotient.sound
      apply (sameResidueIffDifferenceInImage n _ _).mpr
      obtain ⟨z, hz⟩ := (sameResidueIffDifferenceInImage n x y).mp h
      refine ⟨(-z.1, -z.2), ?_⟩
      apply Prod.ext <;> simp only [presentation]
      · have hh := congrArg Prod.fst hz
        simp only [presentation] at hh
        grind
      · have hh := congrArg Prod.snd hz
        simp only [presentation] at hh
        grind)

def CokernelGroupLaws (n : Nat) [NeZero n] : Prop :=
  (∀ x y z : Cokernel n, cokernelAdd n (cokernelAdd n x y) z =
    cokernelAdd n x (cokernelAdd n y z)) ∧
  (∀ x y : Cokernel n, cokernelAdd n x y = cokernelAdd n y x) ∧
  (∀ x : Cokernel n, cokernelAdd n (cokernelZero n) x = x) ∧
  (∀ x : Cokernel n, cokernelAdd n (cokernelNeg n x) x = cokernelZero n)

theorem cokernelGroupLaws (n : Nat) [NeZero n] : CokernelGroupLaws n := by
  constructor
  · intro x y z
    induction x using Quotient.inductionOn with
    | _ x =>
      induction y using Quotient.inductionOn with
      | _ y =>
        induction z using Quotient.inductionOn with
        | _ z =>
          rw [cokernelAddOnRepresentatives, cokernelAddOnRepresentatives,
            cokernelAddOnRepresentatives, cokernelAddOnRepresentatives]
          congr 1 <;> apply Prod.ext <;> omega
  · constructor
    · intro x y
      induction x using Quotient.inductionOn with
      | _ x =>
        induction y using Quotient.inductionOn with
        | _ y =>
          rw [cokernelAddOnRepresentatives, cokernelAddOnRepresentatives]
          congr 1 <;> apply Prod.ext <;> omega
    · constructor
      · intro x
        induction x using Quotient.inductionOn with
        | _ x =>
          change cokernelAdd n (Quotient.mk _ (0, 0)) (Quotient.mk _ x) = _
          rw [cokernelAddOnRepresentatives]
          simp
      · intro x
        induction x using Quotient.inductionOn with
        | _ x =>
          change cokernelAdd n (Quotient.mk _ (-x.1, -x.2)) (Quotient.mk _ x) = _
          rw [cokernelAddOnRepresentatives]
          change Quotient.mk (presentationSetoid n) (-x.1 + x.1, -x.2 + x.2) =
            Quotient.mk (presentationSetoid n) (0, 0)
          congr 1 <;> apply Prod.ext <;> omega

structure IntegerMatrix2 where
  a : Int
  b : Int
  c : Int
  d : Int

def determinant (m : IntegerMatrix2) : Int := m.a * m.d - m.b * m.c

def applyMatrix (m : IntegerMatrix2) (x : IntegerPlane) : IntegerPlane :=
  (m.a * x.1 + m.b * x.2, m.c * x.1 + m.d * x.2)

def integralForm (m : IntegerMatrix2) (x y : IntegerPlane) : Int :=
  x.1 * (applyMatrix m y).1 + x.2 * (applyMatrix m y).2

def presentationMatrix (n : Nat) : IntegerMatrix2 := ⟨0, n, -(n : Int), 0⟩

def normalizedHalfOrder (n : Nat) : Nat := (presentationMatrix n).b.natAbs
def normalizedFiniteFactor (n : Nat) : Nat :=
  (determinant (presentationMatrix n)).natAbs

theorem determinantOfPresentation (n : Nat) :
    determinant (presentationMatrix n) = (n : Int) * n := by
  simp only [determinant, presentationMatrix]
  grind

theorem matrixPresentsMap (n : Nat) (x : IntegerPlane) :
    applyMatrix (presentationMatrix n) x = presentation n x := by
  simp [applyMatrix, presentationMatrix, presentation]

theorem presentationAdditive (n : Nat) (x y : IntegerPlane) :
    presentation n (x.1 + y.1, x.2 + y.2) =
      ((presentation n x).1 + (presentation n y).1,
       (presentation n x).2 + (presentation n y).2) := by
  simp only [presentation]
  grind

theorem elementsLength (n : Nat) : (elements n).length = n * n := by
  simp [elements, List.length_flatMap, List.map_const', List.sum_replicate_nat]

theorem elementsComplete (n : Nat) (x : Plane n) : x ∈ elements n := by
  apply List.mem_flatMap.mpr
  refine ⟨x.1, List.mem_finRange _, ?_⟩
  exact List.mem_map.mpr ⟨x.2, List.mem_finRange _, rfl⟩

private theorem finRangeNodup (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, List.nodup_cons]
    constructor
    · intro h
      obtain ⟨a, _, ha⟩ := List.mem_map.mp h
      have hv := congrArg Fin.val ha
      change a.val + 1 = 0 at hv
      omega
    · apply List.pairwise_map.mpr
      apply ih.imp
      intro a b hab heq
      apply hab
      apply Fin.ext
      have hv := congrArg Fin.val heq
      change a.val + 1 = b.val + 1 at hv
      omega

theorem elementsNodup (n : Nat) : (elements n).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a _
    apply List.pairwise_map.mpr
    apply (finRangeNodup n).imp
    intro u v hne heq
    exact hne (congrArg Prod.snd heq)
  · apply (finRangeNodup n).imp
    intro a b hab x hx y hy heq
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hx
    obtain ⟨v, _, hv⟩ := List.mem_map.mp hy
    rw [← hu, ← hv] at heq
    exact hab (congrArg Prod.fst heq)

/-- The finite factor is computed from the integer map, not postulated as
the desired group order. The enumeration return is proved uniformly in n. -/
theorem determinantReturnsFiniteOrder (n : Nat) :
    normalizedFiniteFactor n = (elements n).length ∧
      normalizedHalfOrder n * normalizedHalfOrder n = normalizedFiniteFactor n := by
  unfold normalizedFiniteFactor
  rw [determinantOfPresentation, elementsLength]
  simp [normalizedHalfOrder, presentationMatrix, Int.natAbs_mul]

def cokernelElements (n : Nat) [NeZero n] : List (Cokernel n) :=
  (elements n).map (planeToCokernel n)

theorem determinantReturnsCokernelOrder (n : Nat) [NeZero n] :
    (cokernelElements n).Nodup ∧ (∀ q : Cokernel n, q ∈ cokernelElements n) ∧
      normalizedFiniteFactor n = (cokernelElements n).length := by
  constructor
  · apply List.pairwise_map.mpr
    apply (elementsNodup n).imp
    intro x y hne heq
    apply hne
    have h := congrArg (cokernelToPlane n) heq
    exact ((cokernelEquivalence n).1 x).symm.trans
      (h.trans ((cokernelEquivalence n).1 y))
  · constructor
    · intro q
      exact List.mem_map.mpr ⟨cokernelToPlane n q, elementsComplete n _,
        (cokernelEquivalence n).2 q⟩
    · simpa [cokernelElements] using (determinantReturnsFiniteOrder n).1

def congruencePfaffian (n : Nat) (basis : IntegerMatrix2) : Int :=
  integralForm (presentationMatrix n) (basis.a, basis.c) (basis.b, basis.d)

/-- The Pfaffian coefficient of B^t (nJ) B transforms by det B. -/
theorem pfaffianCongruenceLaw (n : Nat) (basis : IntegerMatrix2) :
    congruencePfaffian n basis = (n : Int) * determinant basis := by
  simp only [congruencePfaffian, integralForm, applyMatrix, presentationMatrix, determinant]
  grind

theorem unimodularNormalizedFactor (n : Nat) (basis : IntegerMatrix2)
    (hunit : determinant basis = 1 ∨ determinant basis = -1) :
    (congruencePfaffian n basis).natAbs * (congruencePfaffian n basis).natAbs =
      normalizedFiniteFactor n := by
  rw [pfaffianCongruenceLaw]
  rcases hunit with h | h <;>
    simp [h, normalizedFiniteFactor, determinantOfPresentation, Int.natAbs_mul]

def rationalPresentation (n : Nat) (x : Rat × Rat) : Rat × Rat :=
  ((n : Rat) * x.2, -(n : Rat) * x.1)

def inversePresentation (n : Nat) (x : Rat × Rat) : Rat × Rat :=
  (-x.2 / (n : Rat), x.1 / (n : Rat))

private theorem castNonzero (n : Nat) [NeZero n] : (n : Rat) ≠ 0 := by
  intro h
  have hnum := congrArg Rat.num h
  have := NeZero.ne n
  simp at hnum
  omega

/-- Both inverse identities are proved on the actual rational maps. -/
theorem rationalInverse (n : Nat) [NeZero n] (x : Rat × Rat) :
    rationalPresentation n (inversePresentation n x) = x ∧
      inversePresentation n (rationalPresentation n x) = x := by
  have hcancel := Rat.mul_inv_cancel (n : Rat) (castNonzero n)
  constructor <;> apply Prod.ext <;>
    simp only [rationalPresentation, inversePresentation, Rat.div_def] <;> grind

/-- Negation fixes the inverse-matrix convention so that the linking form
on the standard generators agrees with the earlier positive hyperbolic form. -/
def linkingLift (n : Nat) (x y : IntegerPlane) : Rat :=
  -((x.1 : Rat) * (inversePresentation n (y.1, y.2)).1 +
    (x.2 : Rat) * (inversePresentation n (y.1, y.2)).2)

theorem linkingLiftFormula (n : Nat) (x y : IntegerPlane) :
    linkingLift n x y = ((x.1 * y.2 - x.2 * y.1 : Int) : Rat) / (n : Rat) := by
  simp only [linkingLift, inversePresentation, Rat.div_def,
    Rat.intCast_sub, Rat.intCast_mul]
  grind

theorem linkingChangeLeftIsInteger (n : Nat) [NeZero n] (x y z : IntegerPlane) :
    linkingLift n (x.1 + (presentation n z).1, x.2 + (presentation n z).2) y -
      linkingLift n x y = ((z.2 * y.2 + z.1 * y.1 : Int) : Rat) := by
  have hcancel := Rat.mul_inv_cancel (n : Rat) (castNonzero n)
  simp only [linkingLiftFormula, presentation, Rat.div_def,
    Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_add, Rat.intCast_neg, Rat.intCast_natCast]
  grind

theorem linkingChangeRightIsInteger (n : Nat) [NeZero n] (x y z : IntegerPlane) :
    linkingLift n x (y.1 + (presentation n z).1, y.2 + (presentation n z).2) -
      linkingLift n x y = ((-(x.1 * z.1 + x.2 * z.2) : Int) : Rat) := by
  have hcancel := Rat.mul_inv_cancel (n : Rat) (castNonzero n)
  simp only [linkingLiftFormula, presentation, Rat.div_def,
    Rat.intCast_sub, Rat.intCast_mul, Rat.intCast_add, Rat.intCast_neg, Rat.intCast_natCast]
  grind

/-- Well-definedness modulo integers is derived from the presentation,
rather than supplied as a pairing certificate. -/
theorem linkingInvariantModuloIntegers (n : Nat) [NeZero n] (x y z : IntegerPlane) :
    sameClass
      (linkingLift n (x.1 + (presentation n z).1, x.2 + (presentation n z).2) y)
      (linkingLift n x y) ∧
    sameClass
      (linkingLift n x (y.1 + (presentation n z).1, y.2 + (presentation n z).2))
      (linkingLift n x y) := by
  constructor
  · apply (sameClassIffIntegerDifference _ _).mpr
    exact ⟨z.2 * y.2 + z.1 * y.1, linkingChangeLeftIsInteger n x y z⟩
  · apply (sameClassIffIntegerDifference _ _).mpr
    exact ⟨-(x.1 * z.1 + x.2 * z.2), linkingChangeRightIsInteger n x y z⟩

theorem recoversPairingTwo : ∀ x y : Plane 2,
    sameClass (linkingLift 2 (liftPlane x) (liftPlane y)) (residueLift (pairing x y)) := by
  decide +kernel

theorem recoversPairingFour : ∀ x y : Plane 4,
    sameClass (linkingLift 4 (liftPlane x) (liftPlane y)) (residueLift (pairing x y)) := by
  decide +kernel

theorem rawInverseSignMatters :
    ¬ sameClass
      (-linkingLift 4 (liftPlane (eFirst 4)) (liftPlane (eSecond 4)))
      (residueLift (pairing (eFirst 4) (eSecond 4))) := by
  decide +kernel

def liftedBasisChangeFour : IntegerMatrix2 := ⟨3, 4, 4, 5⟩

/-- The earlier finite-group basis change has an actual unimodular
integer lift. Its negative determinant changes orientation but not the
positive determinant factor. -/
theorem finiteBasisChangeHasIntegralRepair :
    determinant liftedBasisChangeFour = -1 ∧
    (∀ x : Plane 4,
      reducePlane 4 (applyMatrix liftedBasisChangeFour (liftPlane x)) = changeBasisFour x) ∧
    congruencePfaffian 4 liftedBasisChangeFour = -4 ∧
    (congruencePfaffian 4 liftedBasisChangeFour).natAbs *
      (congruencePfaffian 4 liftedBasisChangeFour).natAbs = normalizedFiniteFactor 4 ∧
    normalizedFiniteFactor 4 = 16 := by
  decide +kernel

/-- False-target control for the nonzero-modulus hypothesis. At zero the
matrix is singular and the totalized rational inverse loses nonzero data. -/
theorem singularPresentationFailsInverse :
    rationalPresentation 0 (1, 0) = (0, 0) ∧
      inversePresentation 0 (rationalPresentation 0 (1, 0)) ≠ (1, 0) := by
  decide +kernel

theorem modulusOneIsTrivial :
    (∀ q : Cokernel 1, q = cokernelZero 1) ∧ normalizedFiniteFactor 1 = 1 := by
  constructor
  · intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      apply Quotient.sound
      apply Prod.ext <;> apply Fin.ext
      · have h1 := (reducePlane 1 x).1.isLt
        have h2 := (reducePlane 1 (0, 0)).1.isLt
        omega
      · have h1 := (reducePlane 1 x).2.isLt
        have h2 := (reducePlane 1 (0, 0)).2.isLt
        omega
  · decide +kernel

def invalidBasisChange : IntegerMatrix2 := ⟨2, 0, 0, 1⟩

/-- The unimodularity hypothesis is substantive: this integer map loses
a finite residue and changes the supposed normalized factor. -/
theorem nonunitChangeFailsNormalization :
    determinant invalidBasisChange = 2 ∧
    reducePlane 4 (applyMatrix invalidBasisChange (2, 0)) = zeroPlane 4 ∧
    reducePlane 4 (2, 0) ≠ zeroPlane 4 ∧
    (congruencePfaffian 4 invalidBasisChange).natAbs *
      (congruencePfaffian 4 invalidBasisChange).natAbs = 64 ∧
    (64 : Nat) ≠ normalizedFiniteFactor 4 := by
  decide +kernel

/-- The earlier dimension shadow now separates an independently computed
integral determinant factor, with its return to cokernel order proved above. -/
theorem noNormalizedFactorFromTwoTorsionCount :
    ¬ ∃ readout : Nat → Nat,
      readout (twoTorsionElements 2).length = normalizedFiniteFactor 2 ∧
      readout (twoTorsionElements 4).length = normalizedFiniteFactor 4 := by
  rintro ⟨readout, hTwo, hFour⟩
  apply noOrderReadoutFromTwoTorsionCount
  exact ⟨readout,
    hTwo.trans (determinantReturnsFiniteOrder 2).1,
    hFour.trans (determinantReturnsFiniteOrder 4).1⟩

end SixBirdsBSD.Apparatus.FinitePresentation
