import Init.Data.Fin.Lemmas
import Init.Data.List.FinRange
import Init.Data.Rat.Lemmas

/-!
Actual finite hyperbolic pairings for the dimension-only shadow witness.
The groups are (Z/2)^2 and (Z/4)^2, represented by pairs of residues.
Their cyclic pairing targets embed as the corresponding torsion in Q/Z,
verified through rational congruence modulo integers. No elliptic-curve
realization or canonical numerical lift of an arithmetic Pfaffian is claimed.
-/
namespace SixBirdsBSD.Apparatus.FinitePairings

abbrev Plane (n : Nat) := Fin n × Fin n

instance planeForallDecidable {n : Nat} (p : Plane n → Prop) [DecidablePred p] :
    Decidable (∀ x, p x) :=
  if h : ∀ a b : Fin n, p (a, b) then
    isTrue (fun x => h x.1 x.2)
  else
    isFalse (fun hp => h (fun a b => hp (a, b)))

instance planeExistsDecidable {n : Nat} (p : Plane n → Prop) [DecidablePred p] :
    Decidable (∃ x, p x) :=
  if h : ∃ a b : Fin n, p (a, b) then
    isTrue (by obtain ⟨a, b, hab⟩ := h; exact ⟨(a, b), hab⟩)
  else
    isFalse (by rintro ⟨x, hx⟩; exact h ⟨x.1, x.2, hx⟩)

def addPlane {n : Nat} (x y : Plane n) : Plane n := (x.1 + y.1, x.2 + y.2)
def negPlane {n : Nat} (x : Plane n) : Plane n := (-x.1, -x.2)
def zeroPlane (n : Nat) [NeZero n] : Plane n := (0, 0)
def eFirst (n : Nat) [NeZero n] : Plane n := (1, 0)
def eSecond (n : Nat) [NeZero n] : Plane n := (0, 1)

/-- The actual alternating pairing, with values in the n-torsion cyclic
target; an entry k corresponds to k/n modulo integers. -/
def pairing {n : Nat} (x y : Plane n) : Fin n := x.1 * y.2 - x.2 * y.1

def AbelianGroupLaws (n : Nat) [NeZero n] : Prop :=
  (∀ x y z : Plane n, addPlane (addPlane x y) z = addPlane x (addPlane y z)) ∧
  (∀ x y : Plane n, addPlane x y = addPlane y x) ∧
  (∀ x : Plane n, addPlane (zeroPlane n) x = x) ∧
  (∀ x : Plane n, addPlane (negPlane x) x = zeroPlane n)

def AlternatingBiadditive (n : Nat) [NeZero n] : Prop :=
  (∀ x : Plane n, pairing x x = 0) ∧
  (∀ x y z : Plane n, pairing (addPlane x y) z = pairing x z + pairing y z) ∧
  (∀ x y z : Plane n, pairing x (addPlane y z) = pairing x y + pairing x z)

def Nondegenerate (n : Nat) [NeZero n] : Prop :=
  ∀ x : Plane n, (∀ y : Plane n, pairing x y = 0) → x = zeroPlane n

theorem groupLawsTwo : AbelianGroupLaws 2 := by
  unfold AbelianGroupLaws
  decide +kernel

theorem groupLawsFour : AbelianGroupLaws 4 := by
  unfold AbelianGroupLaws
  decide +kernel

theorem alternatingTwo : AlternatingBiadditive 2 := by
  unfold AlternatingBiadditive
  decide +kernel

theorem alternatingFour : AlternatingBiadditive 4 := by
  unfold AlternatingBiadditive
  decide +kernel

theorem nondegenerateTwo : Nondegenerate 2 := by
  unfold Nondegenerate
  decide +kernel

theorem nondegenerateFour : Nondegenerate 4 := by
  unfold Nondegenerate
  decide +kernel

def smulPlane (n : Nat) [NeZero n] : Nat → Plane n → Plane n
  | 0, _ => zeroPlane n
  | k + 1, x => addPlane (smulPlane n k x) x

def smulResidue (n : Nat) [NeZero n] : Nat → Fin n → Fin n
  | 0, _ => 0
  | k + 1, a => smulResidue n k a + a

/-- All additive characters, rather than a tagged dual-coordinate carrier. -/
structure AdditiveCharacter (n : Nat) [NeZero n] where
  toFun : Plane n → Fin n
  map_zero : toFun (zeroPlane n) = 0
  map_add : ∀ x y, toFun (addPlane x y) = toFun x + toFun y

theorem characterOnSmul {n : Nat} [NeZero n] (chi : AdditiveCharacter n)
    (k : Nat) (x : Plane n) :
    chi.toFun (smulPlane n k x) = smulResidue n k (chi.toFun x) := by
  induction k with
  | zero => exact chi.map_zero
  | succ k ih =>
    change chi.toFun (addPlane (smulPlane n k x) x) = _
    rw [chi.map_add, ih]
    rfl

def coordinateCharacter {n : Nat} (a x : Plane n) : Fin n :=
  a.1 * x.1 + a.2 * x.2

theorem characterCoordinatesTwo (chi : AdditiveCharacter 2) (x : Plane 2) :
    chi.toFun x = coordinateCharacter
      (chi.toFun (eFirst 2), chi.toFun (eSecond 2)) x := by
  have hdecomp : ∀ y : Plane 2,
      y = addPlane (smulPlane 2 y.1.val (eFirst 2))
        (smulPlane 2 y.2.val (eSecond 2)) := by decide +kernel
  have hsmul : ∀ a b : Fin 2, smulResidue 2 a.val b = b * a := by decide +kernel
  rw [hdecomp x, chi.map_add, characterOnSmul, characterOnSmul]
  rw [hsmul, hsmul]
  rw [← hdecomp x]
  rfl

theorem characterCoordinatesFour (chi : AdditiveCharacter 4) (x : Plane 4) :
    chi.toFun x = coordinateCharacter
      (chi.toFun (eFirst 4), chi.toFun (eSecond 4)) x := by
  have hdecomp : ∀ y : Plane 4,
      y = addPlane (smulPlane 4 y.1.val (eFirst 4))
        (smulPlane 4 y.2.val (eSecond 4)) := by decide +kernel
  have hsmul : ∀ a b : Fin 4, smulResidue 4 a.val b = b * a := by decide +kernel
  rw [hdecomp x, chi.map_add, characterOnSmul, characterOnSmul]
  rw [hsmul, hsmul]
  rw [← hdecomp x]
  rfl

/-- Perfectness is represented by existence and uniqueness for every
actual additive character. -/
def Perfect (n : Nat) [NeZero n] : Prop :=
  ∀ chi : AdditiveCharacter n, ∃ x : Plane n,
    (∀ y, pairing x y = chi.toFun y) ∧
      ∀ x', (∀ y, pairing x' y = chi.toFun y) → x' = x

theorem perfectTwo : Perfect 2 := by
  intro chi
  let a : Plane 2 := (chi.toFun (eFirst 2), chi.toFun (eSecond 2))
  let x : Plane 2 := (a.2, -a.1)
  have hrep : ∀ a y : Plane 2,
      pairing (a.2, -a.1) y = coordinateCharacter a y := by decide +kernel
  have hinj : ∀ x y : Plane 2, (∀ z, pairing x z = pairing y z) → x = y := by
    decide +kernel
  have himage : ∀ y, pairing x y = chi.toFun y := by
    intro y
    exact (hrep a y).trans (characterCoordinatesTwo chi y).symm
  exact ⟨x, himage, fun x' hx' => hinj x' x (fun y => (hx' y).trans (himage y).symm)⟩

theorem perfectFour : Perfect 4 := by
  intro chi
  let a : Plane 4 := (chi.toFun (eFirst 4), chi.toFun (eSecond 4))
  let x : Plane 4 := (a.2, -a.1)
  have hrep : ∀ a y : Plane 4,
      pairing (a.2, -a.1) y = coordinateCharacter a y := by decide +kernel
  have hinj : ∀ x y : Plane 4, (∀ z, pairing x z = pairing y z) → x = y := by
    decide +kernel
  have himage : ∀ y, pairing x y = chi.toFun y := by
    intro y
    exact (hrep a y).trans (characterCoordinatesFour chi y).symm
  exact ⟨x, himage, fun x' hx' => hinj x' x (fun y => (hx' y).trans (himage y).symm)⟩

def residueLift {n : Nat} (x : Fin n) : Rat := (x.val : Rat) / (n : Rat)

/-- Equality of rational classes modulo integers has a finite decision
procedure: the difference's reduced denominator is one. -/
def sameClass (a b : Rat) : Prop := (a - b).den = 1

instance (a b : Rat) : Decidable (sameClass a b) := inferInstanceAs (Decidable ((a - b).den = 1))

theorem sameClassIffIntegerDifference (a b : Rat) :
    sameClass a b ↔ ∃ z : Int, a - b = (z : Rat) := by
  constructor
  · intro h
    refine ⟨(a - b).num, ?_⟩
    apply Rat.ext
    · simp
    · simpa [sameClass] using h
  · rintro ⟨z, hz⟩
    unfold sameClass
    rw [hz, Rat.den_intCast]

theorem cyclicTargetTwo :
    (∀ a b : Fin 2, sameClass (residueLift (a + b)) (residueLift a + residueLift b)) ∧
    (∀ a b : Fin 2, sameClass (residueLift a) (residueLift b) ↔ a = b) := by
  decide +kernel

theorem cyclicTargetFour :
    (∀ a b : Fin 4, sameClass (residueLift (a + b)) (residueLift a + residueLift b)) ∧
    (∀ a b : Fin 4, sameClass (residueLift a) (residueLift b) ↔ a = b) := by
  decide +kernel

def elements (n : Nat) : List (Plane n) :=
  (List.finRange n).flatMap fun a => (List.finRange n).map fun b => (a, b)

def twoTorsionElements (n : Nat) [NeZero n] : List (Plane n) :=
  (elements n).filter fun x => decide (addPlane x x = zeroPlane n)

theorem enumerateTwo :
    (elements 2).Nodup ∧ (∀ x : Plane 2, x ∈ elements 2) ∧
      (elements 2).length = 4 ∧ (twoTorsionElements 2).length = 4 := by
  decide +kernel

theorem enumerateFour :
    (elements 4).Nodup ∧ (∀ x : Plane 4, x ∈ elements 4) ∧
      (elements 4).length = 16 ∧ (twoTorsionElements 4).length = 4 := by
  decide +kernel

/-- The four-element group embeds as exactly the two-torsion of the
sixteen-element group by multiplying its residue coordinates by two. -/
def torsionEmbedding (x : Plane 2) : Plane 4 :=
  (⟨2 * x.1.val, by have := x.1.isLt; omega⟩,
   ⟨2 * x.2.val, by have := x.2.isLt; omega⟩)

def torsionDecode (x : Plane 4) : Plane 2 :=
  (⟨x.1.val / 2, by have := x.1.isLt; omega⟩,
   ⟨x.2.val / 2, by have := x.2.isLt; omega⟩)

theorem twoTorsionEquivalence :
    (∀ x : Plane 2, addPlane (torsionEmbedding x) (torsionEmbedding x) = zeroPlane 4) ∧
    (∀ x : Plane 2, torsionDecode (torsionEmbedding x) = x) ∧
    (∀ x : Plane 4, addPlane x x = zeroPlane 4 → torsionEmbedding (torsionDecode x) = x) ∧
    (∀ x y : Plane 2, torsionEmbedding (addPlane x y) =
      addPlane (torsionEmbedding x) (torsionEmbedding y)) := by
  decide +kernel

def f2Scale (a : Fin 2) (x : Plane 2) : Plane 2 := (a * x.1, a * x.2)

def F2ModuleLaws : Prop :=
  (∀ a b : Fin 2, ∀ x : Plane 2,
    f2Scale (a + b) x = addPlane (f2Scale a x) (f2Scale b x)) ∧
  (∀ a : Fin 2, ∀ x y : Plane 2,
    f2Scale a (addPlane x y) = addPlane (f2Scale a x) (f2Scale a y)) ∧
  (∀ a b : Fin 2, ∀ x : Plane 2, f2Scale (a * b) x = f2Scale a (f2Scale b x)) ∧
  (∀ x : Plane 2, f2Scale 1 x = x)

theorem f2ModuleLaws : F2ModuleLaws := by
  unfold F2ModuleLaws
  decide +kernel

def f2LinearCombination (coeff : Plane 2) : Plane 2 :=
  addPlane (f2Scale coeff.1 (eFirst 2)) (f2Scale coeff.2 (eSecond 2))

/-- A basis certificate uses existence and uniqueness of actual
coefficients, not a supplied dimension number. -/
theorem f2BasisTwo :
    ∀ x : Plane 2, ∃ coeff : Plane 2,
      f2LinearCombination coeff = x ∧
        ∀ coeff', f2LinearCombination coeff' = x → coeff' = coeff := by
  decide +kernel

theorem f2BasisFourTwoTorsion :
    ∀ x : Plane 4, addPlane x x = zeroPlane 4 → ∃ coeff : Plane 2,
      torsionEmbedding (f2LinearCombination coeff) = x ∧
        ∀ coeff', torsionEmbedding (f2LinearCombination coeff') = x → coeff' = coeff := by
  decide +kernel

/-- The Pfaffian coefficient is only relative to this chosen ordered
generator pair and the chosen rational representatives. -/
def chosenBasisPfaffian (n : Nat) [NeZero n] : Rat :=
  residueLift (pairing (eFirst n) (eSecond n))

theorem chosenBasisValues : chosenBasisPfaffian 2 = 1 / 2 ∧ chosenBasisPfaffian 4 = 1 / 4 := by
  decide +kernel

/-- Basis-dependent numerical Pfaffians do not equal the BSD cardinality
factor; in these standard hyperbolic presentations its reciprocal square
does. This formula is not asserted for arbitrary presentations. -/
theorem hyperbolicCardinalityNormalization :
    1 / (chosenBasisPfaffian 2 * chosenBasisPfaffian 2) = ((elements 2).length : Rat) ∧
    1 / (chosenBasisPfaffian 4 * chosenBasisPfaffian 4) = ((elements 4).length : Rat) := by
  decide +kernel

def changeBasisFour (x : Plane 4) : Plane 4 := (3 * x.1, x.2)

/-- An actual automorphism of the underlying group changes the numerical
coefficient of the same pairing on the resulting ordered basis. -/
theorem numericalPfaffianChangesWithBasis :
    (∀ x : Plane 4, changeBasisFour (changeBasisFour x) = x) ∧
    (∀ x y : Plane 4, changeBasisFour (addPlane x y) =
      addPlane (changeBasisFour x) (changeBasisFour y)) ∧
    residueLift (pairing (changeBasisFour (eFirst 4)) (changeBasisFour (eSecond 4))) = 3 / 4 ∧
    (3 / 4 : Rat) ≠ chosenBasisPfaffian 4 ∧
    (3 / 4 : Rat).den = (chosenBasisPfaffian 4).den := by
  decide +kernel

/-- The dimension-only witness now lives on actual finite groups with
perfect alternating pairings, equal two-torsion basis size, and unequal
orders. Numerical Pfaffian normalization and curve realization remain
separate arithmetic questions. -/
theorem dimensionOnlyShadow :
    AbelianGroupLaws 2 ∧ AbelianGroupLaws 4 ∧
    AlternatingBiadditive 2 ∧ AlternatingBiadditive 4 ∧ Perfect 2 ∧ Perfect 4 ∧
    (twoTorsionElements 2).length = (twoTorsionElements 4).length ∧
    (elements 2).length ≠ (elements 4).length ∧
    chosenBasisPfaffian 2 ≠ chosenBasisPfaffian 4 := by
  exact ⟨groupLawsTwo, groupLawsFour, alternatingTwo, alternatingFour,
    perfectTwo, perfectFour, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! A complementary witness: cardinality alone also loses group information.
The direct sum of two exponent-two hyperbolic planes has the same order as
the exponent-four plane, but different two-torsion. -/

abbrev Quad := Plane 2 × Plane 2

instance quadForallDecidable (p : Quad → Prop) [DecidablePred p] :
    Decidable (∀ x, p x) :=
  if h : ∀ a b : Plane 2, p (a, b) then
    isTrue (fun x => h x.1 x.2)
  else
    isFalse (fun hp => h (fun a b => hp (a, b)))

def addQuad (x y : Quad) : Quad := (addPlane x.1 y.1, addPlane x.2 y.2)
def negQuad (x : Quad) : Quad := (negPlane x.1, negPlane x.2)
def zeroQuad : Quad := (zeroPlane 2, zeroPlane 2)
def leftInclusion (x : Plane 2) : Quad := (x, zeroPlane 2)
def rightInclusion (x : Plane 2) : Quad := (zeroPlane 2, x)
def quadPairing (x y : Quad) : Fin 2 := pairing x.1 y.1 + pairing x.2 y.2

def QuadGroupLaws : Prop :=
  (∀ x y z : Quad, addQuad (addQuad x y) z = addQuad x (addQuad y z)) ∧
  (∀ x y : Quad, addQuad x y = addQuad y x) ∧
  (∀ x : Quad, addQuad zeroQuad x = x) ∧
  (∀ x : Quad, addQuad (negQuad x) x = zeroQuad)

def QuadAlternatingBiadditive : Prop :=
  (∀ x : Quad, quadPairing x x = 0) ∧
  (∀ x y z : Quad, quadPairing (addQuad x y) z = quadPairing x z + quadPairing y z) ∧
  (∀ x y z : Quad, quadPairing x (addQuad y z) = quadPairing x y + quadPairing x z)

theorem quadGroupLaws : QuadGroupLaws := by
  unfold QuadGroupLaws
  decide +kernel

theorem quadAlternating : QuadAlternatingBiadditive := by
  unfold QuadAlternatingBiadditive
  decide +kernel

structure QuadCharacter where
  toFun : Quad → Fin 2
  map_zero : toFun zeroQuad = 0
  map_add : ∀ x y, toFun (addQuad x y) = toFun x + toFun y

def QuadPerfect : Prop :=
  ∀ chi : QuadCharacter, ∃ x : Quad,
    (∀ y, quadPairing x y = chi.toFun y) ∧
      ∀ x', (∀ y, quadPairing x' y = chi.toFun y) → x' = x

theorem quadPerfect : QuadPerfect := by
  intro chi
  let chiLeft : AdditiveCharacter 2 := {
    toFun := fun x => chi.toFun (leftInclusion x)
    map_zero := chi.map_zero
    map_add := by
      intro x y
      exact chi.map_add (leftInclusion x) (leftInclusion y) }
  let chiRight : AdditiveCharacter 2 := {
    toFun := fun x => chi.toFun (rightInclusion x)
    map_zero := chi.map_zero
    map_add := by
      intro x y
      exact chi.map_add (rightInclusion x) (rightInclusion y) }
  obtain ⟨xLeft, hLeft, _⟩ := perfectTwo chiLeft
  obtain ⟨xRight, hRight, _⟩ := perfectTwo chiRight
  have hsplit : ∀ y : Quad, addQuad (leftInclusion y.1) (rightInclusion y.2) = y := by
    decide +kernel
  have hinj : ∀ x y : Quad, (∀ z, quadPairing x z = quadPairing y z) → x = y := by
    decide +kernel
  have himage : ∀ y, quadPairing (xLeft, xRight) y = chi.toFun y := by
    intro y
    change pairing xLeft y.1 + pairing xRight y.2 = _
    rw [hLeft, hRight]
    exact (chi.map_add (leftInclusion y.1) (rightInclusion y.2)).symm.trans
      (congrArg chi.toFun (hsplit y))
  exact ⟨(xLeft, xRight), himage,
    fun x' hx' => hinj x' (xLeft, xRight) (fun y => (hx' y).trans (himage y).symm)⟩

def quadElements : List Quad :=
  (elements 2).flatMap fun a => (elements 2).map fun b => (a, b)

def quadTwoTorsionElements : List Quad :=
  quadElements.filter fun x => decide (addQuad x x = zeroQuad)

theorem enumerateQuad :
    quadElements.Nodup ∧ (∀ x : Quad, x ∈ quadElements) ∧
      quadElements.length = 16 ∧ quadTwoTorsionElements.length = 16 := by
  decide +kernel

theorem cardinalityOnlyShadow :
    AbelianGroupLaws 4 ∧ QuadGroupLaws ∧
    AlternatingBiadditive 4 ∧ QuadAlternatingBiadditive ∧ Perfect 4 ∧ QuadPerfect ∧
    (elements 4).length = quadElements.length ∧
    (twoTorsionElements 4).length ≠ quadTwoTorsionElements.length := by
  exact ⟨groupLawsFour, quadGroupLaws, alternatingFour, quadAlternating,
    perfectFour, quadPerfect, by decide +kernel, by decide +kernel⟩

/-- False-target control: the zero pairing fails the same character
representation criterion used to prove perfectness. -/
theorem zeroPairingFailsPerfectness :
    ∃ chi : AdditiveCharacter 2, ∀ _x : Plane 2,
      ¬ (∀ y : Plane 2, (0 : Fin 2) = chi.toFun y) := by
  let chi : AdditiveCharacter 2 := {
    toFun := fun x => x.1
    map_zero := rfl
    map_add := fun _ _ => rfl }
  refine ⟨chi, fun _ h => ?_⟩
  have he := h (eFirst 2)
  exact (by decide +kernel : (0 : Fin 2) ≠ 1) he

/-- Exact impossibility for every readout through the dimension-only lens,
using the actual finite-group orders rather than independent metadata. -/
theorem noOrderReadoutFromTwoTorsionCount :
    ¬ ∃ readout : Nat → Nat,
      readout (twoTorsionElements 2).length = (elements 2).length ∧
      readout (twoTorsionElements 4).length = (elements 4).length := by
  rintro ⟨readout, hTwo, hFour⟩
  have heq : (twoTorsionElements 2).length = (twoTorsionElements 4).length := by
    decide +kernel
  have hne : (elements 2).length ≠ (elements 4).length := by decide +kernel
  exact hne (hTwo.symm.trans ((congrArg readout heq).trans hFour))

/-- Conversely, no cardinality-only readout recovers two-torsion on both
actual paired groups of order sixteen. -/
theorem noTwoTorsionReadoutFromOrder :
    ¬ ∃ readout : Nat → Nat,
      readout (elements 4).length = (twoTorsionElements 4).length ∧
      readout quadElements.length = quadTwoTorsionElements.length := by
  rintro ⟨readout, hFour, hQuad⟩
  have heq : (elements 4).length = quadElements.length := by decide +kernel
  have hne : (twoTorsionElements 4).length ≠ quadTwoTorsionElements.length := by
    decide +kernel
  exact hne (hFour.symm.trans ((congrArg readout heq).trans hQuad))

end SixBirdsBSD.Apparatus.FinitePairings
