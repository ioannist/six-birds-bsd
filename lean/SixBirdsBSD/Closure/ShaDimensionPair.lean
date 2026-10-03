import SixBirdsBSD.Closure.ShaDescent
import Init.Data.List.Pairwise
import Init.Data.List.Erase

/-!
The arithmetic comparison uses certified descent for Cremona 571a1 and
1309a1, with an external nonvanishing theorem for the latter. This module
proves the group-theoretic return from a halving section on G[2], rather
than assuming the resulting order. No arithmetic Sha type is implemented.
-/
namespace SixBirdsBSD.Closure.ShaDimensionPair

open ShaDescent SixBirdsBSD.Apparatus.FinitePairings
open LocalUnitSupport

def curve1309a1 : IntegralModel := ⟨0, 0, 1, -406957, -99924251⟩

theorem partnerInvariants :
    (c4 curve1309a1, c6 curve1309a1, discriminant curve1309a1) =
      (19533936, 86334552648, -45254746691) ∧
    discriminant curve1309a1 ≠ 0 ∧ (64 : Rat) ≠ 0 ∧
    (c4 curve1309a1)^3 % (discriminant curve1309a1) ≠ 0 := by
  decide +kernel

/-- Ordinary abelian-group operations and laws. Doubling is derived from
addition; no cardinality or arithmetic conclusion is a field. -/
structure AbelianData (G : Type) where
  zero : G
  add : G → G → G
  neg : G → G
  assoc : ∀ x y z, add (add x y) z = add x (add y z)
  comm : ∀ x y, add x y = add y x
  zeroAdd : ∀ x, add zero x = x
  negAdd : ∀ x, add (neg x) x = zero

def doubling {G : Type} (d : AbelianData G) (x : G) : G := d.add x x
def difference {G : Type} (d : AbelianData G) (x y : G) : G := d.add x (d.neg y)
abbrev Two {G : Type} (d : AbelianData G) := KernelTwo d.zero (doubling d)
abbrev Four {G : Type} (d : AbelianData G) :=
  {x : G // doubling d (doubling d x) = d.zero}
abbrev Primary {G : Type} (d : AbelianData G) := TwoPrimary d.zero (doubling d)

theorem addZero {G : Type} (d : AbelianData G) (x : G) : d.add x d.zero = x := by
  rw [d.comm, d.zeroAdd]

theorem addNeg {G : Type} (d : AbelianData G) (x : G) : d.add x (d.neg x) = d.zero := by
  rw [d.comm, d.negAdd]

theorem addDifference {G : Type} (d : AbelianData G) (x y : G) :
    d.add y (difference d x y) = x := by
  unfold difference
  rw [← d.assoc, d.comm y x, d.assoc, addNeg, addZero]

theorem differenceAdd {G : Type} (d : AbelianData G) (x y : G) :
    difference d (d.add x y) x = y := by
  unfold difference
  rw [d.comm x y, d.assoc, addNeg, addZero]

theorem inverseUnique {G : Type} (d : AbelianData G) (x y : G)
    (h : d.add x y = d.zero) : y = d.neg x := by
  have hh := congrArg (d.add (d.neg x)) h
  rw [← d.assoc, d.negAdd, d.zeroAdd, addZero] at hh
  exact hh

theorem doublingAdd {G : Type} (d : AbelianData G) (x y : G) :
    doubling d (d.add x y) = d.add (doubling d x) (doubling d y) := by
  unfold doubling
  calc
    d.add (d.add x y) (d.add x y) = d.add x (d.add y (d.add x y)) := d.assoc _ _ _
    _ = d.add x (d.add (d.add y x) y) := congrArg (d.add x) (d.assoc _ _ _).symm
    _ = d.add x (d.add (d.add x y) y) := by rw [d.comm y x]
    _ = d.add x (d.add x (d.add y y)) := by rw [d.assoc x y y]
    _ = d.add (d.add x x) (d.add y y) := (d.assoc _ _ _).symm

theorem doublingZero {G : Type} (d : AbelianData G) : doubling d d.zero = d.zero :=
  d.zeroAdd _

theorem doublingNeg {G : Type} (d : AbelianData G) (x : G) :
    doubling d (d.neg x) = d.neg (doubling d x) := by
  apply inverseUnique d
  rw [← doublingAdd, addNeg, doublingZero]

theorem doublingDifference {G : Type} (d : AbelianData G) (x y : G) :
    doubling d (difference d x y) = difference d (doubling d x) (doubling d y) := by
  simp only [difference, doublingAdd, doublingNeg]

/-- Choose one half for each two-torsion element. Existence follows from
the separate arithmetic statement 2G[4]=G[2], not from an order claim. -/
def pairToFour {G : Type} (d : AbelianData G) (half : Two d → G)
    (hhalf : ∀ a, doubling d (half a) = a.val) (ab : Two d × Two d) : Four d :=
  ⟨d.add (half ab.1) ab.2.val, by
    rw [doublingAdd, hhalf, ab.2.property, addZero]
    exact ab.1.property⟩

def fourToPair {G : Type} (d : AbelianData G) (half : Two d → G)
    (hhalf : ∀ a, doubling d (half a) = a.val) (x : Four d) : Two d × Two d :=
  let a : Two d := ⟨doubling d x.val, x.property⟩
  (a, ⟨difference d x.val (half a), by
    rw [doublingDifference, hhalf]
    exact addNeg d _⟩)

theorem halvingEquivalence {G : Type} (d : AbelianData G) (half : Two d → G)
    (hhalf : ∀ a, doubling d (half a) = a.val) :
    (∀ ab, fourToPair d half hhalf (pairToFour d half hhalf ab) = ab) ∧
    (∀ x, pairToFour d half hhalf (fourToPair d half hhalf x) = x) := by
  constructor
  · intro ab
    have ha : (fourToPair d half hhalf (pairToFour d half hhalf ab)).1 = ab.1 := by
      apply Subtype.ext
      exact (doublingAdd d _ _).trans (by rw [hhalf, ab.2.property, addZero])
    apply Prod.ext ha
    apply Subtype.ext
    change difference d (d.add (half ab.1) ab.2.val)
      (half (fourToPair d half hhalf (pairToFour d half hhalf ab)).1) = ab.2.val
    rw [ha, differenceAdd]
  · intro x
    apply Subtype.ext
    exact addDifference d _ _

/-- A two-element F2 basis supplies this underlying bijection. Only the
bijection is required here; no linearity is inferred from these fields.
The halving construction then derives sixteen four-torsion elements. -/
structure TwoBasis {G : Type} (d : AbelianData G) where
  toKernel : Plane 2 → Two d
  toPlane : Two d → Plane 2
  leftInv : ∀ a, toPlane (toKernel a) = a
  rightInv : ∀ x, toKernel (toPlane x) = x

def quadToFour {G : Type} (d : AbelianData G) (basis : TwoBasis d)
    (half : Two d → G) (hhalf : ∀ a, doubling d (half a) = a.val) (q : Quad) : Four d :=
  pairToFour d half hhalf (basis.toKernel q.1, basis.toKernel q.2)

def fourToQuad {G : Type} (d : AbelianData G) (basis : TwoBasis d)
    (half : Two d → G) (hhalf : ∀ a, doubling d (half a) = a.val) (x : Four d) : Quad :=
  let ab := fourToPair d half hhalf x
  (basis.toPlane ab.1, basis.toPlane ab.2)

theorem fourQuadEquivalence {G : Type} (d : AbelianData G) (basis : TwoBasis d)
    (half : Two d → G) (hhalf : ∀ a, doubling d (half a) = a.val) :
    (∀ q, fourToQuad d basis half hhalf (quadToFour d basis half hhalf q) = q) ∧
    (∀ x, quadToFour d basis half hhalf (fourToQuad d basis half hhalf x) = x) := by
  constructor
  · intro q
    simp only [fourToQuad, quadToFour, (halvingEquivalence d half hhalf).1,
      basis.leftInv]
  · intro x
    simp only [fourToQuad, quadToFour, basis.rightInv]
    exact (halvingEquivalence d half hhalf).2 x

def fourElements {G : Type} (d : AbelianData G) (basis : TwoBasis d)
    (half : Two d → G) (hhalf : ∀ a, doubling d (half a) = a.val) : List (Four d) :=
  quadElements.map (quadToFour d basis half hhalf)

theorem enumerateFourFromHalving {G : Type} (d : AbelianData G) (basis : TwoBasis d)
    (half : Two d → G) (hhalf : ∀ a, doubling d (half a) = a.val) :
    (fourElements d basis half hhalf).Nodup ∧
    (∀ x : Four d, x ∈ fourElements d basis half hhalf) ∧
    (fourElements d basis half hhalf).length = 16 := by
  constructor
  · apply List.pairwise_map.mpr
    apply enumerateQuad.1.imp
    intro q r hne heq
    apply hne
    have hh := congrArg (fourToQuad d basis half hhalf) heq
    simpa only [(fourQuadEquivalence d basis half hhalf).1] using hh
  · constructor
    · intro x
      exact List.mem_map.mpr ⟨fourToQuad d basis half hhalf x,
        enumerateQuad.2.1 _, (fourQuadEquivalence d basis half hhalf).2 x⟩
    · simpa only [fourElements, List.length_map] using enumerateQuad.2.2.1

def HalvableTwo {G : Type} (d : AbelianData G) : Prop :=
  ∀ a : Two d, ∃ x : G, doubling d x = a.val

noncomputable def chooseHalf {G : Type} (d : AbelianData G) (h : HalvableTwo d)
    (a : Two d) : G := Classical.choose (h a)

theorem chooseHalfCorrect {G : Type} (d : AbelianData G) (h : HalvableTwo d) :
    ∀ a, doubling d (chooseHalf d h a) = a.val :=
  fun a => Classical.choose_spec (h a)

theorem halvabilityProducesFourEnumeration {G : Type} (d : AbelianData G)
    (basis : TwoBasis d) (h : HalvableTwo d) :
    ∃ xs : List (Four d), xs.Nodup ∧ (∀ x, x ∈ xs) ∧ xs.length = 16 :=
  ⟨fourElements d basis (chooseHalf d h) (chooseHalfCorrect d h),
    enumerateFourFromHalving d basis (chooseHalf d h) (chooseHalfCorrect d h)⟩

def fourToPrimary {G : Type} (d : AbelianData G) (x : Four d) : Primary d :=
  ⟨x.val, 2, x.property⟩

theorem fourToPrimaryInjective {G : Type} (d : AbelianData G) (x y : Four d)
    (h : fourToPrimary d x = fourToPrimary d y) : x = y :=
  Subtype.ext (congrArg (fun z : Primary d => z.val) h)

/-- A duplicate-free contained list gives a lower bound even when the
ambient enumeration uses a different ordering. -/
theorem nodupSubsetLength {A : Type} (xs ys : List A) (hxs : xs.Nodup)
    (hsub : ∀ x, x ∈ xs → x ∈ ys) : xs.length ≤ ys.length := by
  classical
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨hna, hn⟩ := List.nodup_cons.mp hxs
    have ha := hsub a (by simp)
    have ht : ∀ x, x ∈ xs → x ∈ ys.erase a := by
      intro x hx
      apply (List.mem_erase_of_ne (by intro heq; exact hna (heq ▸ hx))).mpr
      exact hsub x (by simp [hx])
    have hb := ih (ys.erase a) hn ht
    have he := List.length_erase_of_mem ha
    have hy : 0 < ys.length := by cases ys <;> simp_all
    simp only [List.length_cons]
    omega

theorem primaryOrderLowerBound {G : Type} (d : AbelianData G) (basis : TwoBasis d)
    (half : Two d → G) (hhalf : ∀ a, doubling d (half a) = a.val)
    (all : List (Primary d)) (hcomplete : ∀ x, x ∈ all) : 16 ≤ all.length := by
  let witness := (fourElements d basis half hhalf).map (fourToPrimary d)
  have hn : witness.Nodup := by
    apply List.pairwise_map.mpr
    apply (enumerateFourFromHalving d basis half hhalf).1.imp
    intro x y hne heq
    exact hne (fourToPrimaryInjective d x y heq)
  have hl : witness.length = 16 := by
    simpa only [witness, List.length_map] using
      (enumerateFourFromHalving d basis half hhalf).2.2
  rw [← hl]
  exact nodupSubsetLength witness all hn (fun x _ => hcomplete x)

def collapsedPrimaryElements {G : Type} (d : AbelianData G) (basis : TwoBasis d) :
    List (Primary d) :=
  (elements 2).map (fun a => kernelToPrimary d.zero (doubling d) (basis.toKernel a))

theorem enumerateCollapsedPrimary {G : Type} (d : AbelianData G) (basis : TwoBasis d)
    (hfour : ∀ x, doubling d (doubling d x) = d.zero → doubling d x = d.zero) :
    (collapsedPrimaryElements d basis).Nodup ∧
    (∀ x : Primary d, x ∈ collapsedPrimaryElements d basis) ∧
    (collapsedPrimaryElements d basis).length = 4 := by
  constructor
  · apply List.pairwise_map.mpr
    apply enumerateTwo.1.imp
    intro a b hne heq
    apply hne
    have hv := congrArg (fun z : Primary d => z.val) heq
    have hk : basis.toKernel a = basis.toKernel b := Subtype.ext hv
    have hp := congrArg basis.toPlane hk
    simpa only [basis.leftInv] using hp
  · constructor
    · intro x
      let k := primaryToKernel d.zero (doubling d) (doublingZero d) hfour x
      refine List.mem_map.mpr ⟨basis.toPlane k, enumerateTwo.2.1 _, ?_⟩
      rw [basis.rightInv]
      exact (primaryKernelEquivalence d.zero (doubling d) (doublingZero d) hfour).2 x
    · simpa only [collapsedPrimaryElements, List.length_map] using enumerateTwo.2.2.1

/-- The order difference is derived from a collapse on one group and a
halving section on the other. It is not supplied as a certificate field. -/
theorem noPrimaryOrderReadoutFromTwoBasis {G H : Type}
    (d : AbelianData G) (e : AbelianData H) (basisG : TwoBasis d) (basisH : TwoBasis e)
    (hfour : ∀ x, doubling d (doubling d x) = d.zero → doubling d x = d.zero)
    (half : Two e → H) (hhalf : ∀ a, doubling e (half a) = a.val)
    (allH : List (Primary e)) (_hn : allH.Nodup) (hc : ∀ x, x ∈ allH) :
    ¬ ∃ readout : Nat → Nat,
      readout 2 = (collapsedPrimaryElements d basisG).length ∧
      readout 2 = allH.length := by
  have hg := (enumerateCollapsedPrimary d basisG hfour).2.2
  have hh := primaryOrderLowerBound e basisH half hhalf allH hc
  rintro ⟨readout, ha, hb⟩
  omega

def planeDataTwo : AbelianData (Plane 2) :=
  ⟨zeroPlane 2, addPlane, negPlane, groupLawsTwo.1, groupLawsTwo.2.1,
    groupLawsTwo.2.2.1, groupLawsTwo.2.2.2⟩

def planeDataFour : AbelianData (Plane 4) :=
  ⟨zeroPlane 4, addPlane, negPlane, groupLawsFour.1, groupLawsFour.2.1,
    groupLawsFour.2.2.1, groupLawsFour.2.2.2⟩

def smallLift (x : Plane 2) : Plane 4 :=
  (⟨x.1.val, by have := x.1.isLt; omega⟩, ⟨x.2.val, by have := x.2.isLt; omega⟩)

def halfCoordinates (x : Plane 4) : Plane 2 :=
  (⟨x.1.val / 2, by have := x.1.isLt; omega⟩,
   ⟨x.2.val / 2, by have := x.2.isLt; omega⟩)

theorem fourKernelCoordinateIdentities :
    (∀ a : Plane 2, halfCoordinates (doubling planeDataFour (smallLift a)) = a) ∧
    (∀ x : Plane 4, doubling planeDataFour x = planeDataFour.zero →
      doubling planeDataFour (smallLift (halfCoordinates x)) = x) ∧
    (∀ a : Plane 2, doubling planeDataFour
      (doubling planeDataFour (smallLift a)) = planeDataFour.zero) := by
  decide +kernel

def twoBasisFour : TwoBasis planeDataFour where
  toKernel := fun a => ⟨doubling planeDataFour (smallLift a),
    fourKernelCoordinateIdentities.2.2 a⟩
  toPlane := fun x => halfCoordinates x.val
  leftInv := fourKernelCoordinateIdentities.1
  rightInv := fun x => Subtype.ext (fourKernelCoordinateIdentities.2.1 x.val x.property)

def halfFour (x : Two planeDataFour) : Plane 4 := smallLift (halfCoordinates x.val)

theorem halfFourCorrect : ∀ x, doubling planeDataFour (halfFour x) = x.val :=
  fun x => fourKernelCoordinateIdentities.2.1 x.val x.property

/-- The section is inhabited on H_4 and returns an actual complete list
of sixteen elements through the generic construction. -/
theorem fourHalvingPositiveControl :
    (fourElements planeDataFour twoBasisFour halfFour halfFourCorrect).Nodup ∧
    (∀ x, x ∈ fourElements planeDataFour twoBasisFour halfFour halfFourCorrect) ∧
    (fourElements planeDataFour twoBasisFour halfFour halfFourCorrect).length = 16 :=
  enumerateFourFromHalving planeDataFour twoBasisFour halfFour halfFourCorrect

/-- H_2 has no half for a nonzero kernel element. Equal kernel dimensions
therefore do not supply the section hypothesis. -/
theorem twoHalvingFalseControl :
    ¬ ∃ half : Two planeDataTwo → Plane 2,
      ∀ a, doubling planeDataTwo (half a) = a.val := by
  rintro ⟨half, hh⟩
  let a : Two planeDataTwo := ⟨eFirst 2, by decide +kernel⟩
  have hz : ∀ x : Plane 2, doubling planeDataTwo x = planeDataTwo.zero := by
    decide +kernel
  have hn : eFirst 2 ≠ planeDataTwo.zero := by decide +kernel
  exact hn ((hh a).symm.trans (hz (half a)))

end SixBirdsBSD.Closure.ShaDimensionPair
