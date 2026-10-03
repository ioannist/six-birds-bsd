import SixBirdsBSD.Closure.CTDerivedTransport

/-!
Rank-two Pfaffian root-line calculations for the constructed paired complex.
These are integral and rational coordinate identities. The arithmetic
application over Z_3, and descent between paired presentations, are written
in formalization/ct_pfaffian_root_construction.md. No manuscript native
generator, target-height or final sign certificate is populated here.
-/
namespace SixBirdsBSD.Closure.CTPfaffianRoot

open CTDerivedTransport

def pairingIdentification (u : Int) : Matrix2 := ((u,0),(0,u))
def skewDifferential (u : Int) : Matrix2 := ((0,3*u),(-3*u,0))
def pfaffian (m : Matrix2) : Int := m.1.2

theorem pairedSkewPresentation (u : Int) :
    compose (pairingIdentification u) differential = skewDifferential u ∧
    determinant (pairingIdentification u) = u*u ∧
    pfaffian (skewDifferential u) = 3*u ∧
    determinant (skewDifferential u) = 9*(u*u) := by
  constructor
  · apply Prod.ext <;> apply Prod.ext <;>
      simp [compose, pairingIdentification, differential, skewDifferential] <;> omega
  · simp [determinant, pairingIdentification, pfaffian, skewDifferential]
    grind

/-- Quadratic coordinate of the induced K tensor K to inverse determinant map. -/
def squareToDeterminant (u r : Rat) : Rat := (u*r)*(u*r)

/-- The Pfaffian acyclic trivialization of the actual root line. -/
def pfaffianReadout (u r : Rat) : Rat := 3*(u*r)

def rawPfaffianReadout (u r : Rat) : Rat := -(pfaffianReadout u r)

theorem rootTrivializationsCommute (u r : Rat) :
    pfaffianReadout u r * pfaffianReadout u r =
      9 * squareToDeterminant u r := by
  simp only [pfaffianReadout, squareToDeterminant]
  grind

/-- The root is constructed from the pairing coefficient before its return. -/
theorem canonicalRootReturn (u : Rat) (hu : u ≠ 0) :
    squareToDeterminant u u⁻¹ = 1 ∧ pfaffianReadout u u⁻¹ = 3 := by
  simp [squareToDeterminant, pfaffianReadout, Rat.mul_inv_cancel u hu]

theorem rootNegationKeepsDeterminant (u r : Rat) :
    squareToDeterminant u (-r) = squareToDeterminant u r := by
  simp only [squareToDeterminant, Rat.mul_neg, Rat.neg_mul]
  grind

/-- Negating the raw pairing reverses the root trivialization. The matching
source orientation reversal gives the same positive scalar return. -/
theorem rawCorrectedRootSigns (u : Rat) (hu : u ≠ 0) :
    squareToDeterminant u (-u⁻¹) = 1 ∧
    rawPfaffianReadout u (-u⁻¹) = 3 ∧
    rawPfaffianReadout u u⁻¹ = -3 := by
  have hroot := canonicalRootReturn u hu
  constructor
  · rw [rootNegationKeepsDeterminant]
    exact hroot.1
  · simp [rawPfaffianReadout, pfaffianReadout, Rat.mul_neg,
      Rat.mul_inv_cancel u hu]
    decide +kernel

/-- The frame's own Pfaffian changes while the normalized root return agrees. -/
theorem actualCoefficientFrameControls :
    pfaffian (skewDifferential 1) = 3 ∧
    pfaffian (skewDifferential 2) = 6 ∧
    squareToDeterminant 2 (1/2) = 1 ∧
    squareToDeterminant 2 1 = 4 ∧
    pfaffianReadout 2 (1/2) = 3 ∧
    pfaffianReadout 2 1 = 6 ∧
    rawPfaffianReadout 2 (-(1/2)) = 3 := by decide +kernel

end SixBirdsBSD.Closure.CTPfaffianRoot
