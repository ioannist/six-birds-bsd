import SixBirdsBSD.Closure.OddPrimaryBridge
import Init.Data.Rat.Lemmas

/-!
Equation-derived good fibers of 121a1 and 121b1 on the SAME tame cover
pi^12=11. Exact quotient-polynomial arithmetic and point counts are checked
here; p-adic fields, good-reduction theory and cohomology are written imports.
The no-go retains only unfiltered Frobenius data, not descent or the curve.
-/
namespace SixBirdsBSD.Closure.AdditiveFrobeniusDescent

open LocalUnitSupport OddPrimaryBridge

/-- Coordinates in Q[pi]/(pi^12-11); no field structure is asserted here. -/
abbrev CoverCoordinates := Fin 12 → Rat

def monomial (k : Nat) (a : Rat) : CoverCoordinates :=
  fun i => if i.val = k % 12 then a * 11^(k / 12) else 0

def add (a b : CoverCoordinates) : CoverCoordinates := fun i => a i + b i
def scale (r : Rat) (a : CoverCoordinates) : CoverCoordinates := fun i => r * a i

def multiply (a b : CoverCoordinates) : CoverCoordinates := fun k =>
  (List.finRange 12).foldl (fun total i => total +
    (List.finRange 12).foldl (fun subtotal j => subtotal +
      if (i.val + j.val) % 12 = k.val then
        a i * b j * 11^((i.val + j.val) / 12) else 0) 0) 0

def shortDiscriminant (a b : CoverCoordinates) : CoverCoordinates :=
  scale (-16) (add (scale 4 (multiply (multiply a a) a))
    (scale 27 (multiply b b)))

def coverA121a1 : CoverCoordinates := monomial 4 (-131 / 48)
def coverB121a1 : CoverCoordinates := monomial 0 (-4973 / 864)
def coverA121b1 : CoverCoordinates := monomial 0 (-2 / 3)
def coverB121b1 : CoverCoordinates := monomial 6 (7 / 108)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Scaling the short equation by u=pi^2 or pi^3 gives these coefficients.
The equalities are coefficientwise polynomial computations, not supplied
good-reduction certificates. Both transformed discriminants are -1. -/
theorem commonCoverEquations :
    (∀ i, multiply (monomial 8 1) coverA121a1 i =
      monomial 0 (-(c4 curve121a1 : Rat) / 48) i) ∧
    (∀ i, multiply (monomial 12 1) coverB121a1 i =
      monomial 0 (-(c6 curve121a1 : Rat) / 864) i) ∧
    (∀ i, multiply (monomial 12 1) coverA121b1 i =
      monomial 0 (-(c4 curve121b1 : Rat) / 48) i) ∧
    (∀ i, multiply (monomial 18 1) coverB121b1 i =
      monomial 0 (-(c6 curve121b1 : Rat) / 864) i) ∧
    (∀ i, shortDiscriminant coverA121a1 coverB121a1 i = monomial 0 (-1) i) ∧
    (∀ i, shortDiscriminant coverA121b1 coverB121b1 i = monomial 0 (-1) i) := by
  decide +kernel

def goodFiber121a1 : IntegralModel := ⟨0, 0, 0, 0, 9⟩
def goodFiber121b1 : IntegralModel := ⟨0, 0, 0, 3, 0⟩

/-- Unit denominators and their residue inverses give the displayed fibers;
positive powers of pi vanish on the residue field. -/
theorem residueCoefficientChecks :
    (48*3 : Fin 11) = 1 ∧ (864*2 : Fin 11) = 1 ∧
    (-4973*2 : Fin 11) = 9 ∧ (3*4 : Fin 11) = 1 ∧
    (-2*4 : Fin 11) = 3 ∧ (108*5 : Fin 11) = 1 ∧
    discriminant goodFiber121a1 % 11 = 10 ∧
    discriminant goodFiber121b1 % 11 = 10 := by decide +kernel

def frobeniusLens (fiber : IntegralModel) : Int × Int :=
  (12 - (pointCount fiber 11 : Int), 11)

/-- Complete affine enumeration plus infinity, not a supplied trace. -/
theorem goodFiberCounts :
    pointCount goodFiber121a1 11 = 12 ∧ pointCount goodFiber121b1 11 = 12 ∧
    frobeniusLens goodFiber121a1 = (0,11) ∧
    frobeniusLens goodFiber121b1 = (0,11) := by decide +kernel

/-- No readout from the common-cover Frobenius polynomial can recover both
equation-derived component numbers. Arithmetic interpretation of these
fibers and Tate branches is external, as recorded in the construction. -/
theorem noComponentReadoutFromCoverFrobenius :
    ¬ ∃ readout : Int × Int → Nat,
      readout (frobeniusLens goodFiber121a1) = 1 ∧
      readout (frobeniusLens goodFiber121b1) = 2 := by
  rintro ⟨readout, ha, hb⟩
  rw [goodFiberCounts.2.2.1] at ha
  rw [goodFiberCounts.2.2.2] at hb
  omega

theorem jointArithmeticNumericalWitness :
    shallowTateBranch curve121a1 11 = some (2,2,1) ∧
    shallowTateBranch curve121b1 11 = some (2,3,2) ∧
    frobeniusLens goodFiber121a1 = frobeniusLens goodFiber121b1 := by
  exact ⟨numericalShallowBranches.1, numericalShallowBranches.2,
    goodFiberCounts.2.2.1.trans goodFiberCounts.2.2.2.symm⟩

/-- A boundary control: an unrelated good equation gives a different lens. -/
theorem differentFiberControl :
    discriminant (⟨0,0,0,1,1⟩ : IntegralModel) % 11 ≠ 0 ∧
    frobeniusLens ⟨0,0,0,1,1⟩ ≠ frobeniusLens goodFiber121a1 := by decide +kernel

/-- If tau(pi)=zeta*pi and u=pi^s, the good-fiber coordinates have
characters zeta^(-2s) and zeta^(-3s). Arithmetic descent is a written proof. -/
def tameWeights (s : Fin 12) : Fin 12 × Fin 12 := (-2*s, -3*s)

def weightsKilled (s : Fin 12) (n : Nat) : Prop :=
  Fin.ofNat 12 n * (tameWeights s).1 = 0 ∧
  Fin.ofNat 12 n * (tameWeights s).2 = 0

instance (s : Fin 12) (n : Nat) : Decidable (weightsKilled s n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The two actual scale exponents give orders six and four, respectively;
checking all smaller powers prevents mistaking an upper bound for the order. -/
theorem tameCharacterOrders :
    weightsKilled 2 6 ∧ (∀ n : Fin 6, n ≠ 0 → ¬ weightsKilled 2 n.val) ∧
    weightsKilled 3 4 ∧ (∀ n : Fin 4, n ≠ 0 → ¬ weightsKilled 3 n.val) := by
  decide +kernel

/-- The marked coordinate characters recover the scale exponent modulo
twelve. With discriminant valuation in 1..11 this recovers the valuation,
not only a congruence. No component-number field enters this calculation. -/
theorem markedCharacterRepairsScale : ∀ s : Fin 12,
    (tameWeights s).1 - (tameWeights s).2 = s := by decide +kernel

def iterate {V : Type} (step : V → V) : Nat → V → V
  | 0, x => x
  | n+1, x => step (iterate step n x)

/-- Equivariance transports every generalized-eigenvector equation. -/
theorem specializationIterates {V W : Type} (step : V → V) (targetStep : W → W)
    (specialize : V → W) (h : ∀ x, specialize (step x) = targetStep (specialize x))
    (n : Nat) (x : V) :
    specialize (iterate step n x) = iterate targetStep n (specialize x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterate, h, ih]

/-- On the classical U=0 line, targetStep is multiplication by -beta.
Its kernel is zero for beta nonzero over a field. The lemma checks the
generalized-eigenvector obstruction without modeling a p-adic field or
assuming the desired eta identity. -/
theorem generalizedSpecializationVanishes {V W : Type}
    (step : V → V) (targetStep : W → W) (specialize : V → W)
    (zeroV : V) (zeroW : W)
    (hequiv : ∀ x, specialize (step x) = targetStep (specialize x))
    (hzero : specialize zeroV = zeroW)
    (hkernel : ∀ y, targetStep y = zeroW → y = zeroW)
    (n : Nat) (x : V) (hx : iterate step n x = zeroV) :
    specialize x = zeroW := by
  have hiter : iterate targetStep n (specialize x) = zeroW := by
    rw [← specializationIterates step targetStep specialize hequiv, hx, hzero]
  have descend (m : Nat) : ∀ y, iterate targetStep m y = zeroW → y = zeroW := by
    induction m with
    | zero => intro y hy; exact hy
    | succ m ih =>
      intro y hy
      apply ih y
      exact hkernel _ hy
  exact descend n _ hiter

/-- With eigenvalue zero the kernel hypothesis fails, and a nonzero
classical specialization is possible. -/
theorem zeroEigenvalueControl :
    iterate (fun _ : Fin 2 => (0 : Fin 2)) 1 1 = 0 ∧
    (1 : Fin 2) ≠ 0 ∧
    ¬ (∀ y : Fin 2, (0 : Fin 2) = 0 → y = 0) := by decide +kernel

end SixBirdsBSD.Closure.AdditiveFrobeniusDescent
