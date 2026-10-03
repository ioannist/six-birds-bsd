import SixBirdsBSD.Closure.RationalLocalGlobal

/-!
Bad-reduction places and prime support of rational factors are different
indices. Exact numerical witnesses use the primary models 121a1 and 121b1.
The shallow Tate branch below checks invariant/valuation inputs; its
identification with Neron component groups uses the external Tate algorithm,
and is not a mechanization of Neron models or either recognition source.
-/
namespace SixBirdsBSD.Closure.LocalUnitSupport

open SixBirdsBSD.Apparatus.SupportPrimeNoGo
open SixBirdsBSD.Closure.RationalLocalGlobal

structure IntegralModel where
  a1 : Int
  a2 : Int
  a3 : Int
  a4 : Int
  a6 : Int

def b2 (e : IntegralModel) : Int := e.a1 * e.a1 + 4 * e.a2
def b4 (e : IntegralModel) : Int := e.a1 * e.a3 + 2 * e.a4
def b6 (e : IntegralModel) : Int := e.a3 * e.a3 + 4 * e.a6
def b8 (e : IntegralModel) : Int :=
  e.a1 * e.a1 * e.a6 + 4 * e.a2 * e.a6 - e.a1 * e.a3 * e.a4 +
    e.a2 * e.a3 * e.a3 - e.a4 * e.a4
def c4 (e : IntegralModel) : Int := b2 e * b2 e - 24 * b4 e
def c6 (e : IntegralModel) : Int :=
  -(b2 e * b2 e * b2 e) + 36 * b2 e * b4 e - 216 * b6 e
def discriminant (e : IntegralModel) : Int :=
  -(b2 e * b2 e * b8 e) - 8 * b4 e * b4 e * b4 e -
    27 * b6 e * b6 e + 9 * b2 e * b4 e * b6 e

def curve121a1 : IntegralModel := ⟨1, 1, 1, -30, -76⟩
def curve121b1 : IntegralModel := ⟨0, -1, 1, -7, 10⟩

/-- Exactly the divisibility conditions for valuation k, with no valuation
oracle. A zero input fails the second condition. -/
def ExactValuation (p k : Nat) (z : Int) : Prop :=
  (p : Int) ^ k ∣ z ∧ ¬ (p : Int) ^ (k + 1) ∣ z

instance (p k : Nat) (z : Int) : Decidable (ExactValuation p k z) :=
  inferInstanceAs (Decidable ((p : Int) ^ k ∣ z ∧ ¬ (p : Int) ^ (k + 1) ∣ z))

/-- Numerical II/III branches at p >= 5, returning conductor exponent,
Kodaira code, and component number. No general Tate algorithm is claimed.
The positive discriminant valuations 2 and 3 are below 12 and, with p|c4,
have integral j; these are the minimal potentially-good shallow branches.
Correct arithmetic interpretation of this output is an external import. -/
def shallowTateBranch (e : IntegralModel) (p : Nat) : Option (Nat × Nat × Nat) :=
  if IsPrime p ∧ 5 ≤ p ∧ (p : Int) ∣ c4 e then
    if ExactValuation p 2 (discriminant e) then some (2, 2, 1)
    else if ExactValuation p 3 (discriminant e) then some (2, 3, 2)
    else none
  else none

theorem primaryModelInvariants :
    (c4 curve121a1, c6 curve121a1, discriminant curve121a1) =
      (1441, 54703, -121) ∧
    (c4 curve121b1, c6 curve121b1, discriminant curve121b1) =
      (352, -6776, -1331) := by decide +kernel

theorem numericalShallowBranches :
    shallowTateBranch curve121a1 11 = some (2, 2, 1) ∧
    shallowTateBranch curve121b1 11 = some (2, 3, 2) := by decide +kernel

private theorem primeDvdProduct (p a b : Nat) (hp : IsPrime p)
    (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  obtain ⟨u, v, hua, hvb, huv⟩ := Nat.dvd_mul.mp h
  have hup : u ∣ p := ⟨v, huv.symm⟩
  rcases hp.2 u hup with hu | hu
  · subst u
    have hv : v = p := by simpa using huv
    exact Or.inr (hv ▸ hvb)
  · subst u
    exact Or.inl hua

/-- Each model has nonzero discriminant with exactly the prime support {11}.
This proves support from the equation, independently of a conductor label.
It does not construct the Neron model. -/
theorem discriminantPrimeSupport (e : IntegralModel)
    (he : e = curve121a1 ∨ e = curve121b1) (p : Nat) (hp : IsPrime p) :
    p ∣ (discriminant e).natAbs ↔ p = 11 := by
  have primeEleven : IsPrime 11 := by decide +kernel
  have hp11 (hd : p ∣ 11) : p = 11 := by
    rcases primeEleven.2 p hd with h | h
    · have := hp.1; omega
    · exact h
  rcases he with he | he
  · subst e
    constructor
    · intro hd
      change p ∣ 11 * 11 at hd
      exact (primeDvdProduct p 11 11 hp hd).elim hp11 hp11
    · intro heq; subst p; decide +kernel
  · subst e
    constructor
    · intro hd
      change p ∣ 11 * (11 * 11) at hd
      rcases primeDvdProduct p 11 (11 * 11) hp hd with hd | hd
      · exact hp11 hd
      · exact (primeDvdProduct p 11 11 hp hd).elim hp11 hp11
    · intro heq; subst p; decide +kernel

/-- Every possible shallow component number is a unit at its odd place.
Consequently its unit class cannot itself retain its exact value. -/
theorem shallowFactorUnitAtOddPlace (p c : Nat) (hp : IsPrime p)
    (hp2 : p ≠ 2) (hc : c = 1 ∨ c = 2) : UnitAt (c : Rat) p := by
  rcases hc with hc | hc
  · subst c
    exact oneUnitAt p hp
  · subst c
    exact primeCastUnitAt 2 p (by decide +kernel) hp hp2

/-- An admissible observation of a scalar modulo local units must be
unchanged by multiplication by any rational local unit. This declares the
coarsened interface, rather than silently weakening the whole source record. -/
def UnitInvariant (p : Nat) {Answer : Type} (observe : Rat → Answer) : Prop :=
  ∀ u r : Rat, UnitAt u p → observe (u * r) = observe r

theorem shallowFactorsHaveSameUnitObservation (p : Nat) (hp : IsPrime p)
    (hp2 : p ≠ 2) {Answer : Type} (observe : Rat → Answer)
    (hobserve : UnitInvariant p observe) : observe 2 = observe 1 := by
  simpa using hobserve 2 1
    (shallowFactorUnitAtOddPlace p 2 hp hp2 (Or.inr rfl))

/-- Universal no-go over the unit-class interface, not over all information
in an elliptic-curve equation or the full recognition record. -/
theorem noExactShallowFactorFromUnitClass (p : Nat) (hp : IsPrime p)
    (hp2 : p ≠ 2) :
    ¬ ∃ readout : Rat → Nat, UnitInvariant p readout ∧
      readout 1 = 1 ∧ readout 2 = 2 := by
  rintro ⟨readout, hi, h1, h2⟩
  have h := shallowFactorsHaveSameUnitObservation p hp hp2 readout hi
  omega

/-- The two equation-driven branches instantiate the obstruction. The
readout receives only the component number's unit class, not the equation,
Kodaira code, rank, or exact component-number field of a source record. -/
theorem noExactCurveBranchReadoutFromUnitClass :
    ¬ ∃ readout : Rat → Nat, UnitInvariant 11 readout ∧
      ∀ e kod c, (e = curve121a1 ∨ e = curve121b1) →
        shallowTateBranch e 11 = some (2, kod, c) → readout (c : Rat) = c := by
  rintro ⟨readout, hi, hreturn⟩
  apply noExactShallowFactorFromUnitClass 11 (by decide +kernel) (by decide +kernel)
  exact ⟨readout, hi,
    hreturn curve121a1 2 1 (Or.inl rfl) numericalShallowBranches.1,
    hreturn curve121b1 3 2 (Or.inr rfl) numericalShallowBranches.2⟩

/-- The actual rational multiplier 1/2 witnesses congruence of 1 and 2
modulo 11-adic units. No p-adic completion is constructed here. -/
theorem explicitUnitCongruence :
    UnitAt (1 / 2 : Rat) 11 ∧ (1 : Rat) = (1 / 2 : Rat) * 2 ∧
    UnitAt (2 : Rat) 11 := by decide +kernel

/-- A factor arising at the bad place 11 has coefficient support at 2.
Finite bad-place checks do not supply the support premise of global recovery. -/
theorem badPlaceDoesNotBoundFactorSupport :
    (∀ p, IsPrime p → p = 11 → UnitAt (2 : Rat) p) ∧
    ¬ SupportedOn (2 : Rat) (fun p => p = 11) ∧ (2 : Rat) ≠ 1 := by
  refine ⟨?_, ?_, by decide +kernel⟩
  · intro p _ heq
    subst p
    decide +kernel
  · intro hs
    have h := hs 2 (by decide +kernel) (Or.inl (by decide +kernel))
    omega

/-- Adding the coefficient-prime observation repairs this restricted
one-factor carrier. For unrestricted products a unit flag alone does not
recover the exponent; the range {1,2} is an essential hypothesis. -/
def recoverShallowFactor (unitAtTwo : Bool) : Nat := if unitAtTwo then 1 else 2

theorem coefficientPrimeRepairsShallowReadout (c : Nat) (hc : c = 1 ∨ c = 2) :
    recoverShallowFactor (decide (UnitAt (c : Rat) 2)) = c := by
  rcases hc with hc | hc
  all_goals subst c; decide +kernel

/-- Reject good reduction, a wrong prime, and a composite index. These
checks exercise the actual branch selector, not a supplied output field. -/
theorem falseBranchControls :
    shallowTateBranch curve121a1 5 = none ∧
    shallowTateBranch curve121b1 2 = none ∧
    shallowTateBranch curve121b1 9 = none := by decide +kernel

theorem coefficientPrimeFlagCannotRecoverProducts :
    ¬ ∃ readout : Bool → Nat,
      readout (decide (UnitAt (2 : Rat) 2)) = 2 ∧
      readout (decide (UnitAt (4 : Rat) 2)) = 4 := by
  rintro ⟨readout, h2, h4⟩
  change readout false = 2 at h2
  change readout false = 4 at h4
  omega

end SixBirdsBSD.Closure.LocalUnitSupport
