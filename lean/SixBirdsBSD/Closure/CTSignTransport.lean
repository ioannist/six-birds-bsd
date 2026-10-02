import SixBirdsBSD.Apparatus.NormalizationChecks
import SixBirdsBSD.Closure.RationalLocalGlobal

/-!
Sign correction for the cited Nekovar--Flach comparison, and exact controls
for its scalar return. The arithmetic cohomology identification and source
theorems remain inputs; these are rational algebra and normalization results.
-/
namespace SixBirdsBSD.Closure.CTSignTransport

open SixBirdsBSD.Apparatus.NormalizationChecks
open SixBirdsBSD.Apparatus.SupportPrimeNoGo
open SixBirdsBSD.Closure.CoupledFactors
open SixBirdsBSD.Closure.RationalLocalGlobal

private theorem ratNegNeg (r : Rat) : -(-r) = r := by
  apply Rat.ext <;> simp

/-- Pullback along an explicitly supplied cohomology identification. -/
def pullbackPairing {X Y : Type} (f : X → Y) (b : Y → Y → Rat) : X → X → Rat :=
  fun x y => b (f x) (f y)

/-- The raw U_{2,2} convention has a minus sign in Nekovar 10.8.7.
Negation is the explicit correction before comparison with the Flach lane. -/
def correctedPairing {X : Type} (raw : X → X → Rat) : X → X → Rat :=
  fun x y => -raw x y

theorem correctedComparison {X Y : Type}
    (f : X → Y) (raw : X → X → Rat) (flach : Y → Y → Rat)
    (hraw : ∀ x y, raw x y = -flach (f x) (f y)) :
    correctedPairing raw = pullbackPairing f flach := by
  funext x y
  dsimp [correctedPairing, pullbackPairing]
  rw [hraw, ratNegNeg]

/-- A simultaneous correction of map and source-generator orientation
preserves the image, provided the actual map respects negation. A positive
final comparison is thus possible, but needs both identified corrections. -/
theorem twoSignCorrectionsCancel (f : Rat → Rat)
    (hneg : ∀ r, f (-r) = -f r) (generator : Rat) :
    -(f (-generator)) = f generator := by
  rw [hneg, ratNegNeg]

/-- At a nonzero value the raw negative comparison cannot also be a
positive comparison. This does not assign the final determinant-line sign. -/
theorem rawComparisonCannotBePositive {X Y : Type}
    (f : X → Y) (raw : X → X → Rat) (flach : Y → Y → Rat)
    (hraw : ∀ x y, raw x y = -flach (f x) (f y))
    (x y : X) (hnonzero : flach (f x) (f y) ≠ 0) :
    raw x y ≠ flach (f x) (f y) := by
  intro heq
  have hn := congrArg Rat.num ((hraw x y).symm.trans heq)
  have hz : (flach (f x) (f y)).num = 0 := by
    simp only [Rat.neg_num] at hn
    omega
  exact hnonzero (Rat.num_eq_zero.mp hz)

/-- The two-torsion-valued pairing cannot distinguish these opposite
rational scalar lifts. Classical 2-Selmer equality cannot alone orient
an odd-prime or rational Pfaffian generator. -/
theorem halfPairingCannotDetectNegation :
    sameEntriesModIntegers (alternatingLift (1 / 2)) (alternatingLift (-1 / 2)) ∧
      pfaffian2 (alternatingLift (1 / 2)) ≠ pfaffian2 (alternatingLift (-1 / 2)) := by
  constructor
  · intro i j
    refine ⟨if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0, ?_⟩
    have h : ∀ i j : Fin 2,
        alternatingLift (1 / 2) i j - alternatingLift (-1 / 2) i j =
          ((if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0 : Int) : Rat) := by
      decide +kernel
    exact h i j
  · decide +kernel

/-- A square (determinant) comparison does not choose a sign of its
Pfaffian generator, even with a nonzero coefficient. -/
theorem squaredComparisonDoesNotFixSign :
    (-(1 / 2 : Rat)) * (-(1 / 2 : Rat)) = (1 / 2 : Rat) * (1 / 2 : Rat) ∧
      (-(1 / 2 : Rat)) ≠ (1 / 2 : Rat) := by
  decide +kernel

private theorem addThenSubtract (a b : Rat) : (a + b) - a = b := by
  calc
    (a + b) - a = (b + a) + -a := by
      rw [Rat.sub_eq_add_neg, Rat.add_comm a b]
    _ = b + (a + -a) := Rat.add_assoc _ _ _
    _ = b + (-a + a) := by rw [Rat.add_comm a (-a)]
    _ = b := by rw [Rat.neg_add_cancel, Rat.add_zero]

/-- A rational class modulo integers killed by two and by an odd integer
is zero. This is the explicit Bezout return, without constructing Q/Z. -/
theorem oddAndTwoTorsionClassIsZero (r : Rat) (k : Int)
    (hodd : ∃ a : Int, ((2 * k + 1 : Int) : Rat) * r = (a : Rat))
    (htwo : ∃ b : Int, 2 * r = (b : Rat)) :
    ∃ c : Int, r = (c : Rat) := by
  obtain ⟨a, ha⟩ := hodd
  obtain ⟨b, hb⟩ := htwo
  have hexpand : ((2 * k + 1 : Int) : Rat) * r - (k : Rat) * (2 * r) = r := by
    simp only [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_ofNat,
      Rat.add_mul, Rat.one_mul]
    rw [Rat.mul_comm 2 (k : Rat), Rat.mul_assoc]
    exact addThenSubtract _ r
  refine ⟨a - k * b, ?_⟩
  calc
    r = ((2 * k + 1 : Int) : Rat) * r - (k : Rat) * (2 * r) := hexpand.symm
    _ = (a : Rat) - (k : Rat) * (b : Rat) := by rw [ha, hb]
    _ = ((a - k * b : Int) : Rat) := by rw [Rat.intCast_sub, Rat.intCast_mul]

/-- In a biadditive classical pairing, an odd-torsion first argument and
a two-torsion second argument force the value to be zero modulo integers.
The hypotheses here express those two annihilations on an actual lift. -/
theorem oddPrimaryPairedWithTwoTorsionIsZero (r : Rat) (p : Nat)
    (hp : p % 2 = 1)
    (hodd : ∃ a : Int, (p : Rat) * r = (a : Rat))
    (htwo : ∃ b : Int, 2 * r = (b : Rat)) :
    ∃ c : Int, r = (c : Rat) := by
  have hdecomp : p = 2 * (p / 2) + 1 := by
    have hd := Nat.mod_add_div p 2
    omega
  have hcast : (p : Int) = 2 * (p / 2 : Nat) + 1 := by
    exact_mod_cast hdecomp
  apply oddAndTwoTorsionClassIsZero r (p / 2 : Nat)
  · rw [← hcast, Rat.intCast_natCast]
    exact hodd
  · exact htwo

/-- False-target control: two-torsion by itself need not be zero modulo
integers. The odd annihilator in the preceding theorem is substantive. -/
theorem halfClassIsNonzeroTwoTorsion :
    (∃ b : Int, 2 * (1 / 2 : Rat) = (b : Rat)) ∧
      ¬ (∃ c : Int, (1 / 2 : Rat) = (c : Rat)) := by
  refine ⟨⟨1, by decide +kernel⟩, ?_⟩
  rintro ⟨c, hc⟩
  have hd := congrArg Rat.den hc
  have hleft : (1 / 2 : Rat).den = 2 := by decide +kernel
  rw [hleft, Rat.den_intCast] at hd
  contradiction

theorem unitAtNegIff (r : Rat) (p : Nat) : UnitAt (-r) p ↔ UnitAt r p := by
  simp [UnitAt]

/-- Exact un-oriented return: local units at every prime leave precisely
the global rational sign ambiguity. -/
theorem allPrimeUnitsForcePlusMinusOne (r : Rat)
    (h : ∀ p, IsPrime p → UnitAt r p) : r = 1 ∨ r = -1 := by
  have htwo : IsPrime 2 := by decide +kernel
  have hnonzero : r ≠ 0 := by
    intro hz
    have h2 := (h 2 htwo).1
    rw [hz] at h2
    exact h2 (by decide +kernel)
  by_cases hpos : 0 < r
  · exact Or.inl (allPrimeUnitsForceOne r hpos h)
  · have hle : r ≤ 0 := by
      rcases Rat.le_total (a := r) (b := 0) with hr | hr
      · exact hr
      · exact False.elim (hpos (Rat.lt_of_le_of_ne hr (Ne.symm hnonzero)))
    have hnpos : 0 < -r := by
      have hnum : r.num < 0 := by
        have hr := (Rat.le_iff r 0).mp hle
        have hn : r.num ≠ 0 := fun hz => hnonzero (Rat.num_eq_zero.mp hz)
        simp only [Rat.num_ofNat, Rat.den_ofNat] at hr
        omega
      apply (Rat.lt_iff 0 (-r)).mpr
      simp only [Rat.num_ofNat, Rat.den_ofNat, Rat.neg_num]
      omega
    have hneg : -r = 1 := allPrimeUnitsForceOne (-r) hnpos
      (fun p hp => (unitAtNegIff r p).mpr (h p hp))
    have := congrArg Neg.neg hneg
    rw [ratNegNeg] at this
    exact Or.inr this

theorem allPrimeUnitsIffPlusMinusOne (r : Rat) :
    (∀ p, IsPrime p → UnitAt r p) ↔ r = 1 ∨ r = -1 := by
  constructor
  · exact allPrimeUnitsForcePlusMinusOne r
  · intro hr p hp
    rcases hr with hr | hr
    · rw [hr]
      exact oneUnitAt p hp
    · rw [hr]
      exact (unitAtNegIff 1 p).mpr (oneUnitAt p hp)

def negativeDefectData : FactorData := ⟨-1, 1, 1, 1, -1, 1, 1, 1⟩

/-- Exercising the actual factor assembly: fixity and every prime-unit
comparison still fail scalar BSD if the sign is not fixed. -/
theorem unsignedUnitAssemblyCanFail :
    NativeFixity negativeDefectData ∧
      (∀ p, IsPrime p → UnitAt (comparisonQuotient negativeDefectData) p) ∧
      ¬ ScalarBSD negativeDefectData := by
  refine ⟨?_, ?_, ?_⟩
  · unfold NativeFixity negativeDefectData
    decide +kernel
  · intro p hp
    have hquot : comparisonQuotient negativeDefectData = -1 := by decide +kernel
    rw [hquot]
    exact (unitAtNegIff 1 p).mpr (oneUnitAt p hp)
  · unfold ScalarBSD negativeDefectData
    decide +kernel

/-- Numerical scope of the cited odd-prime Stark-system route. It is a
necessary screen, not the cartesian/core-vertex applicability proof. -/
def oddStarkScope (p : Nat) : Prop := IsPrime p ∧ p % 2 = 1

theorem twoOutsideOddStarkScope : ¬ oddStarkScope 2 := by
  unfold oddStarkScope
  decide +kernel

end SixBirdsBSD.Closure.CTSignTransport
