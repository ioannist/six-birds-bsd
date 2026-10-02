import Init.Data.Rat.Lemmas
import SixBirdsBSD.Apparatus.Comparison
import SixBirdsBSD.Apparatus.DetAssembly

/-!
Normalization counterexamples for the definition audit. These are exact
rational calculations; they do not realize an elliptic curve, determinant
line, or arithmetic Cassels--Tate comparison.
-/
namespace SixBirdsBSD.Apparatus.NormalizationChecks

abbrev Matrix2 := Fin 2 → Fin 2 → Rat

def alternatingLift (x : Rat) : Matrix2 :=
  fun i j => if i = 0 ∧ j = 1 then x else if i = 1 ∧ j = 0 then -x else 0

/-- The Pfaffian of a two-by-two alternating matrix is its upper-right entry. -/
def pfaffian2 (m : Matrix2) : Rat := m 0 1

/-- Entrywise equality modulo integers, expressed with actual rational lifts. -/
def sameEntriesModIntegers (m n : Matrix2) : Prop :=
  ∀ i j, ∃ z : Int, m i j - n i j = (z : Rat)

private def integralCorrection (i j : Fin 2) : Int :=
  if i = 0 ∧ j = 1 then -1 else if i = 1 ∧ j = 0 then 1 else 0

/-- Two lifts of the same torsion-valued matrix need not have the same real
Pfaffian coefficient. An integral presentation and normalization are required
before a raw torsion-valued pairing can be read as a scalar Pfaffian. -/
theorem pfaffianDependsOnLift :
    sameEntriesModIntegers (alternatingLift (1 / 2)) (alternatingLift (3 / 2)) ∧
      pfaffian2 (alternatingLift (1 / 2)) ≠ pfaffian2 (alternatingLift (3 / 2)) := by
  constructor
  · intro i j
    refine ⟨integralCorrection i j, ?_⟩
    have h : ∀ i j : Fin 2,
        alternatingLift (1 / 2) i j - alternatingLift (3 / 2) i j =
          (integralCorrection i j : Rat) := by
      decide +kernel
    exact h i j
  · decide +kernel

/-- No lift-invariant scalar readout equals the numerical Pfaffian on every
two-by-two rational alternating lift. Determinant-line or ideal-valued
constructions are different targets and are not excluded here. -/
theorem noLiftInvariantNumericalPfaffian
    (readout : Matrix2 → Rat)
    (hinvariant : ∀ x y : Rat,
      sameEntriesModIntegers (alternatingLift x) (alternatingLift y) →
        readout (alternatingLift x) = readout (alternatingLift y)) :
    ¬ (∀ x : Rat, readout (alternatingLift x) = pfaffian2 (alternatingLift x)) := by
  intro hpf
  have heq := hinvariant (1 / 2) (3 / 2) pfaffianDependsOnLift.1
  rw [hpf, hpf] at heq
  exact pfaffianDependsOnLift.2 heq

def arithmeticProduct (height analytic finite padic : Rat) : Rat :=
  ((height * analytic) * finite) * padic

def finalAssembly : Rat :=
  DetAssembly.detAssemblyMap arithmeticProduct (fun x orientation => x * orientation)
    (2, 3, 5, 7, 1)

def reusedFinalAssembly : Rat :=
  Comparison.fiveColumnTensor
    (fun a h f p d : Rat => (((a * h) * f) * p) * d)
    (2, 3, 5, 7, finalAssembly)

def independentOrientationAssembly : Rat :=
  Comparison.fiveColumnTensor
    (fun a h f p orientation : Rat => (((a * h) * f) * p) * orientation)
    (2, 3, 5, 7, 1)

/-- The fifth tensor factor must be the independent orientation/trivialization
input, not the final assembly of the preceding four factors. This example
exercises both existing generic maps on positive, nonidentity input. -/
theorem assembledColumnDoubleCounts :
    finalAssembly = 210 ∧ reusedFinalAssembly = 44100 ∧
      independentOrientationAssembly = 210 ∧ reusedFinalAssembly ≠ finalAssembly := by
  decide +kernel

end SixBirdsBSD.Apparatus.NormalizationChecks
