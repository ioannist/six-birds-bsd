import SixBirdsBSD.Closure.ChiCTp
import SixBirdsBSD.Apparatus.FinitePresentation

/-!
Instance-matching controls for the repaired CT interface. Bool indexes two
actual finite hyperbolic presentations, not elliptic curves. The comparison
squares their computed integral half-orders to their determinant factors.
The eight citation labels are True in this diagnostic; this is not an
instantiation of the named arithmetic theorem stack or a Stark system.
-/
namespace SixBirdsBSD.Closure.CTInstanceChecks

open Imports
open SixBirdsBSD.Apparatus

def modulus (E : Bool) : Nat := if E then 2 else 4
def allowedPrime (E : Bool) : Nat := if E then 3 else 5

abbrev finiteContext : chiCTpContext Bool where
  finiteSha := fun E _ =>
    (FinitePairings.elements (modulus E)).Nodup ∧
      ∀ x : FinitePairings.Plane (modulus E), x ∈ FinitePairings.elements (modulus E)
  nondegenerateCTPairing := fun E _ =>
    if E then FinitePairings.Perfect 2 else FinitePairings.Perfect 4
  selmerComplexHypotheses := fun E p => p = allowedPrime E
  primeNotDividingTamagawa := fun _ p => ¬ p ∣ 1
  T_E1 := fun _ _ => True
  T_E2 := fun _ _ => True
  T_E3 := fun _ _ => True
  T_E4 := fun _ _ => True
  T_E5 := fun _ _ => True
  T_E6 := fun _ _ => True
  T_E7 := fun _ _ => True
  T_E8 := fun _ _ => True
  Sigma_NekCT := fun _ _ => 1
  SqrtFittCTDomain := fun _ _ => Nat
  VctpCodomain := fun _ _ => Nat
  sqrtStarkGenerator := fun E _ => some (FinitePresentation.normalizedHalfOrder (modulus E))
  h_p_CT := fun E _ => some (FinitePresentation.normalizedFiniteFactor (modulus E))
  canonicalProperty := fun _ _ f => ∀ n, f n = n * n

def finiteCertificate (E : Bool) : chiCTpImport finiteContext E (allowedPrime E) where
  applicability := {
    prime := by cases E <;> decide +kernel
    finiteSha := ⟨FinitePresentation.elementsNodup _, FinitePresentation.elementsComplete _⟩
    nondegenerateCTPairing := by
      cases E
      · exact FinitePairings.perfectFour
      · exact FinitePairings.perfectTwo
    selmerComplexHypotheses := rfl
    primeNotDividingTamagawa := by
      change ¬ allowedPrime E ∣ 1
      cases E <;> decide +kernel }
  T_E1_proof := True.intro
  T_E2_proof := True.intro
  T_E3_proof := True.intro
  T_E4_proof := True.intro
  T_E5_proof := True.intro
  T_E6_proof := True.intro
  T_E7_proof := True.intro
  T_E8_proof := True.intro
  Sigma_NekCT_eq_plus_one := rfl
  sqrtStarkGenerator := FinitePresentation.normalizedHalfOrder (modulus E)
  sqrtStarkGenerator_selected := rfl
  h_p_CT := FinitePresentation.normalizedFiniteFactor (modulus E)
  h_p_CT_selected := rfl
  canonicalPfaffian := fun n : Nat => n * n
  canonicalProperty_proof := fun _ => rfl
  pfaffianSends := (FinitePresentation.determinantReturnsFiniteOrder (modulus E)).2

theorem matchedInstancesReturnDifferentFactors :
    (finiteCertificate true).canonicalPfaffian (finiteCertificate true).sqrtStarkGenerator = 4 ∧
    (finiteCertificate false).canonicalPfaffian (finiteCertificate false).sqrtStarkGenerator = 16 := by
  decide +kernel

theorem wrongCurveCannotSupplyComparison : ¬ Nonempty (chiCTpImport finiteContext false 3) := by
  rintro ⟨d⟩
  have h := d.applicability.selmerComplexHypotheses
  change (3 : Nat) = 5 at h
  omega

theorem wrongPrimeCannotSupplyComparison : ¬ Nonempty (chiCTpImport finiteContext true 5) := by
  rintro ⟨d⟩
  have h := d.applicability.selmerComplexHypotheses
  change (5 : Nat) = 3 at h
  omega

theorem compositeCannotSupplyComparison : ¬ Nonempty (chiCTpImport finiteContext true 9) := by
  rintro ⟨d⟩
  have h := d.applicability.prime.2 3 (by decide : 3 ∣ 9)
  omega

def withoutGenerator : chiCTpContext Bool :=
  { finiteContext with sqrtStarkGenerator := fun _ _ => none }

def withoutTarget : chiCTpContext Bool :=
  { finiteContext with h_p_CT := fun _ _ => none }

theorem missingSelectionCannotSupplyComparison :
    ¬ Nonempty (chiCTpImport withoutGenerator true 3) ∧
      ¬ Nonempty (chiCTpImport withoutTarget true 3) := by
  exact ⟨chiCTpImport.missingGeneratorPreventsComparison rfl,
    chiCTpImport.missingCTTargetPreventsComparison rfl⟩

/-- Existing applicability survives both selection ablations. It cannot
on its own populate the independently required comparison certificate. -/
theorem applicabilityDoesNotSupplySelections :
    chiCTpApplicability withoutGenerator true 3 ∧ chiCTpApplicability withoutTarget true 3 := by
  have d := (finiteCertificate true).applicability
  constructor
  all_goals exact ⟨d.prime, d.finiteSha, d.nondegenerateCTPairing,
    d.selmerComplexHypotheses, d.primeNotDividingTamagawa⟩

theorem wrongMapFailsNativeReturn :
    (fun n : Nat => n) (finiteCertificate true).sqrtStarkGenerator ≠
      (finiteCertificate true).h_p_CT := by
  decide +kernel

theorem comparisonUsesIndexedInstance (E : Bool) :
    ∃ f : Nat → Nat,
      (∀ n, f n = n * n) ∧
      f (FinitePresentation.normalizedHalfOrder (modulus E)) =
        FinitePresentation.normalizedFiniteFactor (modulus E) := by
  obtain ⟨f, hcanonical, hreturn, _⟩ :=
    ChiCTp.chiCTpComparison E (allowedPrime E) finiteContext (finiteCertificate E)
  exact ⟨f, hcanonical, hreturn⟩

end SixBirdsBSD.Closure.CTInstanceChecks
