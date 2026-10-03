import SixBirdsBSD.Apparatus.SupportPrimeNoGo

/-!
Imported theorem-record structures for the closure axis.

The declarations in this module are sourced-assumption carriers. They
are ordinary Lean `structure`s whose fields record the imported
theorem statements and certificates supplied by later hypotheses. The
local consistency lemmas below do not derive the arithmetic comparisons.
-/

namespace SixBirdsBSD.Closure.Imports

universe u v w x uE

/--
The native family for the imported `chi_CT,p` stack, with hypotheses,
the eight theorem statements, carriers, partial generator/target
selections, and sign fixed by curve and numerical prime. The comparison
record below separately supplies their certificates and the normalized
positive sign. The named propositions do not derive that comparison.
In particular, Nekovar
10.8.7 compares raw U_{2,2} on torsion H^2 with *minus* the Flach pairing;
a cohomology identification and explicit sign correction are required.
The odd-prime Stark-system results do not supply a prime-two extension.
-/
structure chiCTpContext (EllipticCurve : Type u) where
  finiteSha : EllipticCurve → Nat → Prop
  nondegenerateCTPairing : EllipticCurve → Nat → Prop
  selmerComplexHypotheses : EllipticCurve → Nat → Prop
  primeNotDividingTamagawa : EllipticCurve → Nat → Prop
  T_E1 : EllipticCurve → Nat → Prop
  T_E2 : EllipticCurve → Nat → Prop
  T_E3 : EllipticCurve → Nat → Prop
  T_E4 : EllipticCurve → Nat → Prop
  T_E5 : EllipticCurve → Nat → Prop
  T_E6 : EllipticCurve → Nat → Prop
  T_E7 : EllipticCurve → Nat → Prop
  T_E8 : EllipticCurve → Nat → Prop
  Sigma_NekCT : EllipticCurve → Nat → Int
  SqrtFittCTDomain : EllipticCurve → Nat → Type
  VctpCodomain : EllipticCurve → Nat → Type
  /-- Partial native selections avoid assuming bases exist at every
  curve/prime outside the applicable comparison scope. -/
  sqrtStarkGenerator : ∀ E p, Option (SqrtFittCTDomain E p)
  h_p_CT : ∀ E p, Option (VctpCodomain E p)
  canonicalProperty : ∀ E p, (SqrtFittCTDomain E p → VctpCodomain E p) → Prop

/-- Applicability is checked at the same indexed instance as the
comparison. The predicates need an arithmetic interpretation; only
primality has a fixed mathematical definition here. No odd-prime or
ordinary theorem is silently extended to another local scope. -/
structure chiCTpApplicability {EllipticCurve : Type u}
    (context : chiCTpContext EllipticCurve) (E : EllipticCurve) (p : Nat) : Prop where
  prime : SixBirdsBSD.Apparatus.SupportPrimeNoGo.IsPrime p
  finiteSha : context.finiteSha E p
  nondegenerateCTPairing : context.nondegenerateCTPairing E p
  selmerComplexHypotheses : context.selmerComplexHypotheses E p
  primeNotDividingTamagawa : context.primeNotDividingTamagawa E p

/-- A supplied comparison at one fixed curve/prime of a declared native
family. The family fixes the hypotheses, carriers, generators, target,
and sign before the comparison certificate is supplied. This prevents
accidental instance substitution; it does not derive the arithmetic map
from the eight theorem certificates. -/
structure chiCTpImport {EllipticCurve : Type u}
    (context : chiCTpContext EllipticCurve) (E : EllipticCurve) (p : Nat) where
  applicability : chiCTpApplicability context E p
  T_E1_proof : context.T_E1 E p
  T_E2_proof : context.T_E2 E p
  T_E3_proof : context.T_E3 E p
  T_E4_proof : context.T_E4 E p
  T_E5_proof : context.T_E5 E p
  T_E6_proof : context.T_E6 E p
  T_E7_proof : context.T_E7 E p
  T_E8_proof : context.T_E8 E p
  Sigma_NekCT_eq_plus_one : context.Sigma_NekCT E p = 1
  sqrtStarkGenerator : context.SqrtFittCTDomain E p
  sqrtStarkGenerator_selected : context.sqrtStarkGenerator E p = some sqrtStarkGenerator
  h_p_CT : context.VctpCodomain E p
  h_p_CT_selected : context.h_p_CT E p = some h_p_CT
  canonicalPfaffian : context.SqrtFittCTDomain E p → context.VctpCodomain E p
  canonicalProperty_proof : context.canonicalProperty E p canonicalPfaffian
  pfaffianSends : canonicalPfaffian sqrtStarkGenerator = h_p_CT

variable {EllipticCurve : Type u} {context : chiCTpContext EllipticCurve}
  {E : EllipticCurve} {p : Nat}

abbrev chiCTpImport.T_E1 (_d : chiCTpImport context E p) : Prop := context.T_E1 E p
abbrev chiCTpImport.T_E2 (_d : chiCTpImport context E p) : Prop := context.T_E2 E p
abbrev chiCTpImport.T_E3 (_d : chiCTpImport context E p) : Prop := context.T_E3 E p
abbrev chiCTpImport.T_E4 (_d : chiCTpImport context E p) : Prop := context.T_E4 E p
abbrev chiCTpImport.T_E5 (_d : chiCTpImport context E p) : Prop := context.T_E5 E p
abbrev chiCTpImport.T_E6 (_d : chiCTpImport context E p) : Prop := context.T_E6 E p
abbrev chiCTpImport.T_E7 (_d : chiCTpImport context E p) : Prop := context.T_E7 E p
abbrev chiCTpImport.T_E8 (_d : chiCTpImport context E p) : Prop := context.T_E8 E p
abbrev chiCTpImport.Sigma_NekCT (_d : chiCTpImport context E p) : Int := context.Sigma_NekCT E p
abbrev chiCTpImport.SqrtFittCTDomain (_d : chiCTpImport context E p) : Type := context.SqrtFittCTDomain E p
abbrev chiCTpImport.VctpCodomain (_d : chiCTpImport context E p) : Type := context.VctpCodomain E p
abbrev chiCTpImport.canonicalProperty (_d : chiCTpImport context E p) := context.canonicalProperty E p

/-- Certificates cannot silently choose a different native generator or
CT target within the same declared family and indexed instance. -/
theorem chiCTpImport.nativeSelectionsAgree (a b : chiCTpImport context E p) :
    a.sqrtStarkGenerator = b.sqrtStarkGenerator ∧ a.h_p_CT = b.h_p_CT := by
  constructor
  · exact Option.some.inj (a.sqrtStarkGenerator_selected.symm.trans b.sqrtStarkGenerator_selected)
  · exact Option.some.inj (a.h_p_CT_selected.symm.trans b.h_p_CT_selected)

theorem chiCTpImport.missingGeneratorPreventsComparison (h : context.sqrtStarkGenerator E p = none) :
    ¬ Nonempty (chiCTpImport context E p) := by
  rintro ⟨d⟩
  have hd := d.sqrtStarkGenerator_selected
  rw [h] at hd
  cases hd

theorem chiCTpImport.missingCTTargetPreventsComparison (h : context.h_p_CT E p = none) :
    ¬ Nonempty (chiCTpImport context E p) := by
  rintro ⟨d⟩
  have hd := d.h_p_CT_selected
  rw [h] at hd
  cases hd

/-- Native Selmer-complex data fixed by curve before the import certificates
are supplied. The family is an explicit premise of the conditional translation;
no arithmetic Selmer complex or pairing is derived here. -/
structure aEContext (EllipticCurve : Type uE) where
  TargetCategory : EllipticCurve → Type u
  Hom : ∀ E, TargetCategory E → TargetCategory E → Type v
  SelmerComplex : EllipticCurve → Type w
  PairingTarget : EllipticCurve → Type x
  pairing : ∀ E, SelmerComplex E → SelmerComplex E → PairingTarget E
  nekovarSelmerComplexWithIntrinsicCasselsTatePairing : EllipticCurve → Prop
  burnsFlachMaciasSanoNekovarAESelFormulation : EllipticCurve → Prop
  pairingBilinearOrCategorical : EllipticCurve → Prop

/-- The imported `A_E` unified Selmer-complex pairing substrate at one
specified curve of the declared family. Arithmetic content remains supplied,
with the same three certificate premises as before. -/
structure aEImport {EllipticCurve : Type uE}
    (context : aEContext EllipticCurve) (E : EllipticCurve) where
  nekovarSelmerComplexWithIntrinsicCasselsTatePairing_proof :
    context.nekovarSelmerComplexWithIntrinsicCasselsTatePairing E
  burnsFlachMaciasSanoNekovarAESelFormulation_proof :
    context.burnsFlachMaciasSanoNekovarAESelFormulation E
  pairingBilinearOrCategorical_proof : context.pairingBilinearOrCategorical E

variable {AECurve : Type uE} {aEContext : aEContext AECurve} {aE : AECurve}

abbrev aEImport.TargetCategory (_d : aEImport aEContext aE) := aEContext.TargetCategory aE
abbrev aEImport.Hom (_d : aEImport aEContext aE) := aEContext.Hom aE
abbrev aEImport.SelmerComplex (_d : aEImport aEContext aE) := aEContext.SelmerComplex aE
abbrev aEImport.PairingTarget (_d : aEImport aEContext aE) := aEContext.PairingTarget aE
abbrev aEImport.pairing (_d : aEImport aEContext aE) := aEContext.pairing aE
abbrev aEImport.nekovarSelmerComplexWithIntrinsicCasselsTatePairing
    (_d : aEImport aEContext aE) : Prop :=
  aEContext.nekovarSelmerComplexWithIntrinsicCasselsTatePairing aE
abbrev aEImport.burnsFlachMaciasSanoNekovarAESelFormulation
    (_d : aEImport aEContext aE) : Prop :=
  aEContext.burnsFlachMaciasSanoNekovarAESelFormulation aE
abbrev aEImport.pairingBilinearOrCategorical (_d : aEImport aEContext aE) : Prop :=
  aEContext.pairingBilinearOrCategorical aE

/-- Native archimedean data and the determinant/L-value comparison statement
fixed by curve before certificates. This is conditional comparison content,
not a construction or proof of a general elliptic-curve L-value theorem. -/
structure beilinsonContext (EllipticCurve : Type uE) where
  rank : EllipticCurve → Nat
  ArchimedeanRegulator : EllipticCurve → Type u
  DeterminantLine : EllipticCurve → Type v
  LValueSide : EllipticCurve → Type w
  regulatorToDeterminantLine : ∀ E, ArchimedeanRegulator E → DeterminantLine E
  determinantLValueComparison : EllipticCurve → Prop

/-- The Beilinson rank-at-least-two comparison at one curve of a fixed
family. The rank bound and comparison are explicit hypotheses. -/
structure beilinsonImport {EllipticCurve : Type uE}
    (context : beilinsonContext EllipticCurve) (E : EllipticCurve) where
  rank_ge_two : 2 ≤ context.rank E
  determinantLValueComparison_proof : context.determinantLValueComparison E

variable {BICurve : Type uE} {biContext : beilinsonContext BICurve} {biE : BICurve}

abbrev beilinsonImport.rank (_d : beilinsonImport biContext biE) := biContext.rank biE
abbrev beilinsonImport.ArchimedeanRegulator (_d : beilinsonImport biContext biE) :=
  biContext.ArchimedeanRegulator biE
abbrev beilinsonImport.DeterminantLine (_d : beilinsonImport biContext biE) :=
  biContext.DeterminantLine biE
abbrev beilinsonImport.LValueSide (_d : beilinsonImport biContext biE) :=
  biContext.LValueSide biE
abbrev beilinsonImport.regulatorToDeterminantLine (_d : beilinsonImport biContext biE) :=
  biContext.regulatorToDeterminantLine biE
abbrev beilinsonImport.determinantLValueComparison
    (_d : beilinsonImport biContext biE) : Prop :=
  biContext.determinantLValueComparison biE

/-- Certificates cannot replace the prescribed curve's pairing with a
pairing from another instance in the declared native family. -/
theorem aEImport.pairingFixed (d : aEImport aEContext aE) :
    d.pairing = aEContext.pairing aE := rfl

/-- A low-rank instance cannot populate the higher-rank comparison record. -/
theorem beilinsonImport.lowRankPreventsComparison
    (h : biContext.rank biE < 2) : ¬ Nonempty (beilinsonImport biContext biE) := by
  rintro ⟨d⟩
  have hd := d.rank_ge_two
  omega

/-- A false comparison at the prescribed curve cannot be replaced with
an import certificate for a different curve in the same family. -/
theorem beilinsonImport.failedComparisonPreventsImport
    (h : ¬ biContext.determinantLValueComparison biE) :
    ¬ Nonempty (beilinsonImport biContext biE) := by
  rintro ⟨d⟩
  exact h d.determinantLValueComparison_proof

/-- The pairing premise is also checked at the specified curve. -/
theorem aEImport.failedPairingPreventsImport
    (h : ¬ aEContext.pairingBilinearOrCategorical aE) :
    ¬ Nonempty (aEImport aEContext aE) := by
  rintro ⟨d⟩
  exact h d.pairingBilinearOrCategorical_proof

end SixBirdsBSD.Closure.Imports
