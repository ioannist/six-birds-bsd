/-!
Imported theorem-record structures for the closure axis.

The declarations in this module are sourced-assumption carriers. They
are ordinary Lean `structure`s whose fields record the imported
theorem statements and certificates supplied by later hypotheses; no
project-local theorem is derived here.
-/

namespace SixBirdsBSD.Closure.Imports

universe u v w x

/--
The imported `chi_CT,p` theorem stack: eight named external theorem
statements `T_E1` through `T_E8`, each carried with its certificate,
plus the unconditional Nekovar-Cassels-Tate sign closure
`Sigma_NekCT = +1`, and the canonical Pfaffian comparison data
established by the imported stack.
-/
structure chiCTpImport where
  T_E1 : Prop
  T_E1_proof : T_E1
  T_E2 : Prop
  T_E2_proof : T_E2
  T_E3 : Prop
  T_E3_proof : T_E3
  T_E4 : Prop
  T_E4_proof : T_E4
  T_E5 : Prop
  T_E5_proof : T_E5
  T_E6 : Prop
  T_E6_proof : T_E6
  T_E7 : Prop
  T_E7_proof : T_E7
  T_E8 : Prop
  T_E8_proof : T_E8
  Sigma_NekCT : Int
  Sigma_NekCT_eq_plus_one : Sigma_NekCT = 1
  SqrtFittCTDomain : Type
  VctpCodomain : Type
  sqrtStarkGenerator : SqrtFittCTDomain
  h_p_CT : VctpCodomain
  canonicalPfaffian : SqrtFittCTDomain → VctpCodomain
  canonicalProperty : Prop
  canonicalProperty_proof : canonicalProperty
  pfaffianSends : canonicalPfaffian sqrtStarkGenerator = h_p_CT

/--
The imported `A_E` unified Selmer-complex pairing substrate. It supplies
a typed target category, a Selmer-complex carrier, a pairing, and
certificates for the Nekovar Cassels-Tate and
Burns-Flach-Macias-Sano-Nekovar `A_E^Sel` inputs, together with the
bilinear/categorical pairing property.
-/
structure aEImport where
  TargetCategory : Type u
  Hom : TargetCategory → TargetCategory → Type v
  SelmerComplex : Type w
  PairingTarget : Type x
  pairing : SelmerComplex → SelmerComplex → PairingTarget
  nekovarSelmerComplexWithIntrinsicCasselsTatePairing : Prop
  nekovarSelmerComplexWithIntrinsicCasselsTatePairing_proof :
    nekovarSelmerComplexWithIntrinsicCasselsTatePairing
  burnsFlachMaciasSanoNekovarAESelFormulation : Prop
  burnsFlachMaciasSanoNekovarAESelFormulation_proof :
    burnsFlachMaciasSanoNekovarAESelFormulation
  pairingBilinearOrCategorical : Prop
  pairingBilinearOrCategorical_proof : pairingBilinearOrCategorical

/--
The imported Beilinson rank-`>= 2` determinant/L-value comparison:
rank data, the archimedean regulator-to-determinant-line map, and a
certificate for the determinant/L-value comparison used by the landing.
-/
structure beilinsonImport where
  rank : Nat
  rank_ge_two : 2 ≤ rank
  ArchimedeanRegulator : Type u
  DeterminantLine : Type v
  LValueSide : Type w
  regulatorToDeterminantLine : ArchimedeanRegulator → DeterminantLine
  determinantLValueComparison : Prop
  determinantLValueComparison_proof : determinantLValueComparison

end SixBirdsBSD.Closure.Imports
