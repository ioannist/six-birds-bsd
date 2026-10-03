import SixBirdsBSD.Closure.Imports

/-!
The `χ_{CT,p}` Cassels–Tate Pfaffian comparison (supporting) for the
closure axis.

The theorem here is conditional on the imported `chi_CT,p` stack. The
import carrier supplies the eight named proposition certificates and a
separate normalized sign certificate. Neither their arithmetic instantiation
nor the sign correction from raw U_{2,2} is proved by this projection.
-/

namespace SixBirdsBSD.Closure.ChiCTp

universe u v w

/--
Conditional `chi_CT,p` comparison. From the finite-Sha, nondegenerate
Cassels-Tate pairing, Sakamoto/Macias-Sano Selmer-complex, and
`p`-not-Tamagawa hypotheses, a supplied comparison record gives a
canonical orientation-respecting Pfaffian map
`sqrtFittCT_H1Cp_div_U22 -> vctp_p` sending the square-root Stark
generator to `h_p_CT_E`, with normalized sign `Sigma_NekCT = +1`.
The fixed native family and certificate are indexed by the same curve and
numerical prime, with applicability returned explicitly. Their arithmetic
interpretation remains supplied. The raw cited U_{2,2} pairing is on
torsion H^2, not the H^1/div label used in this generic projection's prose.
-/
theorem chiCTpComparison
    {EllipticCurve : Type u}
    (E : EllipticCurve) (p : Nat)
    (context : SixBirdsBSD.Closure.Imports.chiCTpContext EllipticCurve)
    (chiImport : SixBirdsBSD.Closure.Imports.chiCTpImport context E p) :
    ∃ Pf_Nek_p_or_sqrt :
        chiImport.SqrtFittCTDomain → chiImport.VctpCodomain,
      chiImport.canonicalProperty Pf_Nek_p_or_sqrt ∧
        Pf_Nek_p_or_sqrt chiImport.sqrtStarkGenerator =
          chiImport.h_p_CT ∧
        chiImport.Sigma_NekCT = 1 ∧
        chiImport.T_E1 ∧ chiImport.T_E2 ∧ chiImport.T_E3 ∧
        chiImport.T_E4 ∧ chiImport.T_E5 ∧ chiImport.T_E6 ∧
        chiImport.T_E7 ∧ chiImport.T_E8 ∧
        SixBirdsBSD.Closure.Imports.chiCTpApplicability context E p := by
  exact
    ⟨chiImport.canonicalPfaffian, chiImport.canonicalProperty_proof,
      chiImport.pfaffianSends, chiImport.Sigma_NekCT_eq_plus_one,
      chiImport.T_E1_proof, chiImport.T_E2_proof, chiImport.T_E3_proof,
      chiImport.T_E4_proof, chiImport.T_E5_proof, chiImport.T_E6_proof,
      chiImport.T_E7_proof, chiImport.T_E8_proof, chiImport.applicability⟩

end SixBirdsBSD.Closure.ChiCTp
