import SixBirdsBSD.Closure.Imports

/-!
The `χ_{CT,p}` Cassels–Tate Pfaffian comparison (supporting) for the
closure axis.

The theorem here is conditional on the imported `chi_CT,p` stack. The
import carrier supplies the eight named external certificates and the
unconditional Nekovar-Cassels-Tate sign closure.
-/

namespace SixBirdsBSD.Closure.ChiCTp

universe u v w

/--
Conditional `chi_CT,p` comparison. From the finite-Sha, nondegenerate
Cassels-Tate pairing, Sakamoto/Macias-Sano Selmer-complex, and
`p`-not-Tamagawa hypotheses, the imported `T_E1` through `T_E8` stack
yields a canonical orientation-respecting Pfaffian map
`sqrtFittCT_H1Cp_div_U22 -> vctp_p` sending the square-root Stark
generator to `h_p_CT_E`, with sign closure `Sigma_NekCT = +1`.
-/
theorem chiCTpComparison
    {EllipticCurve Prime : Type u}
    (_E : EllipticCurve) (_p : Prime)
    (finiteSha_p_infty nondegenerateCTPairing
      sakamotoMaciasSanoSelmerComplexHypotheses p_not_dvd_Tam : Prop)
    (_hfiniteSha : finiteSha_p_infty)
    (_hCT : nondegenerateCTPairing)
    (_hSMS : sakamotoMaciasSanoSelmerComplexHypotheses)
    (_hTam : p_not_dvd_Tam)
    (chiImport : SixBirdsBSD.Closure.Imports.chiCTpImport) :
    ∃ Pf_Nek_p_or_sqrt :
        chiImport.SqrtFittCTDomain → chiImport.VctpCodomain,
      chiImport.canonicalProperty ∧
        Pf_Nek_p_or_sqrt chiImport.sqrtStarkGenerator =
          chiImport.h_p_CT ∧
        chiImport.Sigma_NekCT = 1 ∧
        chiImport.T_E1 ∧ chiImport.T_E2 ∧ chiImport.T_E3 ∧
        chiImport.T_E4 ∧ chiImport.T_E5 ∧ chiImport.T_E6 ∧
        chiImport.T_E7 ∧ chiImport.T_E8 := by
  rcases chiImport with
    ⟨T_E1, hT_E1, T_E2, hT_E2, T_E3, hT_E3, T_E4, hT_E4,
      T_E5, hT_E5, T_E6, hT_E6, T_E7, hT_E7, T_E8, hT_E8,
      Sigma_NekCT, hSigma_NekCT, SqrtFittCTDomain, VctpCodomain,
      sqrtStarkGenerator, h_p_CT, canonicalPfaffian, canonicalProperty,
      hCanonicalProperty, hPfaffianSends⟩
  exact
    ⟨canonicalPfaffian, hCanonicalProperty, hPfaffianSends, hSigma_NekCT, hT_E1,
      hT_E2, hT_E3, hT_E4, hT_E5, hT_E6, hT_E7, hT_E8⟩

end SixBirdsBSD.Closure.ChiCTp
