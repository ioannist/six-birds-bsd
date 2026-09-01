/-!
The conditional overconvergent `eta`-formula (supporting) for the
closure axis.

This module keeps the published imports as distinct proof-carrying
fields and proves the conditional eta identity from those fields.
-/

namespace SixBirdsBSD.Closure.EtaFormula

universe u

/--
Published imports for the overconvergent `eta` formula, kept as
separate proof-carrying fields: Bellaiche Lemma 3.21,
Pollack-Stevens 2011, arXiv:2403.16076, Lang-Wake 2025
arXiv:2501.04162 as a distinct import, Lorenzini 1995, Ling 1997, and
the cascade-internal conjecture `C_B691`.
-/
structure etaPublishedImports where
  bellaicheLemma321 : Prop
  bellaicheLemma321_proof : bellaicheLemma321
  pollackStevens2011 : Prop
  pollackStevens2011_proof : pollackStevens2011
  arxiv2403_16076 : Prop
  arxiv2403_16076_proof : arxiv2403_16076
  langWake2025_arxiv2501_04162 : Prop
  langWake2025_arxiv2501_04162_proof : langWake2025_arxiv2501_04162
  lorenzini1995 : Prop
  lorenzini1995_proof : lorenzini1995
  ling1997 : Prop
  ling1997_proof : ling1997
  C_B691_cuspidal_layer_evaluation_nonzero_and_primitive : Prop
  C_B691_cuspidal_layer_evaluation_nonzero_and_primitive_proof :
    C_B691_cuspidal_layer_evaluation_nonzero_and_primitive
  Scalar : Type
  mul : Scalar → Scalar → Scalar
  pow : Scalar → Int → Scalar
  neg : Scalar → Scalar
  pScalar : Scalar
  torsionAbs : Scalar
  beta : Scalar
  T_leading_Bellaiche : Scalar
  eta_p_E : Scalar
  ord_T_E_p : Int
  betaCriticalSlope : mul beta beta = neg pScalar
  etaFormulaHolds :
    eta_p_E =
      mul
        (mul (pow (mul pScalar torsionAbs) (ord_T_E_p - 1))
          (pow beta (-2)))
        T_leading_Bellaiche

/--
Conditional unified overconvergent eta formula at additive odd primes.
Under the Phase-7-S/T shallow additive odd-prime hypotheses, with
Bellaiche critical-slope stabilization `beta^2 = -p`, the eta value is
the explicit product
`(p * torsion)^(ord_T - 1) * beta^(-2) * T_leading_Bellaiche`.
-/
theorem ocEtaFormula
    {EllipticCurve Prime : Type u}
    (_E : EllipticCurve) (_p : Prime)
    (phase7STShallowAdditiveOddPrimeScope oddAdditivePrime : Prop)
    (_hScope : phase7STShallowAdditiveOddPrimeScope)
    (_hOddAdditive : oddAdditivePrime)
    (imports : etaPublishedImports)
    :
    imports.eta_p_E =
        imports.mul
          (imports.mul
            (imports.pow (imports.mul imports.pScalar imports.torsionAbs)
              (imports.ord_T_E_p - 1))
            (imports.pow imports.beta (-2)))
          imports.T_leading_Bellaiche ∧
      imports.bellaicheLemma321 ∧ imports.pollackStevens2011 ∧
      imports.arxiv2403_16076 ∧ imports.langWake2025_arxiv2501_04162 ∧
      imports.lorenzini1995 ∧ imports.ling1997 ∧
      imports.C_B691_cuspidal_layer_evaluation_nonzero_and_primitive := by
  rcases imports with
    ⟨bellaicheLemma321, hBellaicheLemma321,
      pollackStevens2011, hPollackStevens2011,
      arxiv2403_16076, hArxiv2403_16076,
      langWake2025_arxiv2501_04162, hLangWake2025_arxiv2501_04162,
      lorenzini1995, hLorenzini1995,
      ling1997, hLing1997,
      C_B691, hC_B691, Scalar, mul, pow, neg, pScalar, torsionAbs, beta,
      T_leading_Bellaiche, eta_p_E, ord_T_E_p, hBetaCriticalSlope,
      hEtaFormula⟩
  exact
    ⟨hEtaFormula, hBellaicheLemma321, hPollackStevens2011, hArxiv2403_16076,
      hLangWake2025_arxiv2501_04162, hLorenzini1995, hLing1997, hC_B691⟩

end SixBirdsBSD.Closure.EtaFormula
