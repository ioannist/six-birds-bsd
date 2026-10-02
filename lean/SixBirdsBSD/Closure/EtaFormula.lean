import SixBirdsBSD.Apparatus.SupportPrimeNoGo

/-!
The conditional overconvergent `eta`-formula (supporting) for the
closure axis.

This module keeps citation-labelled inputs as distinct proof-carrying
fields. The eta identity itself is an additional supplied certificate;
it is not derived from the citation-labelled proposition fields.
-/

namespace SixBirdsBSD.Closure.EtaFormula

universe u

/--
Certificate carrier for the overconvergent `eta` formula, kept under
its historical public name. Citation-labelled fields include Bellaiche Lemma 3.21,
Pollack-Stevens 2011, arXiv:2403.16076, Lang-Wake 2025
arXiv:2501.04162 as a distinct import, Lorenzini 1995, Ling 1997, and
the cascade-internal conjecture `C_B691`. `etaFormulaHolds` is separate
arithmetic content. The record does not prove that these named results
apply to the data or imply that certificate.
-/
structure etaPublishedImports {EllipticCurve : Type u} (E : EllipticCurve) (p : Nat) where
  prime : SixBirdsBSD.Apparatus.SupportPrimeNoGo.IsPrime p
  odd : p % 2 = 1
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
  zero : Scalar
  mul : Scalar → Scalar → Scalar
  pow : Scalar → Int → Scalar
  neg : Scalar → Scalar
  castNat : Nat → Scalar
  pScalar : Scalar
  pScalar_eq : pScalar = castNat p
  pScalar_nonzero : pScalar ≠ zero
  torsionCard : Nat
  torsionCard_positive : 0 < torsionCard
  torsionAbs : Scalar
  torsionAbs_eq : torsionAbs = castNat torsionCard
  torsionAbs_nonzero : torsionAbs ≠ zero
  beta : Scalar
  beta_nonzero : beta ≠ zero
  T_leading_Bellaiche : Scalar
  eta_p_E : Scalar
  ord_T_E_p : Int
  /-- A square relation, not a certificate of weight-two critical slope.
  Under v_p(p)=1 this forces slope 1/2; see `EtaApplicability`. -/
  betaSquareRelation : mul beta beta = neg pScalar
  etaFormulaHolds :
    eta_p_E =
      mul
        (mul (pow (mul pScalar torsionAbs) (ord_T_E_p - 1))
          (pow beta (-2)))
        T_leading_Bellaiche

/--
Conditional unified overconvergent eta formula at additive odd primes.
Under the Phase-7-S/T shallow additive odd-prime hypotheses, with
the supplied square relation `beta^2 = -p`, the eta value is
the explicit product
`(p * torsion)^(ord_T - 1) * beta^(-2) * T_leading_Bellaiche`.
-/
theorem ocEtaFormula
    {EllipticCurve : Type u}
    (E : EllipticCurve) (p : Nat)
    (phase7STShallowAdditiveOddPrimeScope : EllipticCurve → Nat → Prop)
    (_hScope : phase7STShallowAdditiveOddPrimeScope E p)
    (imports : etaPublishedImports E p)
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
  exact ⟨imports.etaFormulaHolds, imports.bellaicheLemma321_proof,
    imports.pollackStevens2011_proof, imports.arxiv2403_16076_proof,
    imports.langWake2025_arxiv2501_04162_proof, imports.lorenzini1995_proof,
    imports.ling1997_proof,
    imports.C_B691_cuspidal_layer_evaluation_nonzero_and_primitive_proof⟩

end SixBirdsBSD.Closure.EtaFormula
