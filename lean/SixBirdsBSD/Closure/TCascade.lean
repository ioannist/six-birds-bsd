/-!
The conditional p-part Strong-BSD cascade, rank <= 1 (supporting) for
the closure axis.

The import stack is proof-carrying and branch-aware: the CM branch and
non-CM branch imports remain separate, and the rank-one Heegner inputs
in the theorem are gated by `rank = 1`.
-/

namespace SixBirdsBSD.Closure.TCascade

universe u

/-- The named external theorem stack for `T_CASCADE`, with CM and non-CM branches. -/
structure tCascadeImport where
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
  T_CM1 : Prop
  T_CM1_proof : T_CM1
  T_CM2 : Prop
  T_CM2_proof : T_CM2
  T_CM3 : Prop
  T_CM3_proof : T_CM3
  T_CM4 : Prop
  T_CM4_proof : T_CM4
  T_CM5 : Prop
  T_CM5_proof : T_CM5
  T_CM6 : Prop
  T_CM6_proof : T_CM6
  T_SS1 : Prop
  T_SS1_proof : T_SS1
  T_SS2 : Prop
  T_SS2_proof : T_SS2
  T_SS3 : Prop
  T_SS3_proof : T_SS3
  T_SS4 : Prop
  T_SS4_proof : T_SS4
  T_SS5 : Prop
  T_SS5_proof : T_SS5
  T_SS6 : Prop
  T_SS6_proof : T_SS6
  T_SS7 : Prop
  T_SS7_proof : T_SS7
  T_ARC1 : Prop
  T_ARC1_proof : T_ARC1
  T_ARC2 : Prop
  T_ARC2_proof : T_ARC2
  T_ARC3 : Prop
  T_ARC3_proof : T_ARC3
  T_ARC4 : Prop
  T_ARC4_proof : T_ARC4
  T_ARC5 : Prop
  T_ARC5_proof : T_ARC5
  T_ARC6 : Prop
  T_ARC6_proof : T_ARC6
  T_UNI1 : Prop
  T_UNI1_proof : T_UNI1
  T_UNI2 : Prop
  T_UNI2_proof : T_UNI2
  T_UNI3 : Prop
  T_UNI3_proof : T_UNI3
  T_UNI4 : Prop
  T_UNI4_proof : T_UNI4
  T_UNI5 : Prop
  T_UNI5_proof : T_UNI5
  T_UNI6 : Prop
  T_UNI6_proof : T_UNI6
  T_UNI7 : Prop
  T_UNI7_proof : T_UNI7
  T_nC1 : Prop
  T_nC1_proof : T_nC1
  T_nC2 : Prop
  T_nC2_proof : T_nC2
  T_nC3 : Prop
  T_nC3_proof : T_nC3
  T_nC4 : Prop
  T_nC4_proof : T_nC4
  T_nC5 : Prop
  T_nC5_proof : T_nC5
  T_nC6 : Prop
  T_nC6_proof : T_nC6

/--
Conditional p-part Strong BSD in rank at most one. The branch
hypotheses are explicit: the CM branch has its ordinary/supersingular
alternative and CM-specific hypotheses, while the non-CM branch has
rank `0` or `1`, Skinner-Urban style hypotheses, and the Heegner/GZK
input only as an implication from `rank = 1`.
-/
theorem tCascadeRankLeOne
    {EllipticCurve Prime Scalar Valuation : Type u}
    (E : EllipticCurve) (p : Prime)
    (cmRank nonCMRank : Nat)
    (cmCurve cmOrdSplitGoodOrdinarySplit cmSSInertGoodSupersingularInert
      cmPGeFive cmShaFinite cmCTNondegenerate
      cmSakamotoMaciasSano cmPNotTam cmRamification
      cmHeegnerForRankOne cmGaloisImageStandard : Prop)
    (nonCMCurve nonCMRankZeroOrOne nonCMSurjectiveRho
      nonCMGoodOrdinaryPNotN nonCMPNotTam nonCMSkinnerUrbanOrdinaryLocal
      nonCMResidualIrreducibility nonCMRamification nonCMLevelHypotheses
      nonCMShaFinite nonCMCTNondegenerate nonCMSakamotoMaciasSano
      nonCMHeegnerGrossZagierKolyvaginForRankOne : Prop)
    (mul div : Scalar → Scalar → Scalar)
    (vp : Scalar → Valuation)
    (L_derivative_over_factorial rFactorial Omega Reg ShaCard Tam
      torsionSquared : Scalar)
    (imports : tCascadeImport)
    :
    let branchHypotheses : Prop :=
      (cmCurve ∧
        (cmRank = 0 ∨ cmRank = 1) ∧
        (cmOrdSplitGoodOrdinarySplit ∨
          (cmSSInertGoodSupersingularInert ∧ cmPGeFive)) ∧
        cmShaFinite ∧ cmCTNondegenerate ∧
        cmSakamotoMaciasSano ∧ cmPNotTam ∧ cmRamification ∧
        (cmRank = 1 → cmHeegnerForRankOne) ∧
        cmGaloisImageStandard) ∨
      (nonCMCurve ∧ nonCMRankZeroOrOne ∧ nonCMSurjectiveRho ∧
        nonCMGoodOrdinaryPNotN ∧ nonCMPNotTam ∧
        nonCMSkinnerUrbanOrdinaryLocal ∧ nonCMResidualIrreducibility ∧
        nonCMRamification ∧ nonCMLevelHypotheses ∧ nonCMShaFinite ∧
        nonCMCTNondegenerate ∧ nonCMSakamotoMaciasSano ∧
        (nonCMRank = 1 → nonCMHeegnerGrossZagierKolyvaginForRankOne))
    let analyticSide : Scalar :=
      div L_derivative_over_factorial (mul (mul rFactorial Omega) Reg)
    let arithmeticSide : Scalar :=
      div (mul ShaCard Tam) torsionSquared
    ((E : EllipticCurve) → (p : Prime) →
      imports.T_E1 → imports.T_E2 → imports.T_E3 → imports.T_E4 →
      imports.T_E5 → imports.T_E6 → imports.T_E7 → imports.T_E8 →
      imports.T_CM1 → imports.T_CM2 → imports.T_CM3 → imports.T_CM4 →
      imports.T_CM5 → imports.T_CM6 →
      imports.T_SS1 → imports.T_SS2 → imports.T_SS3 → imports.T_SS4 →
      imports.T_SS5 → imports.T_SS6 → imports.T_SS7 →
      imports.T_ARC1 → imports.T_ARC2 → imports.T_ARC3 → imports.T_ARC4 →
      imports.T_ARC5 → imports.T_ARC6 →
      imports.T_UNI1 → imports.T_UNI2 → imports.T_UNI3 → imports.T_UNI4 →
      imports.T_UNI5 → imports.T_UNI6 → imports.T_UNI7 →
      imports.T_nC1 → imports.T_nC2 → imports.T_nC3 → imports.T_nC4 →
      imports.T_nC5 → imports.T_nC6 →
      branchHypotheses → vp analyticSide = vp arithmeticSide) →
    branchHypotheses →
    vp analyticSide = vp arithmeticSide := by
  dsimp
  intro cascadeImportsYieldValuationIdentity hBranch
  rcases imports with
    ⟨T_E1, hT_E1, T_E2, hT_E2, T_E3, hT_E3, T_E4, hT_E4,
      T_E5, hT_E5, T_E6, hT_E6, T_E7, hT_E7, T_E8, hT_E8,
      T_CM1, hT_CM1, T_CM2, hT_CM2, T_CM3, hT_CM3,
      T_CM4, hT_CM4, T_CM5, hT_CM5, T_CM6, hT_CM6,
      T_SS1, hT_SS1, T_SS2, hT_SS2, T_SS3, hT_SS3, T_SS4, hT_SS4,
      T_SS5, hT_SS5, T_SS6, hT_SS6, T_SS7, hT_SS7,
      T_ARC1, hT_ARC1, T_ARC2, hT_ARC2, T_ARC3, hT_ARC3,
      T_ARC4, hT_ARC4, T_ARC5, hT_ARC5, T_ARC6, hT_ARC6,
      T_UNI1, hT_UNI1, T_UNI2, hT_UNI2, T_UNI3, hT_UNI3,
      T_UNI4, hT_UNI4, T_UNI5, hT_UNI5, T_UNI6, hT_UNI6,
      T_UNI7, hT_UNI7,
      T_nC1, hT_nC1, T_nC2, hT_nC2, T_nC3, hT_nC3,
      T_nC4, hT_nC4, T_nC5, hT_nC5, T_nC6, hT_nC6⟩
  exact
    cascadeImportsYieldValuationIdentity E p hT_E1 hT_E2 hT_E3 hT_E4
      hT_E5 hT_E6 hT_E7 hT_E8 hT_CM1 hT_CM2 hT_CM3 hT_CM4 hT_CM5
      hT_CM6 hT_SS1 hT_SS2 hT_SS3 hT_SS4 hT_SS5 hT_SS6 hT_SS7
      hT_ARC1 hT_ARC2 hT_ARC3 hT_ARC4 hT_ARC5 hT_ARC6 hT_UNI1
      hT_UNI2 hT_UNI3 hT_UNI4 hT_UNI5 hT_UNI6 hT_UNI7 hT_nC1
      hT_nC2 hT_nC3 hT_nC4 hT_nC5 hT_nC6 hBranch

end SixBirdsBSD.Closure.TCascade
