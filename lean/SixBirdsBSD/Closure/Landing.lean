import SixBirdsBSD.Closure.Imports
import SixBirdsBSD.Closure.RecognitionSources
import SixBirdsBSD.Closure.SelShell

/-!
The Phase-9 conditional Strong-BSD landing for the closure axis.

The theorem in this module is explicitly conditional on the shell,
recognition carriers, imported theorem records, and the Foundations-I
closure assumption. It routes through the SelShell theorems rather than
proving any unconditional classical BSD statement.
-/

namespace SixBirdsBSD.Closure.Landing

universe uPD vPD wPD xPD yPD
universe uSP vSP wSP xSP ySP
universe uGZ vGZ
universe uAE vAE wAE xAE
universe uBI vBI wBI

/--
Conditional Strong BSD within the Six Birds closure discipline. From the
`Sel!_BSD` shell, the explicit higher-GZ recognition carrier, the
remaining BSD recognition carriers, the three import structures, and
the Foundations-I closure assumption, the scalar Strong-BSD identity is
routed through the SelShell higher-GZ helper, master-applicability, and
composite signature theorems.
-/
theorem strongBSDConditionalWithAudits
    {EPD : Type uPD} {LPD : Type vPD}
    {ESP : Type uSP} {LSP : Type vSP} {EGZ : Type uGZ}
    (shell : SixBirdsBSD.Closure.SelShell.selBSDShell)
    (closureAssumption : SixBirdsBSD.F1ClosureOp shell.FormedLayer)
    (hClosureAssumption : closureAssumption = shell.closureAssumption)
    (gPD :
      SixBirdsBSD.Closure.RecognitionSources.gammaPadicDescent EPD LPD
        shell.Scalar)
    (gSP :
      SixBirdsBSD.Closure.RecognitionSources.gammaShaPersistence ESP LSP
        shell.Scalar)
    (gGZ :
      SixBirdsBSD.Closure.RecognitionSources.gammaHigherGZFixity EGZ
        shell.Scalar shell.zero shell.sub shell.mul)
    (hLderiv :
      gGZ.L_derivative_over_factorial =
        shell.L_derivative_over_factorial)
    (hReg : gGZ.Reg_NT_E = shell.Reg_NT)
    (hOmega : gGZ.Omega_E = shell.Omega_E)
    (hTam : gGZ.Tam_E = shell.Tam)
    (hKappa :
      gGZ.kappa_r_E = shell.div shell.ShaCard shell.torsionSquared)
    (hRhs :
      gGZ.rhsRegulatorProduct =
        shell.mul
          (shell.mul (shell.mul gGZ.kappa_r_E gGZ.Reg_NT_E) gGZ.Omega_E)
          gGZ.Tam_E)
    (hSha : gSP.shaFactor = shell.ShaCard)
    (hTamFac : gPD.tamFactor = shell.Tam)
    (cancellation : SixBirdsBSD.Closure.SelShell.FactorCancellation shell)
    (chiImports : SixBirdsBSD.Closure.Imports.chiCTpImport)
    (aEImports :
      SixBirdsBSD.Closure.Imports.aEImport.{uAE, vAE, wAE, xAE})
    (beilinsonImports :
      SixBirdsBSD.Closure.Imports.beilinsonImport.{uBI, vBI, wBI}) :
    shell.L_derivative_over_factorial = shell.strongBSDRightSide ∧
      closureAssumption = shell.closureAssumption ∧
      (shell.masterTheoremApplies ∧ shell.smuggleAuditPasses ∧
        (gPD.f2DescentRepairMinimalCoarsening ∧
          gPD.f3HolonomyMemoryRouteResidue ∧ gPD.f4LocalGlobal) ∧
        (gSP.f19ObjectPersistence ∧ gSP.f21ReflexiveNonclosure ∧
          gSP.f29PresentationInvariance) ∧
        (gGZ.f14DualityFixity ∧ gGZ.f27ConservationAsOrbitDescent ∧
          gGZ.f40AnomalySymmetryObstruction)) ∧
      (shell.compositeOperationalPredicate ∧
        gPD.stage6_FP_trace_ii ∧ gPD.stage6_SAU_trace_iii ∧
        gPD.stage6_VDE_trace_ii ∧
        gSP.stage6_FP_trace_ii ∧ gSP.stage6_SAU_trace_iii ∧
        gSP.stage6_VDE_trace_ii ∧
        gGZ.stage6_FP_trace_ii ∧ gGZ.stage6_SAU_trace_iii ∧
        gGZ.stage6_VDE_trace_ii ∧
        shell.compositeComputable ∧ shell.compositeFalsifiable ∧
        shell.genuineDependenceOnFormedBSDLayerData ∧
        (∀ Sha' : shell.Scalar, Sha' ≠ gSP.shaFactor →
          shell.div
              (shell.mul (shell.mul (shell.mul Sha' gGZ.Reg_NT_E)
                shell.Omega_E) gPD.tamFactor)
              shell.torsionSquared ≠
            shell.strongBSDRightSide) ∧
        (∀ Reg' : shell.Scalar, Reg' ≠ gGZ.Reg_NT_E →
          shell.div
              (shell.mul (shell.mul (shell.mul gSP.shaFactor Reg')
                shell.Omega_E) gPD.tamFactor)
              shell.torsionSquared ≠
            shell.strongBSDRightSide) ∧
        (∀ Tam' : shell.Scalar, Tam' ≠ gPD.tamFactor →
          shell.div
              (shell.mul (shell.mul (shell.mul gSP.shaFactor gGZ.Reg_NT_E)
                shell.Omega_E) Tam')
              shell.torsionSquared ≠
            shell.strongBSDRightSide)) ∧
      (chiImports.Sigma_NekCT = 1 ∧
        chiImports.T_E1 ∧ chiImports.T_E2 ∧ chiImports.T_E3 ∧
        chiImports.T_E4 ∧ chiImports.T_E5 ∧ chiImports.T_E6 ∧
        chiImports.T_E7 ∧ chiImports.T_E8) ∧
      (aEImports.nekovarSelmerComplexWithIntrinsicCasselsTatePairing ∧
        aEImports.burnsFlachMaciasSanoNekovarAESelFormulation ∧
        aEImports.pairingBilinearOrCategorical) ∧
      (2 ≤ beilinsonImports.rank ∧
        beilinsonImports.determinantLValueComparison) := by
  have hResidualZero :=
    SixBirdsBSD.Closure.SelShell.gzFixityForcesResidualZero shell gGZ
      hLderiv hReg hOmega hTam hKappa hRhs
  have hStrongBSD :
      shell.L_derivative_over_factorial = shell.strongBSDRightSide :=
    (SixBirdsBSD.Closure.SelShell.piBSDIffStrongBSD shell).mp hResidualZero
  have hMaster :=
    SixBirdsBSD.Closure.SelShell.masterTheoremApplicability shell gPD gSP gGZ
  have hComposite :=
    SixBirdsBSD.Closure.SelShell.compositeSignature shell gPD gSP gGZ
      hSha hReg hTamFac cancellation
  rcases chiImports with
    ⟨T_E1, hT_E1, T_E2, hT_E2, T_E3, hT_E3, T_E4, hT_E4,
      T_E5, hT_E5, T_E6, hT_E6, T_E7, hT_E7, T_E8, hT_E8,
      Sigma_NekCT, hSigma_NekCT, SqrtFittCTDomain, VctpCodomain,
      sqrtStarkGenerator, h_p_CT, canonicalPfaffian, canonicalProperty,
      hCanonicalProperty, hPfaffianSends⟩
  rcases aEImports with
    ⟨TargetCategory, Hom, SelmerComplex, PairingTarget, pairing,
      nekovarSelmerComplexWithIntrinsicCasselsTatePairing,
      hNekovarSelmerComplexWithIntrinsicCasselsTatePairing,
      burnsFlachMaciasSanoNekovarAESelFormulation,
      hBurnsFlachMaciasSanoNekovarAESelFormulation,
      pairingBilinearOrCategorical, hPairingBilinearOrCategorical⟩
  rcases beilinsonImports with
    ⟨rank, hrank, ArchimedeanRegulator, DeterminantLine, LValueSide,
      regulatorToDeterminantLine, determinantLValueComparison,
      hDeterminantLValueComparison⟩
  exact
    ⟨hStrongBSD, hClosureAssumption, hMaster, hComposite,
      ⟨hSigma_NekCT, hT_E1, hT_E2, hT_E3, hT_E4, hT_E5, hT_E6,
        hT_E7, hT_E8⟩,
      ⟨hNekovarSelmerComplexWithIntrinsicCasselsTatePairing,
        hBurnsFlachMaciasSanoNekovarAESelFormulation,
        hPairingBilinearOrCategorical⟩,
      ⟨hrank, hDeterminantLValueComparison⟩⟩

/-- Conditional scalar BSD in all analytic ranks, from the quantified,
curve-matched recognition predicate. The rank-at-least-two comparison import
is required only in that rank range and is tied to the shell's rank.
The closure operator and imports remain explicit records, not a proof that an
arbitrary idempotent endomorphism forces an arithmetic residual to vanish. -/
theorem strongBSDConditional
    (shell : SixBirdsBSD.Closure.SelShell.selBSDShell)
    (closureAssumption : SixBirdsBSD.F1ClosureOp shell.FormedLayer)
    (hClosureAssumption : closureAssumption = shell.closureAssumption)
    (recognition : SixBirdsBSD.Closure.SelShell.piBSD shell)
    (chiImports : SixBirdsBSD.Closure.Imports.chiCTpImport)
    (aEImports : SixBirdsBSD.Closure.Imports.aEImport.{uAE, vAE, wAE, xAE})
    (beilinsonImports : 2 ≤ shell.analyticRank →
      { b : SixBirdsBSD.Closure.Imports.beilinsonImport.{uBI, vBI, wBI} //
        b.rank = shell.analyticRank }) :
    shell.L_derivative_over_factorial = shell.strongBSDRightSide ∧
      closureAssumption = shell.closureAssumption ∧
      chiImports.Sigma_NekCT = 1 ∧
      aEImports.pairingBilinearOrCategorical ∧
      (∀ hr : 2 ≤ shell.analyticRank,
        (beilinsonImports hr).val.determinantLValueComparison) := by
  exact ⟨SixBirdsBSD.Closure.SelShell.piBSDForcesStrongBSD shell recognition,
    hClosureAssumption, chiImports.Sigma_NekCT_eq_plus_one,
    aEImports.pairingBilinearOrCategorical_proof,
    fun hr => (beilinsonImports hr).val.determinantLValueComparison_proof⟩

end SixBirdsBSD.Closure.Landing
