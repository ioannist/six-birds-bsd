import SixBirdsBSD.Apparatus.KappaNormalization
import SixBirdsBSD.Closure.AORPrimitives
import SixBirdsBSD.Closure.Imports
import SixBirdsBSD.Closure.RecognitionSources
import SixBirdsBSD.Closure.SelShell

/-!
"BSD as an AOR instance" for the closure axis.

The AOR reading is non-eliminative: recognition-source records are
reclassified as bridged discharge atoms, while the open arithmetic is
not erased.
-/

namespace SixBirdsBSD.Closure.AORInstance

universe u uPD vPD sPD uSP vSP sSP uGZ vGZ

/-- Wrapper for the BSD AOR-instance carrier attached to `Sel!_BSD`. -/
structure SelAORInstance
    {EPD : Type uPD} {LPD : Type vPD}
    {SPD : Type sPD}
    {ESP : Type uSP} {LSP : Type vSP} {SSP : Type sSP}
    {EGZ : Type uGZ}
    {SGZ : Type vGZ} {zGZ : SGZ} {subGZ mulGZ : SGZ → SGZ → SGZ}
    (shell : SixBirdsBSD.Closure.SelShell.selBSDShell)
    (gPD : SixBirdsBSD.Closure.RecognitionSources.gammaPadicDescent EPD LPD SPD)
    (gSP : SixBirdsBSD.Closure.RecognitionSources.gammaShaPersistence ESP LSP SSP)
    (gGZ :
      SixBirdsBSD.Closure.RecognitionSources.gammaHigherGZFixity EGZ SGZ zGZ
        subGZ mulGZ)
    (chiImports : SixBirdsBSD.Closure.Imports.chiCTpImport)
    (aEImports : SixBirdsBSD.Closure.Imports.aEImport)
    (beilinsonImports : SixBirdsBSD.Closure.Imports.beilinsonImport) where
  carrier : SixBirdsBSD.Closure.AORPrimitives.AORInstanceCarrier

/-- The BSD AOR-instance object attached to `Sel!_BSD`. -/
def aorSelInstance
    {EPD : Type uPD} {LPD : Type vPD}
    {SPD : Type sPD}
    {ESP : Type uSP} {LSP : Type vSP} {SSP : Type sSP}
    {EGZ : Type uGZ}
    {SGZ : Type vGZ} {zGZ : SGZ} {subGZ mulGZ : SGZ → SGZ → SGZ}
    (shell : SixBirdsBSD.Closure.SelShell.selBSDShell)
    (gPD : SixBirdsBSD.Closure.RecognitionSources.gammaPadicDescent EPD LPD SPD)
    (gSP : SixBirdsBSD.Closure.RecognitionSources.gammaShaPersistence ESP LSP SSP)
    (gGZ :
      SixBirdsBSD.Closure.RecognitionSources.gammaHigherGZFixity EGZ SGZ zGZ
        subGZ mulGZ)
    (chiImports : SixBirdsBSD.Closure.Imports.chiCTpImport)
    (aEImports : SixBirdsBSD.Closure.Imports.aEImport)
    (beilinsonImports : SixBirdsBSD.Closure.Imports.beilinsonImport) :
    SelAORInstance shell gPD gSP gGZ chiImports aEImports beilinsonImports :=
  let forcedRecognitionSecondaries :=
    [ SixBirdsBSD.Closure.AORPrimitives.ResidualType.role,
      SixBirdsBSD.Closure.AORPrimitives.ResidualType.target,
      SixBirdsBSD.Closure.AORPrimitives.ResidualType.transport,
      SixBirdsBSD.Closure.AORPrimitives.ResidualType.limit ]
  let shellConstructionAtom : SixBirdsBSD.Closure.AORPrimitives.DischargeAtom :=
    { primary := by
        let _formedLayer := shell.FormedLayer
        exact SixBirdsBSD.Closure.AORPrimitives.ResidualType.presentation
      forced_secondaries := []
      status := SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.by_construction }
  let kappaNormalizationAtom : SixBirdsBSD.Closure.AORPrimitives.DischargeAtom :=
    { primary := by
        let _scalar := shell.Scalar
        exact SixBirdsBSD.Closure.AORPrimitives.ResidualType.transport
      forced_secondaries := []
      status := SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.by_construction }
  let chiImportAtom : SixBirdsBSD.Closure.AORPrimitives.DischargeAtom :=
    { primary := by
        let _sign := chiImports.Sigma_NekCT
        exact SixBirdsBSD.Closure.AORPrimitives.ResidualType.source
      forced_secondaries := []
      status := SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.approved_other }
  let aEImportAtom : SixBirdsBSD.Closure.AORPrimitives.DischargeAtom :=
    { primary := by
        let _targetCategory := aEImports.TargetCategory
        exact SixBirdsBSD.Closure.AORPrimitives.ResidualType.source
      forced_secondaries := []
      status := SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.approved_other }
  let beilinsonImportAtom : SixBirdsBSD.Closure.AORPrimitives.DischargeAtom :=
    { primary := by
        let _rank := beilinsonImports.rank
        exact SixBirdsBSD.Closure.AORPrimitives.ResidualType.source
      forced_secondaries := []
      status := SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.approved_other }
  let gammaPDAtom : SixBirdsBSD.Closure.AORPrimitives.DischargeAtom :=
    { primary := by
        let _p := gPD.p
        exact SixBirdsBSD.Closure.AORPrimitives.ResidualType.source
      forced_secondaries := forcedRecognitionSecondaries
      status := SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.bridged }
  let gammaSPAtom : SixBirdsBSD.Closure.AORPrimitives.DischargeAtom :=
    { primary := by
        let _p := gSP.p
        exact SixBirdsBSD.Closure.AORPrimitives.ResidualType.source
      forced_secondaries := forcedRecognitionSecondaries
      status := SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.bridged }
  let gammaGZAtom : SixBirdsBSD.Closure.AORPrimitives.DischargeAtom :=
    { primary := by
        let _rank := gGZ.analyticRank
        exact SixBirdsBSD.Closure.AORPrimitives.ResidualType.source
      forced_secondaries := forcedRecognitionSecondaries
      status := SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.bridged }
  { carrier :=
    { carrier_id := "Sel!_BSD"
      observations := ["Strong-BSD scalar readout", "BSD residual shell"]
      routes := ["SelShell.piBSDIffStrongBSD", "SelShell.masterTheoremApplicability",
        "SelShell.compositeSignature"]
      sources := ["Gamma_BSD^padic-descent", "Gamma_BSD^Sha-persistence",
        "Gamma_BSD^higher-GZ-fixity"]
      interfaces := ["Sel!_BSD construction", "kappa_r normalization",
        "chi_CT,p/A_E/Beilinson approved_other imports"]
      constraints := ["refinement-stable membrane", "audit-closed presentation",
        "non-eliminative recognition-source reclassification"]
      discharges :=
        [ shellConstructionAtom, kappaNormalizationAtom, chiImportAtom,
          aEImportAtom, beilinsonImportAtom, gammaPDAtom, gammaSPAtom,
          gammaGZAtom ]
      nonclaims :=
        [ "AOR-instance reading is non-eliminative",
          "Recognition records are reclassified, not discharged of open arithmetic",
          "T_E12_REFINED remains open",
          "T_BAD_REFINED remains open" ]
      nonclaims_nonempty := by decide } }

/-- Mechanical AOR membership components for the BSD instance. -/
def mechanicalRecordDischarge
    (chiImports : SixBirdsBSD.Closure.Imports.chiCTpImport)
    (aEImports : SixBirdsBSD.Closure.Imports.aEImport)
    (beilinsonImports : SixBirdsBSD.Closure.Imports.beilinsonImport)
    (Omega_E Reg_r Tam_E kappa_r sha_over_tors_sq : Int) : Prop :=
  let common := Omega_E * Reg_r * Tam_E
  let cascadeForm := kappa_r * common
  let standardBSDForm := sha_over_tors_sq * common
  let selConstructionAtom : SixBirdsBSD.Closure.AORPrimitives.DischargeAtom :=
    { primary := SixBirdsBSD.Closure.AORPrimitives.ResidualType.presentation
      forced_secondaries := []
      status := SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.by_construction }
  let kappaNormalizationAtom : SixBirdsBSD.Closure.AORPrimitives.DischargeAtom :=
    { primary := SixBirdsBSD.Closure.AORPrimitives.ResidualType.transport
      forced_secondaries := []
      status := SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.by_construction }
  let importCitationAtom : SixBirdsBSD.Closure.AORPrimitives.DischargeAtom :=
    { primary := SixBirdsBSD.Closure.AORPrimitives.ResidualType.source
      forced_secondaries := []
      status := SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.approved_other }
  selConstructionAtom.status =
      SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.by_construction ∧
    kappaNormalizationAtom.status =
      SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.by_construction ∧
    importCitationAtom.status =
      SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.approved_other ∧
    (cascadeForm = standardBSDForm ↔ kappa_r = sha_over_tors_sq) ∧
    chiImports.Sigma_NekCT = 1 ∧
    aEImports.nekovarSelmerComplexWithIntrinsicCasselsTatePairing ∧
    aEImports.burnsFlachMaciasSanoNekovarAESelFormulation ∧
    aEImports.pairingBilinearOrCategorical ∧
    2 ≤ beilinsonImports.rank ∧
    beilinsonImports.determinantLValueComparison

/-- Recognition-source AOR components for the three BSD recognition carriers. -/
def recognitionDischarge
    {EPD : Type uPD} {LPD : Type vPD}
    {SPD : Type sPD}
    {ESP : Type uSP} {LSP : Type vSP} {SSP : Type sSP}
    {EGZ : Type uGZ}
    {SGZ : Type vGZ} {zGZ : SGZ} {subGZ mulGZ : SGZ → SGZ → SGZ}
    (gPD : SixBirdsBSD.Closure.RecognitionSources.gammaPadicDescent EPD LPD SPD)
    (gSP : SixBirdsBSD.Closure.RecognitionSources.gammaShaPersistence ESP LSP SSP)
    (gGZ :
      SixBirdsBSD.Closure.RecognitionSources.gammaHigherGZFixity EGZ SGZ zGZ
        subGZ mulGZ) : Prop :=
  let forced :=
    [ SixBirdsBSD.Closure.AORPrimitives.ResidualType.role,
      SixBirdsBSD.Closure.AORPrimitives.ResidualType.target,
      SixBirdsBSD.Closure.AORPrimitives.ResidualType.transport,
      SixBirdsBSD.Closure.AORPrimitives.ResidualType.limit ]
  let gammaPDAtom : SixBirdsBSD.Closure.AORPrimitives.DischargeAtom :=
    { primary := SixBirdsBSD.Closure.AORPrimitives.ResidualType.source
      forced_secondaries := forced
      status := SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.bridged }
  let gammaSPAtom : SixBirdsBSD.Closure.AORPrimitives.DischargeAtom :=
    { primary := SixBirdsBSD.Closure.AORPrimitives.ResidualType.source
      forced_secondaries := forced
      status := SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.bridged }
  let gammaGZAtom : SixBirdsBSD.Closure.AORPrimitives.DischargeAtom :=
    { primary := SixBirdsBSD.Closure.AORPrimitives.ResidualType.source
      forced_secondaries := forced
      status := SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.bridged }
  gammaPDAtom.primary = SixBirdsBSD.Closure.AORPrimitives.ResidualType.source ∧
    gammaPDAtom.forced_secondaries = forced ∧
    gammaPDAtom.status = SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.bridged ∧
    gammaPDAtom.status ≠ SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.zero ∧
    gammaSPAtom.primary = SixBirdsBSD.Closure.AORPrimitives.ResidualType.source ∧
    gammaSPAtom.forced_secondaries = forced ∧
    gammaSPAtom.status = SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.bridged ∧
    gammaSPAtom.status ≠ SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.zero ∧
    gammaGZAtom.primary = SixBirdsBSD.Closure.AORPrimitives.ResidualType.source ∧
    gammaGZAtom.forced_secondaries = forced ∧
    gammaGZAtom.status = SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.bridged ∧
    gammaGZAtom.status ≠ SixBirdsBSD.Closure.AORPrimitives.DischargeStatus.zero ∧
    gPD.localDescentCongruenceModZpUnits ∧
    gSP.C_loc_III_congruent_c_p_mod_ZpUnits ∧
    gGZ.higherGZFixity

/--
The mechanical membership components discharge by construction or as an
approved-other external citation chain.
-/
theorem aorMechanicalRecords
    (chiImports : SixBirdsBSD.Closure.Imports.chiCTpImport)
    (aEImports : SixBirdsBSD.Closure.Imports.aEImport)
    (beilinsonImports : SixBirdsBSD.Closure.Imports.beilinsonImport)
    (Omega_E Reg_r Tam_E kappa_r sha_over_tors_sq : Int)
    (h_common : Omega_E * Reg_r * Tam_E ≠ 0) :
    mechanicalRecordDischarge chiImports aEImports beilinsonImports Omega_E
      Reg_r Tam_E kappa_r sha_over_tors_sq := by
  rcases chiImports with
    ⟨T_E1, hT_E1, T_E2, hT_E2, T_E3, hT_E3, T_E4, hT_E4,
      T_E5, hT_E5, T_E6, hT_E6, T_E7, hT_E7, T_E8, hT_E8,
      Sigma_NekCT, hSigma_NekCT⟩
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
  have hkappa :=
    SixBirdsBSD.Apparatus.KappaNormalization.kappaRNormalizationEquivalence
      Omega_E Reg_r Tam_E kappa_r sha_over_tors_sq h_common
  dsimp [mechanicalRecordDischarge]
  exact
    ⟨rfl, rfl, rfl, hkappa, hSigma_NekCT,
      hNekovarSelmerComplexWithIntrinsicCasselsTatePairing,
      hBurnsFlachMaciasSanoNekovarAESelFormulation,
      hPairingBilinearOrCategorical, hrank, hDeterminantLValueComparison⟩

/--
The three BSD recognition sources discharge as bridged source records,
with forced role/target/transport/limit secondaries.
-/
theorem aorRecognitionDischarge
    {EPD : Type uPD} {LPD : Type vPD}
    {SPD : Type sPD}
    {ESP : Type uSP} {LSP : Type vSP} {SSP : Type sSP}
    {EGZ : Type uGZ}
    {SGZ : Type vGZ} {zGZ : SGZ} {subGZ mulGZ : SGZ → SGZ → SGZ}
    (gPD : SixBirdsBSD.Closure.RecognitionSources.gammaPadicDescent EPD LPD SPD)
    (gSP : SixBirdsBSD.Closure.RecognitionSources.gammaShaPersistence ESP LSP SSP)
    (gGZ :
      SixBirdsBSD.Closure.RecognitionSources.gammaHigherGZFixity EGZ SGZ zGZ
        subGZ mulGZ) :
    recognitionDischarge gPD gSP gGZ := by
  dsimp [recognitionDischarge]
  exact
    ⟨rfl, rfl, rfl, by decide, rfl, rfl, rfl, by decide, rfl, rfl, rfl,
      by decide, gPD.localDescentCongruenceModZpUnits_proof,
      gSP.C_loc_III_congruent_c_p_mod_ZpUnits_proof,
      gGZ.higherGZFixity_proof⟩

/--
The BSD AOR instance is refinement-stable audit-closed under the
declared non-eliminative presentation.
-/
theorem aorInstance
    {EPD : Type uPD} {LPD : Type vPD}
    {SPD : Type sPD}
    {ESP : Type uSP} {LSP : Type vSP} {SSP : Type sSP}
    {EGZ : Type uGZ}
    {SGZ : Type vGZ} {zGZ : SGZ} {subGZ mulGZ : SGZ → SGZ → SGZ}
    (shell : SixBirdsBSD.Closure.SelShell.selBSDShell)
    (gPD : SixBirdsBSD.Closure.RecognitionSources.gammaPadicDescent EPD LPD SPD)
    (gSP : SixBirdsBSD.Closure.RecognitionSources.gammaShaPersistence ESP LSP SSP)
    (gGZ :
      SixBirdsBSD.Closure.RecognitionSources.gammaHigherGZFixity EGZ SGZ zGZ
        subGZ mulGZ)
    (chiImports : SixBirdsBSD.Closure.Imports.chiCTpImport)
    (aEImports : SixBirdsBSD.Closure.Imports.aEImport)
    (beilinsonImports : SixBirdsBSD.Closure.Imports.beilinsonImport)
    (Omega_E Reg_r Tam_E kappa_r sha_over_tors_sq : Int)
    (h_common : Omega_E * Reg_r * Tam_E ≠ 0) :
    SixBirdsBSD.Closure.AORPrimitives.RefStableAOR
      (aorSelInstance shell gPD gSP gGZ chiImports aEImports
        beilinsonImports).carrier ∧
      mechanicalRecordDischarge chiImports aEImports beilinsonImports Omega_E
        Reg_r Tam_E kappa_r sha_over_tors_sq ∧
      recognitionDischarge gPD gSP gGZ := by
  have hMechanical :=
    aorMechanicalRecords chiImports aEImports beilinsonImports Omega_E Reg_r
      Tam_E kappa_r sha_over_tors_sq h_common
  have hRecognition := aorRecognitionDischarge gPD gSP gGZ
  have hMembership :
      SixBirdsBSD.Closure.AORPrimitives.RefStableAOR
        (aorSelInstance shell gPD gSP gGZ chiImports aEImports
          beilinsonImports).carrier := by
    apply SixBirdsBSD.Closure.AORPrimitives.refStableOfClosed
    unfold SixBirdsBSD.Closure.AORPrimitives.ClosedAORRegister
    constructor
    · simp [aorSelInstance]
    · intro atom hatom
      simp [aorSelInstance] at hatom
      rcases hatom with h | h | h | h | h | h | h | h
      all_goals
        subst_vars
        simp [SixBirdsBSD.Closure.AORPrimitives.ClosedStatus]
  exact ⟨hMembership, hMechanical, hRecognition⟩

end SixBirdsBSD.Closure.AORInstance
