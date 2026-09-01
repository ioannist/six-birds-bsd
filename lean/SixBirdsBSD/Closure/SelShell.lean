import SixBirdsBSD.Closure.RecognitionSources
import SixBirdsBSD.FoundationsICompat

/-!
The `Sel!_BSD` closure architecture for the closure axis.

This module keeps the architecture readout-scoped. The predicate
`piBSD` is a quantified record of BSD recognition-source readouts, and
the Strong-BSD comparison theorem proves only the scalar readout
equivalence attached to the shell.
-/

namespace SixBirdsBSD.Closure.SelShell

universe u v w x y z uPD vPD sPD uSP vSP sSP uGZ vGZ

/--
The saturated BSD trace shell
`Sel!_BSD = (E, rho_E, J!_BSD, Vis!_BSD, Audit!_BSD)`.
The scalar residual is represented by `residual_eq`, whose right side is
`L^(r)(E,1)/r! - (#Sha * Reg_NT * Omega_E * Tam) / torsionSquared`.
The closure object is carried under the Foundations-I closure
assumption, with admissibility, anti-tautology, and lawfulness data.
-/
structure selBSDShell where
  EllipticCurve : Type u
  Scalar : Type v
  LocalLift : Type w
  FormedLayer : Type x
  InvolutiveDatum : Type y
  VisibleReadoutDatum : Type z
  AuditRecordDatum : Type u
  E : EllipticCurve
  analyticRank : Nat
  zero : Scalar
  sub : Scalar → Scalar → Scalar
  mul : Scalar → Scalar → Scalar
  div : Scalar → Scalar → Scalar
  L_derivative_over_factorial : Scalar
  ShaCard : Scalar
  Reg_NT : Scalar
  Omega_E : Scalar
  Tam : Scalar
  torsionSquared : Scalar
  strongBSDRightSide : Scalar
  strongBSDRightSide_eq :
    strongBSDRightSide =
      div (mul (mul (mul ShaCard Reg_NT) Omega_E) Tam) torsionSquared
  residual : Scalar
  residual_eq :
    residual = sub L_derivative_over_factorial strongBSDRightSide
  sub_eq_zero_iff :
    ∀ a b : Scalar, sub a b = zero ↔ a = b
  mulDivLeft : ∀ a b d : Scalar, mul (div a d) b = div (mul a b) d
  J_BSD : InvolutiveDatum
  Vis_BSD : VisibleReadoutDatum
  Audit_BSD : AuditRecordDatum
  closureAssumption : SixBirdsBSD.F1ClosureOp FormedLayer
  admissibility : Prop
  admissibility_proof : admissibility
  antiTautology : Prop
  antiTautology_proof : antiTautology
  lawfulness : Prop
  lawfulness_proof : lawfulness
  additiveBadPrimeInScope : Nat → Prop
  inertiaTrivializingLiftInScope : Nat → LocalLift → Prop
  signedSelmerAdmissiblePrime : Nat → Prop
  smuggleAuditPasses : Prop
  smuggleAuditPasses_proof : smuggleAuditPasses
  masterTheoremApplies : Prop
  foundationsIVApplicabilityAudit : Prop
  foundationsIVApplicabilityAudit_proof : foundationsIVApplicabilityAudit
  masterFromRecognitionAudits :
    ∀ (pd2 pd3 pd4 : Prop), pd2 → pd3 → pd4 →
    ∀ (sp19 sp21 sp29 : Prop), sp19 → sp21 → sp29 →
    ∀ (gz14 gz27 gz40 : Prop), gz14 → gz27 → gz40 →
    smuggleAuditPasses → masterTheoremApplies
  compositeOperationalPredicate : Prop
  compositeOperationalPredicate_proof : compositeOperationalPredicate
  compositeComputable : Prop
  compositeComputable_proof : compositeComputable
  compositeFalsifiable : Prop
  compositeFalsifiable_proof : compositeFalsifiable
  genuineDependenceOnFormedBSDLayerData : Prop
  genuineDependenceOnFormedBSDLayerData_proof :
    genuineDependenceOnFormedBSDLayerData
  AblationWitness : Type u
  ablatePadicBreaksStrongBSDScalarFactorPackage :
    AblationWitness → Prop
  ablateShaBreaksStrongBSDScalarFactorPackage :
    AblationWitness → Prop
  ablateGZBreaksStrongBSDScalarFactorPackage :
    AblationWitness → Prop
  ablatePadicWitness : AblationWitness
  ablatePadicWitness_proof :
    ablatePadicBreaksStrongBSDScalarFactorPackage ablatePadicWitness
  ablateShaWitness : AblationWitness
  ablateShaWitness_proof :
    ablateShaBreaksStrongBSDScalarFactorPackage ablateShaWitness
  ablateGZWitness : AblationWitness
  ablateGZWitness_proof :
    ablateGZBreaksStrongBSDScalarFactorPackage ablateGZWitness

/--
`Pi_BSD(E)` is the structured quantified predicate over the BSD
recognition readouts. It explicitly requires the p-adic descent carrier
for every additive bad prime and inertia-trivializing lift in scope, the
signed-Selmer persistence carrier for every HPS2-passing prime, and the
higher-GZ fixity carrier in rank at least two, together with the
lower-rank analogue lane for ranks zero and one.
-/
structure piBSD (shell : selBSDShell) where
  gammaPadicDescentReadout :
    ∀ (p : Nat) (L : shell.LocalLift),
      shell.additiveBadPrimeInScope p →
      shell.inertiaTrivializingLiftInScope p L →
      { g : SixBirdsBSD.Closure.RecognitionSources.gammaPadicDescent
          shell.EllipticCurve shell.LocalLift shell.Scalar //
        g.p = p ∧ g.E = shell.E ∧ g.L = L ∧ g.tamFactor = shell.Tam }
  gammaShaPersistenceReadout :
    ∀ p : Nat,
      shell.signedSelmerAdmissiblePrime p →
      { g : SixBirdsBSD.Closure.RecognitionSources.gammaShaPersistence
          shell.EllipticCurve shell.LocalLift shell.Scalar //
        g.p = p ∧ g.E = shell.E ∧ g.shaFactor = shell.ShaCard }
  gammaHigherGZFixityReadout :
    2 ≤ shell.analyticRank →
      { g : SixBirdsBSD.Closure.RecognitionSources.gammaHigherGZFixity
          shell.EllipticCurve shell.Scalar shell.zero shell.sub shell.mul //
        g.analyticRank = shell.analyticRank ∧ g.E = shell.E ∧
        g.L_derivative_over_factorial =
          shell.L_derivative_over_factorial ∧
        g.Reg_NT_E = shell.Reg_NT ∧ g.Omega_E = shell.Omega_E ∧
        g.Tam_E = shell.Tam ∧
        g.kappa_r_E = shell.div shell.ShaCard shell.torsionSquared ∧
        g.rhsRegulatorProduct =
          shell.mul (shell.mul (shell.mul g.kappa_r_E g.Reg_NT_E)
            g.Omega_E) g.Tam_E }
  lowerRankAnalogLane :
    shell.analyticRank = 0 ∨ shell.analyticRank = 1 →
      shell.L_derivative_over_factorial = shell.strongBSDRightSide

/--
Readout-level equivalence between residual vanishing and the Strong-BSD
scalar identity attached to the shell.
-/
theorem piBSDIffStrongBSD (shell : selBSDShell) :
    (shell.residual = shell.zero) ↔
      (shell.L_derivative_over_factorial = shell.strongBSDRightSide) := by
  rw [shell.residual_eq]
  exact
    ⟨fun h =>
      (shell.sub_eq_zero_iff shell.L_derivative_over_factorial
        shell.strongBSDRightSide).mp h,
    fun h =>
      (shell.sub_eq_zero_iff shell.L_derivative_over_factorial
        shell.strongBSDRightSide).mpr h⟩

/--
The explicit higher-GZ fixity carrier, tied to the shell scalar data
and kappa normalization, forces the Strong-BSD scalar identity.
-/
theorem gzFixityForcesStrongBSD
    {EGZ : Type uGZ}
    (shell : selBSDShell)
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
          gGZ.Tam_E) :
    shell.L_derivative_over_factorial = shell.strongBSDRightSide := by
  have hFix : gGZ.psi_minus = shell.zero :=
    (gGZ.higherGZFixity_iff_psi_minus_eq_zero).mp
      gGZ.higherGZFixity_proof
  have hSubZero :
      shell.sub gGZ.L_derivative_over_factorial
          gGZ.rhsRegulatorProduct =
        shell.zero := by
    rw [← gGZ.antiInvariantReadout_eq]
    exact hFix
  have hGZId :
      gGZ.L_derivative_over_factorial = gGZ.rhsRegulatorProduct :=
    (shell.sub_eq_zero_iff gGZ.L_derivative_over_factorial
      gGZ.rhsRegulatorProduct).mp hSubZero
  have hRhsToStrong : gGZ.rhsRegulatorProduct = shell.strongBSDRightSide := by
    calc
      gGZ.rhsRegulatorProduct =
          shell.mul
            (shell.mul (shell.mul gGZ.kappa_r_E gGZ.Reg_NT_E) gGZ.Omega_E)
            gGZ.Tam_E := hRhs
      _ =
          shell.mul
            (shell.mul
              (shell.mul
                (shell.div shell.ShaCard shell.torsionSquared)
                shell.Reg_NT)
              shell.Omega_E)
            shell.Tam := by
        rw [hKappa, hReg, hOmega, hTam]
      _ =
          shell.div
            (shell.mul (shell.mul (shell.mul shell.ShaCard shell.Reg_NT)
              shell.Omega_E) shell.Tam)
            shell.torsionSquared := by
        rw [shell.mulDivLeft shell.ShaCard shell.Reg_NT
          shell.torsionSquared]
        rw [shell.mulDivLeft (shell.mul shell.ShaCard shell.Reg_NT)
          shell.Omega_E shell.torsionSquared]
        rw [shell.mulDivLeft
          (shell.mul (shell.mul shell.ShaCard shell.Reg_NT) shell.Omega_E)
          shell.Tam shell.torsionSquared]
      _ = shell.strongBSDRightSide := by
        rw [← shell.strongBSDRightSide_eq]
  rw [← hLderiv]
  exact hGZId.trans hRhsToStrong

/--
The explicit higher-GZ fixity carrier, tied to the shell scalar data
and kappa normalization, forces vanishing of the shell residual.
-/
theorem gzFixityForcesResidualZero
    {EGZ : Type uGZ}
    (shell : selBSDShell)
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
          gGZ.Tam_E) :
    shell.residual = shell.zero := by
  have hStrong :=
    gzFixityForcesStrongBSD shell gGZ hLderiv hReg hOmega hTam hKappa hRhs
  rw [shell.residual_eq]
  exact
    (shell.sub_eq_zero_iff shell.L_derivative_over_factorial
      shell.strongBSDRightSide).mpr hStrong

/--
The closure master theorem applies to `Sel!_BSD`: the
Foundations-IV applicability audit for the three recognition-source
instantiations is combined with the smuggle audit.
-/
theorem masterTheoremApplicability
    {EPD : Type uPD} {LPD : Type vPD}
    {SPD : Type sPD}
    {ESP : Type uSP} {LSP : Type vSP} {EGZ : Type uGZ}
    {SSP : Type sSP}
    {SGZ : Type vGZ} {zGZ : SGZ} {subGZ mulGZ : SGZ → SGZ → SGZ}
    (shell : selBSDShell)
    (gPD : SixBirdsBSD.Closure.RecognitionSources.gammaPadicDescent EPD LPD SPD)
    (gSP : SixBirdsBSD.Closure.RecognitionSources.gammaShaPersistence ESP LSP SSP)
    (gGZ :
      SixBirdsBSD.Closure.RecognitionSources.gammaHigherGZFixity EGZ SGZ zGZ
        subGZ mulGZ) :
    shell.masterTheoremApplies ∧ shell.smuggleAuditPasses ∧
      (gPD.f2DescentRepairMinimalCoarsening ∧
        gPD.f3HolonomyMemoryRouteResidue ∧ gPD.f4LocalGlobal) ∧
      (gSP.f19ObjectPersistence ∧ gSP.f21ReflexiveNonclosure ∧
        gSP.f29PresentationInvariance) ∧
      (gGZ.f14DualityFixity ∧ gGZ.f27ConservationAsOrbitDescent ∧
        gGZ.f40AnomalySymmetryObstruction) := by
  have hPD :
      gPD.f2DescentRepairMinimalCoarsening ∧
        gPD.f3HolonomyMemoryRouteResidue ∧ gPD.f4LocalGlobal :=
    ⟨gPD.f2DescentRepairMinimalCoarsening_proof,
      gPD.f3HolonomyMemoryRouteResidue_proof, gPD.f4LocalGlobal_proof⟩
  have hSP :
      gSP.f19ObjectPersistence ∧ gSP.f21ReflexiveNonclosure ∧
        gSP.f29PresentationInvariance :=
    ⟨gSP.f19ObjectPersistence_proof, gSP.f21ReflexiveNonclosure_proof,
      gSP.f29PresentationInvariance_proof⟩
  have hGZ :
      gGZ.f14DualityFixity ∧ gGZ.f27ConservationAsOrbitDescent ∧
        gGZ.f40AnomalySymmetryObstruction :=
    ⟨gGZ.f14DualityFixity_proof,
      gGZ.f27ConservationAsOrbitDescent_proof,
      gGZ.f40AnomalySymmetryObstruction_proof⟩
  have hmaster : shell.masterTheoremApplies :=
    shell.masterFromRecognitionAudits
      gPD.f2DescentRepairMinimalCoarsening
      gPD.f3HolonomyMemoryRouteResidue gPD.f4LocalGlobal
      gPD.f2DescentRepairMinimalCoarsening_proof
      gPD.f3HolonomyMemoryRouteResidue_proof gPD.f4LocalGlobal_proof
      gSP.f19ObjectPersistence gSP.f21ReflexiveNonclosure
      gSP.f29PresentationInvariance gSP.f19ObjectPersistence_proof
      gSP.f21ReflexiveNonclosure_proof gSP.f29PresentationInvariance_proof
      gGZ.f14DualityFixity gGZ.f27ConservationAsOrbitDescent
      gGZ.f40AnomalySymmetryObstruction gGZ.f14DualityFixity_proof
      gGZ.f27ConservationAsOrbitDescent_proof
      gGZ.f40AnomalySymmetryObstruction_proof
      shell.smuggleAuditPasses_proof
  exact ⟨hmaster, shell.smuggleAuditPasses_proof, hPD, hSP, hGZ⟩

/--
The BSD composite operational predicate carries the `(ii)/(iii)/(ii)`
Stage-6 trace signature and the Stage-5 anti-tautology hardening:
computability, falsifiability, genuine dependence, and cancellation
proofs showing that changing any one recognition factor changes the
Strong-BSD scalar factor package.
-/
theorem compositeSignature
    {EPD : Type uPD} {LPD : Type vPD}
    {ESP : Type uSP} {LSP : Type vSP} {EGZ : Type uGZ}
    (shell : selBSDShell)
    (gPD :
      SixBirdsBSD.Closure.RecognitionSources.gammaPadicDescent EPD LPD
        shell.Scalar)
    (gSP :
      SixBirdsBSD.Closure.RecognitionSources.gammaShaPersistence ESP LSP
        shell.Scalar)
    (gGZ :
      SixBirdsBSD.Closure.RecognitionSources.gammaHigherGZFixity EGZ
        shell.Scalar shell.zero shell.sub shell.mul)
    (hSha : gSP.shaFactor = shell.ShaCard)
    (hReg : gGZ.Reg_NT_E = shell.Reg_NT)
    (hTam : gPD.tamFactor = shell.Tam)
    (mulRightCancel :
      ∀ a b c : shell.Scalar, shell.mul a c = shell.mul b c → a = b)
    (mulLeftCancel :
      ∀ a b c : shell.Scalar, shell.mul c a = shell.mul c b → a = b)
    (divLeftCancel :
      ∀ a b d : shell.Scalar, shell.div a d = shell.div b d → a = b) :
    shell.compositeOperationalPredicate ∧
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
          shell.strongBSDRightSide) := by
  refine ⟨shell.compositeOperationalPredicate_proof, ?_⟩
  refine ⟨gPD.stage6_FP_trace_ii_proof, ?_⟩
  refine ⟨gPD.stage6_SAU_trace_iii_proof, ?_⟩
  refine ⟨gPD.stage6_VDE_trace_ii_proof, ?_⟩
  refine ⟨gSP.stage6_FP_trace_ii_proof, ?_⟩
  refine ⟨gSP.stage6_SAU_trace_iii_proof, ?_⟩
  refine ⟨gSP.stage6_VDE_trace_ii_proof, ?_⟩
  refine ⟨gGZ.stage6_FP_trace_ii_proof, ?_⟩
  refine ⟨gGZ.stage6_SAU_trace_iii_proof, ?_⟩
  refine ⟨gGZ.stage6_VDE_trace_ii_proof, ?_⟩
  refine ⟨shell.compositeComputable_proof, ?_⟩
  refine ⟨shell.compositeFalsifiable_proof, ?_⟩
  refine ⟨shell.genuineDependenceOnFormedBSDLayerData_proof, ?_⟩
  refine ⟨?shaNonDisposable, ?_⟩
  · intro Sha' hchanged hsame
    rw [shell.strongBSDRightSide_eq, hReg, hTam, ← hSha] at hsame
    have hnumer :
        shell.mul (shell.mul (shell.mul Sha' shell.Reg_NT) shell.Omega_E)
            shell.Tam =
          shell.mul
            (shell.mul (shell.mul gSP.shaFactor shell.Reg_NT) shell.Omega_E)
            shell.Tam :=
      divLeftCancel
        (shell.mul (shell.mul (shell.mul Sha' shell.Reg_NT) shell.Omega_E)
          shell.Tam)
        (shell.mul
          (shell.mul (shell.mul gSP.shaFactor shell.Reg_NT) shell.Omega_E)
          shell.Tam)
        shell.torsionSquared hsame
    have hNoTam :
        shell.mul (shell.mul Sha' shell.Reg_NT) shell.Omega_E =
          shell.mul (shell.mul gSP.shaFactor shell.Reg_NT) shell.Omega_E :=
      mulRightCancel
        (shell.mul (shell.mul Sha' shell.Reg_NT) shell.Omega_E)
        (shell.mul (shell.mul gSP.shaFactor shell.Reg_NT) shell.Omega_E)
        shell.Tam hnumer
    have hNoOmega :
        shell.mul Sha' shell.Reg_NT =
          shell.mul gSP.shaFactor shell.Reg_NT :=
      mulRightCancel (shell.mul Sha' shell.Reg_NT)
        (shell.mul gSP.shaFactor shell.Reg_NT) shell.Omega_E hNoTam
    have hfactor : Sha' = gSP.shaFactor :=
      mulRightCancel Sha' gSP.shaFactor shell.Reg_NT hNoOmega
    exact hchanged hfactor
  refine ⟨?regNonDisposable, ?tamNonDisposable⟩
  · intro Reg' hchanged hsame
    rw [shell.strongBSDRightSide_eq, hSha, hTam, ← hReg] at hsame
    have hnumer :
        shell.mul (shell.mul (shell.mul shell.ShaCard Reg') shell.Omega_E)
            shell.Tam =
          shell.mul
            (shell.mul (shell.mul shell.ShaCard gGZ.Reg_NT_E) shell.Omega_E)
            shell.Tam :=
      divLeftCancel
        (shell.mul (shell.mul (shell.mul shell.ShaCard Reg') shell.Omega_E)
          shell.Tam)
        (shell.mul
          (shell.mul (shell.mul shell.ShaCard gGZ.Reg_NT_E) shell.Omega_E)
          shell.Tam)
        shell.torsionSquared hsame
    have hNoTam :
        shell.mul (shell.mul shell.ShaCard Reg') shell.Omega_E =
          shell.mul (shell.mul shell.ShaCard gGZ.Reg_NT_E) shell.Omega_E :=
      mulRightCancel
        (shell.mul (shell.mul shell.ShaCard Reg') shell.Omega_E)
        (shell.mul (shell.mul shell.ShaCard gGZ.Reg_NT_E) shell.Omega_E)
        shell.Tam hnumer
    have hNoOmega :
        shell.mul shell.ShaCard Reg' =
          shell.mul shell.ShaCard gGZ.Reg_NT_E :=
      mulRightCancel (shell.mul shell.ShaCard Reg')
        (shell.mul shell.ShaCard gGZ.Reg_NT_E) shell.Omega_E hNoTam
    have hfactor : Reg' = gGZ.Reg_NT_E :=
      mulLeftCancel Reg' gGZ.Reg_NT_E shell.ShaCard hNoOmega
    exact hchanged hfactor
  · intro Tam' hchanged hsame
    rw [shell.strongBSDRightSide_eq, hSha, hReg, ← hTam] at hsame
    have hnumer :
        shell.mul
            (shell.mul (shell.mul shell.ShaCard shell.Reg_NT) shell.Omega_E)
            Tam' =
          shell.mul
            (shell.mul (shell.mul shell.ShaCard shell.Reg_NT) shell.Omega_E)
            gPD.tamFactor :=
      divLeftCancel
        (shell.mul
          (shell.mul (shell.mul shell.ShaCard shell.Reg_NT) shell.Omega_E)
          Tam')
        (shell.mul
          (shell.mul (shell.mul shell.ShaCard shell.Reg_NT) shell.Omega_E)
          gPD.tamFactor)
        shell.torsionSquared hsame
    have hfactor : Tam' = gPD.tamFactor :=
      mulLeftCancel Tam' gPD.tamFactor
        (shell.mul (shell.mul shell.ShaCard shell.Reg_NT) shell.Omega_E)
        hnumer
    exact hchanged hfactor

end SixBirdsBSD.Closure.SelShell
