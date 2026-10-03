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

/-- The legacy audit rule quantifies over arbitrary propositions. These
propositions have no interpreted source/instance constraints. Its exact
logical strength is proved below rather than inferred from its name. -/
def RecognitionAuditLaw (smuggle master : Prop) : Prop :=
  ∀ (pd2 pd3 pd4 : Prop), pd2 → pd3 → pd4 →
  ∀ (sp19 sp21 sp29 : Prop), sp19 → sp21 → sp29 →
  ∀ (gz14 gz27 gz40 : Prop), gz14 → gz27 → gz40 →
  smuggle → master

/-- Nine universally quantified proved propositions do not supply extra
logical content: instantiate every one with True. -/
theorem recognitionAuditLawIffImplication (smuggle master : Prop) :
    RecognitionAuditLaw smuggle master ↔ (smuggle → master) := by
  constructor
  · intro h hs
    exact h True True True True.intro True.intro True.intro
      True True True True.intro True.intro True.intro
      True True True True.intro True.intro True.intro hs
  · intro h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs
    exact h hs

theorem recognitionAuditLawIffConclusion (smuggle master : Prop)
    (hs : smuggle) : RecognitionAuditLaw smuggle master ↔ master := by
  rw [recognitionAuditLawIffImplication]
  exact ⟨fun h => h hs,fun h _ => h⟩

/-- Both premise controls matter when interpreting the law. A false
smuggle premise makes it vacuous; a true premise rejects a false return. -/
theorem recognitionAuditLawControls :
    RecognitionAuditLaw False False ∧ ¬ RecognitionAuditLaw True False := by
  constructor
  · exact (recognitionAuditLawIffImplication False False).mpr id
  · intro h
    exact (recognitionAuditLawIffConclusion True False True.intro).mp h

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
  /-- With the preceding smuggle proof this field is equivalent to the
  applicability conclusion itself. It is supplied content, not a derived
  Foundations-IV applicability theorem or a source-dependence proof. -/
  masterFromRecognitionAudits : RecognitionAuditLaw smuggleAuditPasses masterTheoremApplies
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

/-- Exact dependency of the legacy master conclusion. No recognition
carrier or closure operator is used by this projection of supplied content. -/
theorem selBSDShell.masterApplicabilityFromRule (shell : selBSDShell) :
    shell.masterTheoremApplies :=
  (recognitionAuditLawIffConclusion _ _ shell.smuggleAuditPasses_proof).mp
    shell.masterFromRecognitionAudits

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

/-- A local descent readout inherits actual numerical scope at its matched
prime. Both the bad-place and specified-lift hypotheses are necessary. -/
theorem piBSD.padicPrimeScope (shell : selBSDShell) (recognition : piBSD shell)
    (p : Nat) (L : shell.LocalLift)
    (hp : shell.additiveBadPrimeInScope p)
    (hL : shell.inertiaTrivializingLiftInScope p L) :
    SixBirdsBSD.Apparatus.SupportPrimeNoGo.IsPrime p ∧ p % 2 = 1 := by
  obtain ⟨g, hg⟩ := recognition.gammaPadicDescentReadout p L hp hL
  rw [← hg.1]
  exact ⟨g.prime, g.odd⟩

/-- Signed-Selmer scope requires a prime; no unsupported oddness restriction
is added to this separate source. -/
theorem piBSD.signedPrimeScope (shell : selBSDShell) (recognition : piBSD shell)
    (p : Nat) (hp : shell.signedSelmerAdmissiblePrime p) :
    SixBirdsBSD.Apparatus.SupportPrimeNoGo.IsPrime p := by
  obtain ⟨g, hg⟩ := recognition.gammaShaPersistenceReadout p hp
  rw [← hg.1]
  exact g.prime

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
Conditional applicability and the three supplied source-audit packages.
The master component follows from the shell's conclusion-equivalent rule;
the source records supply the separately returned audit conjuncts. This
does not derive an interpreted Foundations-IV application from those records.
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
  have hmaster : shell.masterTheoremApplies := shell.masterApplicabilityFromRule
  exact ⟨hmaster, shell.smuggleAuditPasses_proof, hPD, hSP, hGZ⟩

/-- Cancellation only at the five actual BSD multipliers and denominator.
These hypotheses hold for nonzero real BSD factors. They do not require
cancellation at zero, and do not assert independence of recognition records. -/
structure FactorCancellation (shell : selBSDShell) : Prop where
  reg : ∀ a b, shell.mul a shell.Reg_NT = shell.mul b shell.Reg_NT → a = b
  omega : ∀ a b, shell.mul a shell.Omega_E = shell.mul b shell.Omega_E → a = b
  tam : ∀ a b, shell.mul a shell.Tam = shell.mul b shell.Tam → a = b
  sha : ∀ a b, shell.mul shell.ShaCard a = shell.mul shell.ShaCard b → a = b
  shaRegOmega : ∀ a b,
    shell.mul (shell.mul (shell.mul shell.ShaCard shell.Reg_NT) shell.Omega_E) a =
      shell.mul (shell.mul (shell.mul shell.ShaCard shell.Reg_NT) shell.Omega_E) b →
      a = b
  torsion : ∀ a b, shell.div a shell.torsionSquared =
    shell.div b shell.torsionSquared → a = b

/-- For native field operations, the previously separate cancellation
record is constructed from the actual nonzero BSD factors. These operation
matches are essential; an arbitrary shell multiplication is not identified
with field multiplication merely by supplying a field on its carrier. -/
def factorCancellationFromField (shell : selBSDShell)
    [Lean.Grind.Field shell.Scalar]
    (hMul : shell.mul = fun a b => a*b)
    (hDiv : shell.div = fun a b => a/b)
    (hReg : shell.Reg_NT ≠ 0) (hOmega : shell.Omega_E ≠ 0)
    (hTam : shell.Tam ≠ 0) (hSha : shell.ShaCard ≠ 0)
    (hTorsion : shell.torsionSquared ≠ 0) : FactorCancellation shell where
  reg := by intro a b h; rw [hMul] at h; grind
  omega := by intro a b h; rw [hMul] at h; grind
  tam := by intro a b h; rw [hMul] at h; grind
  sha := by intro a b h; rw [hMul] at h; grind
  shaRegOmega := by intro a b h; simp only [hMul] at h; grind
  torsion := by intro a b h; rw [hDiv] at h; grind

/-- Exact strength of the cancellation record on native field operations.
The mixed multiplier law adds no further nonzero condition. -/
theorem factorCancellationIffNonzero (shell : selBSDShell)
    [Lean.Grind.Field shell.Scalar]
    (hMul : shell.mul = fun a b => a*b)
    (hDiv : shell.div = fun a b => a/b) :
    FactorCancellation shell ↔
      shell.Reg_NT ≠ 0 ∧ shell.Omega_E ≠ 0 ∧ shell.Tam ≠ 0 ∧
        shell.ShaCard ≠ 0 ∧ shell.torsionSquared ≠ 0 := by
  constructor
  · intro c
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hZero
      apply Lean.Grind.Field.zero_ne_one (α := shell.Scalar)
      exact c.reg 0 1 (by rw [hMul, hZero]; grind)
    · intro hZero
      apply Lean.Grind.Field.zero_ne_one (α := shell.Scalar)
      exact c.omega 0 1 (by rw [hMul, hZero]; grind)
    · intro hZero
      apply Lean.Grind.Field.zero_ne_one (α := shell.Scalar)
      exact c.tam 0 1 (by rw [hMul, hZero]; grind)
    · intro hZero
      apply Lean.Grind.Field.zero_ne_one (α := shell.Scalar)
      exact c.sha 0 1 (by rw [hMul, hZero]; grind)
    · intro hZero
      apply Lean.Grind.Field.zero_ne_one (α := shell.Scalar)
      exact c.torsion 0 1 (by rw [hDiv, hZero]; grind)
  · rintro ⟨hReg, hOmega, hTam, hSha, hTorsion⟩
    exact factorCancellationFromField shell hMul hDiv
      hReg hOmega hTam hSha hTorsion

/-- The quantified recognition predicate supplies the scalar identity in every
rank. The lower-rank lane and the normalized higher-rank fixity are explicit
supplied arithmetic content; this does not reconstruct sources from a scalar. -/
theorem piBSDForcesStrongBSD (shell : selBSDShell) (recognition : piBSD shell) :
    shell.L_derivative_over_factorial = shell.strongBSDRightSide := by
  by_cases hr : 2 ≤ shell.analyticRank
  · obtain ⟨g, hRank, hE, hL, hReg, hOmega, hTam, hKappa, hRhs⟩ :=
      recognition.gammaHigherGZFixityReadout hr
    exact gzFixityForcesStrongBSD shell g hL hReg hOmega hTam hKappa hRhs
  · have hlow : shell.analyticRank = 0 ∨ shell.analyticRank = 1 := by omega
    exact recognition.lowerRankAnalogLane hlow

/-- Forward scalar readout of the quantified recognition predicate. -/
theorem piBSDForcesResidualZero (shell : selBSDShell) (recognition : piBSD shell) :
    shell.residual = shell.zero :=
  (piBSDIffStrongBSD shell).mpr (piBSDForcesStrongBSD shell recognition)

/--
The BSD composite operational predicate carries the `(ii)/(iii)/(ii)`
Stage-6 trace signature and the Stage-5 anti-tautology hardening:
computability, falsifiability, genuine dependence, and cancellation
proofs showing that changing any one scalar factor changes the
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
    (cancellation : FactorCancellation shell) :
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
      cancellation.torsion
        (shell.mul (shell.mul (shell.mul Sha' shell.Reg_NT) shell.Omega_E)
          shell.Tam)
        (shell.mul
          (shell.mul (shell.mul gSP.shaFactor shell.Reg_NT) shell.Omega_E)
          shell.Tam)
        hsame
    have hNoTam :
        shell.mul (shell.mul Sha' shell.Reg_NT) shell.Omega_E =
          shell.mul (shell.mul gSP.shaFactor shell.Reg_NT) shell.Omega_E :=
      cancellation.tam
        (shell.mul (shell.mul Sha' shell.Reg_NT) shell.Omega_E)
        (shell.mul (shell.mul gSP.shaFactor shell.Reg_NT) shell.Omega_E)
        hnumer
    have hNoOmega :
        shell.mul Sha' shell.Reg_NT =
          shell.mul gSP.shaFactor shell.Reg_NT :=
      cancellation.omega (shell.mul Sha' shell.Reg_NT)
        (shell.mul gSP.shaFactor shell.Reg_NT) hNoTam
    have hfactor : Sha' = gSP.shaFactor :=
      cancellation.reg Sha' gSP.shaFactor hNoOmega
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
      cancellation.torsion
        (shell.mul (shell.mul (shell.mul shell.ShaCard Reg') shell.Omega_E)
          shell.Tam)
        (shell.mul
          (shell.mul (shell.mul shell.ShaCard gGZ.Reg_NT_E) shell.Omega_E)
          shell.Tam)
        hsame
    have hNoTam :
        shell.mul (shell.mul shell.ShaCard Reg') shell.Omega_E =
          shell.mul (shell.mul shell.ShaCard gGZ.Reg_NT_E) shell.Omega_E :=
      cancellation.tam
        (shell.mul (shell.mul shell.ShaCard Reg') shell.Omega_E)
        (shell.mul (shell.mul shell.ShaCard gGZ.Reg_NT_E) shell.Omega_E)
        hnumer
    have hNoOmega :
        shell.mul shell.ShaCard Reg' =
          shell.mul shell.ShaCard gGZ.Reg_NT_E :=
      cancellation.omega (shell.mul shell.ShaCard Reg')
        (shell.mul shell.ShaCard gGZ.Reg_NT_E) hNoTam
    have hfactor : Reg' = gGZ.Reg_NT_E :=
      cancellation.sha Reg' gGZ.Reg_NT_E hNoOmega
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
      cancellation.torsion
        (shell.mul
          (shell.mul (shell.mul shell.ShaCard shell.Reg_NT) shell.Omega_E)
          Tam')
        (shell.mul
          (shell.mul (shell.mul shell.ShaCard shell.Reg_NT) shell.Omega_E)
          gPD.tamFactor)
        hsame
    have hfactor : Tam' = gPD.tamFactor :=
      cancellation.shaRegOmega Tam' gPD.tamFactor hnumer
    exact hchanged hfactor

end SixBirdsBSD.Closure.SelShell
