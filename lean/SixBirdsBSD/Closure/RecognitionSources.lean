import SixBirdsBSD.Apparatus.SupportPrimeNoGo

/-!
Recognition-source carriers for the closure axis.

These are typed carriers for formed-layer closure content. Their
arithmetic content is represented by explicit `Prop` fields and
certificate fields, so downstream closure theorems can take the
carrier as a hypothesis while this module derives no framework theorem.
-/

namespace SixBirdsBSD.Closure.RecognitionSources

open SixBirdsBSD.Apparatus.SupportPrimeNoGo

universe u v w x y z

/-- Numerical scope only; additive reduction, tameness and Sha hypotheses
remain separate arithmetic inputs. In particular this does not certify
the arithmetic applicability of a numerical prime-three control. -/
def OddShallowNumericScope (p c : Nat) : Prop :=
  IsPrime p ∧ p % 2 = 1 ∧ (c = 1 ∨ c = 2)

instance (p c : Nat) : Decidable (OddShallowNumericScope p c) :=
  inferInstanceAs (Decidable (IsPrime p ∧ p % 2 = 1 ∧ (c = 1 ∨ c = 2)))

theorem oddShallowNondivisibility (p c : Nat)
    (h : OddShallowNumericScope p c) : ¬ p ∣ c := by
  have hp := h.1.1
  have hodd := h.2.1
  have hp3 : 3 ≤ p := by omega
  have hc : 0 < c ∧ c ≤ 2 := by rcases h.2.2 with hc | hc <;> omega
  intro hd
  have := Nat.le_of_dvd hc.1 hd
  omega

theorem numericalScopeControls :
    OddShallowNumericScope 11 1 ∧ OddShallowNumericScope 11 2 ∧
    OddShallowNumericScope 3 2 ∧
    ¬ OddShallowNumericScope 0 1 ∧ ¬ OddShallowNumericScope 1 1 ∧
    ¬ OddShallowNumericScope 2 1 ∧ ¬ OddShallowNumericScope 9 1 ∧
    ¬ OddShallowNumericScope 11 0 ∧ ¬ OddShallowNumericScope 11 3 ∧
    IsPrime 2 := by decide +kernel

/--
`Gamma_BSD^padic-descent`: the D3''' additive-prime p-adic descent
recognition source. For `E/Q`, an odd additive prime `p` in the shallow
Kodaira II/III scope, with the stated Tamagawa and p-primary Sha
hypotheses and a finite tame inertia-trivializing extension `L/Q_p`,
the formed local layer carries the OC descent comparison and unit whose
congruence is recorded as recognition-source content.
-/
structure gammaPadicDescent
    (EllipticCurve : Type u) (LocalExtension : Type v)
    (Scalar : Type z) where
  E : EllipticCurve
  p : Nat
  prime : IsPrime p
  odd : p % 2 = 1
  L : LocalExtension
  oddAdditivePrime : Prop
  oddAdditivePrime_proof : oddAdditivePrime
  shallowKodairaIIOrIII : Prop
  shallowKodairaIIOrIII_proof : shallowKodairaIIOrIII
  c_p : Nat
  c_p_mem_one_or_two : c_p = 1 ∨ c_p = 2
  sha_p_infty_zero : Prop
  sha_p_infty_zero_proof : sha_p_infty_zero
  finiteTameInertiaTrivializing : Prop
  finiteTameInertiaTrivializing_proof : finiteTameInertiaTrivializing
  LC_triv_E_L : Type w
  LC_triv_E : Type x
  descent_p_OC : LC_triv_E_L → LC_triv_E
  ZpUnit : Type y
  epsilon_p : ZpUnit
  localDescentCongruenceModZpUnits : Prop
  localDescentCongruenceModZpUnits_proof :
    localDescentCongruenceModZpUnits
  f2DescentRepairMinimalCoarsening : Prop
  f2DescentRepairMinimalCoarsening_proof :
    f2DescentRepairMinimalCoarsening
  f3HolonomyMemoryRouteResidue : Prop
  f3HolonomyMemoryRouteResidue_proof :
    f3HolonomyMemoryRouteResidue
  f4LocalGlobal : Prop
  f4LocalGlobal_proof : f4LocalGlobal
  stage6_FP_trace_ii : Prop
  stage6_FP_trace_ii_proof : stage6_FP_trace_ii
  stage6_SAU_trace_iii : Prop
  stage6_SAU_trace_iii_proof : stage6_SAU_trace_iii
  stage6_VDE_trace_ii : Prop
  stage6_VDE_trace_ii_proof : stage6_VDE_trace_ii
  tamFactor : Scalar

abbrev gammaPadicDescent.p_does_not_divide_c_p
    {E : Type u} {L : Type v} {S : Type z}
    (g : gammaPadicDescent E L S) : Prop := ¬ g.p ∣ g.c_p

theorem gammaPadicDescent.numericApplicability
    {E : Type u} {L : Type v} {S : Type z}
    (g : gammaPadicDescent E L S) : OddShallowNumericScope g.p g.c_p :=
  ⟨g.prime, g.odd, g.c_p_mem_one_or_two⟩

/-- Nondivisibility is derived from the actual indices, rather than supplied
as an unrelated proposition carrying the name of the desired fact. -/
theorem gammaPadicDescent.p_does_not_divide_c_p_proof
    {E : Type u} {L : Type v} {S : Type z}
    (g : gammaPadicDescent E L S) : g.p_does_not_divide_c_p :=
  oddShallowNondivisibility g.p g.c_p g.numericApplicability

/--
`Gamma_BSD^Sha-persistence`: the D2''' signed-Selmer corestriction
recognition source. For `E/Q`, an HPS2-passing additive prime `p`, and
a tame inertia-trivializing `L/Q_p`, the signed-Selmer persistence
layer carries the cover-change determinant
`C_loc_III = det(cores o signed_local_pairing_p)` and the congruence
to the local Tamagawa factor modulo `Z_p^x`.
-/
structure gammaShaPersistence
    (EllipticCurve : Type u) (LocalExtension : Type v)
    (Scalar : Type z) where
  E : EllipticCurve
  p : Nat
  prime : IsPrime p
  L : LocalExtension
  hps2PassingAdditivePrime : Prop
  hps2PassingAdditivePrime_proof : hps2PassingAdditivePrime
  tameInertiaTrivializing : Prop
  tameInertiaTrivializing_proof : tameInertiaTrivializing
  SignedSelmerSource : Type w
  /-- The cover-side readout of the signed local pairing. -/
  SignedSelmerTarget : Type x
  /-- The base-field readout after corestriction. Cover and base carriers
  are kept distinct; determinant-line compatibility remains supplied. -/
  SignedSelmerBase : Type x
  DeterminantValue : Type y
  signed_local_pairing_p : SignedSelmerSource → SignedSelmerTarget
  cores_L_Qp : SignedSelmerTarget → SignedSelmerBase
  det : (SignedSelmerSource → SignedSelmerBase) → DeterminantValue
  C_loc_III : DeterminantValue
  C_loc_III_eq_det_corestriction_signed_local_pairing :
    C_loc_III =
      det (fun s => cores_L_Qp (signed_local_pairing_p s))
  c_p : DeterminantValue
  C_loc_III_congruent_c_p_mod_ZpUnits : Prop
  C_loc_III_congruent_c_p_mod_ZpUnits_proof :
    C_loc_III_congruent_c_p_mod_ZpUnits
  f19ObjectPersistence : Prop
  f19ObjectPersistence_proof : f19ObjectPersistence
  f21ReflexiveNonclosure : Prop
  f21ReflexiveNonclosure_proof : f21ReflexiveNonclosure
  f29PresentationInvariance : Prop
  f29PresentationInvariance_proof : f29PresentationInvariance
  stage6_FP_trace_ii : Prop
  stage6_FP_trace_ii_proof : stage6_FP_trace_ii
  stage6_SAU_trace_iii : Prop
  stage6_SAU_trace_iii_proof : stage6_SAU_trace_iii
  stage6_VDE_trace_ii : Prop
  stage6_VDE_trace_ii_proof : stage6_VDE_trace_ii
  shaFactor : Scalar

/--
`Gamma_BSD^higher-GZ-fixity`: the D2'' rank-`r` archimedean fixity
recognition source. For non-CM `E/Q` of analytic rank at least two,
the formed rank-`r` arithmetic/analytic duality layer carries the
anti-invariant readout `psi_minus` and the higher-GZ fixity predicate
`psi_minus = 0`, equivalently the displayed determinant/regulator
identity.
-/
structure gammaHigherGZFixity
    (EllipticCurve : Type u) (Scalar : Type v)
    (zero : Scalar) (sub mul : Scalar → Scalar → Scalar) where
  E : EllipticCurve
  analyticRank : Nat
  analyticRank_ge_two : 2 ≤ analyticRank
  nonCM : Prop
  nonCM_proof : nonCM
  L_derivative_over_factorial : Scalar
  kappa_r_E : Scalar
  Reg_NT_E : Scalar
  Omega_E : Scalar
  Tam_E : Scalar
  psi_minus : Scalar
  rhsRegulatorProduct : Scalar :=
    mul (mul (mul kappa_r_E Reg_NT_E) Omega_E) Tam_E
  antiInvariantReadout_eq :
    psi_minus = sub L_derivative_over_factorial rhsRegulatorProduct
  higherGZFixity : Prop
  higherGZFixity_iff_psi_minus_eq_zero :
    higherGZFixity ↔ psi_minus = zero
  higherGZFixity_proof : higherGZFixity
  equivalentRankIdentity : Prop
  equivalentRankIdentity_iff_fixity :
    equivalentRankIdentity ↔ higherGZFixity
  f14DualityFixity : Prop
  f14DualityFixity_proof : f14DualityFixity
  f27ConservationAsOrbitDescent : Prop
  f27ConservationAsOrbitDescent_proof :
    f27ConservationAsOrbitDescent
  f40AnomalySymmetryObstruction : Prop
  f40AnomalySymmetryObstruction_proof :
    f40AnomalySymmetryObstruction
  stage6_FP_trace_ii : Prop
  stage6_FP_trace_ii_proof : stage6_FP_trace_ii
  stage6_SAU_trace_iii : Prop
  stage6_SAU_trace_iii_proof : stage6_SAU_trace_iii
  stage6_VDE_trace_ii : Prop
  stage6_VDE_trace_ii_proof : stage6_VDE_trace_ii

end SixBirdsBSD.Closure.RecognitionSources
