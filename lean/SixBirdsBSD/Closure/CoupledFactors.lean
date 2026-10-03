import Init.Data.Rat.Lemmas

/-!
A candidate factor assembly with three independently necessary inputs.

This is a mathematical construction, not an implementation of the existing
arithmetic recognition carriers. The coefficient and local factor stay native
until two explicit comparison equations identify them. Supplying those exact
comparisons from the arithmetic sources is a separate, unresolved obligation.
-/
namespace SixBirdsBSD.Closure.CoupledFactors

private theorem ratMulLeftComm (a b c : Rat) : a * (b * c) = b * (a * c) := by
  rw [← Rat.mul_assoc, Rat.mul_comm a b, Rat.mul_assoc]

private theorem ratInvOne : (1 : Rat)⁻¹ = 1 := by
  simpa using Rat.mul_inv_cancel (1 : Rat) (by decide)

/-- Scalar data before the coefficient and local-factor comparisons. -/
structure FactorData where
  leading : Rat
  coefficient : Rat
  regulator : Rat
  period : Rat
  nativeLocal : Rat
  sha : Rat
  torsionSquared : Rat
  tamagawa : Rat

/-- Fixity on native factors, without inserting the BSD normalization. -/
def NativeFixity (d : FactorData) : Prop :=
  d.leading = ((d.coefficient * d.regulator) * d.period) * d.nativeLocal

/-- Required exact return from the native local factor to the Tamagawa product.
A prime-local congruence up to units alone does not supply this equation. -/
def LocalComparison (d : FactorData) : Prop := d.nativeLocal = d.tamagawa

/-- Required exact return from the native coefficient to the Sha/torsion ratio.
This is separate from native fixity and must have an arithmetic source. -/
def CoefficientComparison (d : FactorData) : Prop :=
  d.coefficient = d.sha / d.torsionSquared

def ScalarBSD (d : FactorData) : Prop :=
  d.leading = ((d.sha * d.regulator) * d.period) * d.tamagawa / d.torsionSquared

/-- The scalar identity sees the product of the two native factors. -/
def CombinedComparison (d : FactorData) : Prop :=
  d.coefficient * d.nativeLocal = (d.sha / d.torsionSquared) * d.tamagawa

/-- Under native fixity, the exact scalar requirement is a product comparison.
Separate comparisons give more information and may fail by compensating units. -/
theorem scalarIffCombined (d : FactorData) (hFix : NativeFixity d)
    (hNonzero : d.regulator * d.period ≠ 0) :
    ScalarBSD d ↔ CombinedComparison d := by
  have hNative : d.leading =
      (d.coefficient * d.nativeLocal) * (d.regulator * d.period) := by
    unfold NativeFixity at hFix
    rw [hFix]
    simp only [Rat.mul_comm, ratMulLeftComm]
  have hTarget :
      ((d.sha * d.regulator) * d.period) * d.tamagawa / d.torsionSquared =
      ((d.sha / d.torsionSquared) * d.tamagawa) * (d.regulator * d.period) := by
    simp only [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, ratMulLeftComm]
  unfold ScalarBSD CombinedComparison
  rw [hNative, hTarget]
  constructor
  · intro h
    have hc := congrArg (fun x : Rat => x * (d.regulator * d.period)⁻¹) h
    simpa only [Rat.mul_assoc, Rat.mul_inv_cancel _ hNonzero, Rat.mul_one] using hc
  · intro h
    rw [h]

/-- The three explicit comparisons assemble scalar BSD. No cancellation or
nonzero assumption is needed for this forward identity in totalized Rat. -/
theorem assemble (d : FactorData) (hFix : NativeFixity d)
    (hLocal : LocalComparison d) (hCoefficient : CoefficientComparison d) :
    ScalarBSD d := by
  unfold NativeFixity at hFix
  unfold LocalComparison at hLocal
  unfold CoefficientComparison at hCoefficient
  unfold ScalarBSD
  rw [hFix, hLocal, hCoefficient]
  simp only [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, ratMulLeftComm]

/-- Three fully positive data sets, each violating only one required input.
They witness logical necessity relative to this weakened native interface. -/
def missingLocal : FactorData := ⟨2, 1, 1, 1, 2, 1, 1, 1⟩
def missingCoefficient : FactorData := ⟨2, 2, 1, 1, 1, 1, 1, 1⟩
def missingFixity : FactorData := ⟨2, 1, 1, 1, 1, 1, 1, 1⟩

theorem localInputNecessary :
    NativeFixity missingLocal ∧ CoefficientComparison missingLocal ∧
      ¬ LocalComparison missingLocal ∧ ¬ ScalarBSD missingLocal := by
  simp [NativeFixity, CoefficientComparison, LocalComparison, ScalarBSD,
    missingLocal, Rat.div_def, ratInvOne]

theorem coefficientInputNecessary :
    NativeFixity missingCoefficient ∧ LocalComparison missingCoefficient ∧
      ¬ CoefficientComparison missingCoefficient ∧ ¬ ScalarBSD missingCoefficient := by
  simp [NativeFixity, CoefficientComparison, LocalComparison, ScalarBSD,
    missingCoefficient, Rat.div_def, ratInvOne]

theorem fixityInputNecessary :
    LocalComparison missingFixity ∧ CoefficientComparison missingFixity ∧
      ¬ NativeFixity missingFixity ∧ ¬ ScalarBSD missingFixity := by
  simp [NativeFixity, CoefficientComparison, LocalComparison, ScalarBSD,
    missingFixity, Rat.div_def, ratInvOne]

/-- BSD can hold with both individual comparisons false. Necessity above means
that dropping one premise invalidates the universal assembly theorem; it does
not mean each premise is necessary for every individual scalar equality. -/
def compensatingFactors : FactorData := ⟨1, 2, 1, 1, 1 / 2, 1, 1, 1⟩

theorem compensatingFactorsWork :
    NativeFixity compensatingFactors ∧ ScalarBSD compensatingFactors ∧
      ¬ LocalComparison compensatingFactors ∧
      ¬ CoefficientComparison compensatingFactors := by
  unfold NativeFixity ScalarBSD LocalComparison CoefficientComparison compensatingFactors
  decide +kernel

def AllPositive (d : FactorData) : Prop :=
  0 < d.leading ∧ 0 < d.coefficient ∧ 0 < d.regulator ∧ 0 < d.period ∧
    0 < d.nativeLocal ∧ 0 < d.sha ∧ 0 < d.torsionSquared ∧ 0 < d.tamagawa

theorem countermodelsPositive : AllPositive missingLocal ∧
    AllPositive missingCoefficient ∧ AllPositive missingFixity ∧
    AllPositive compensatingFactors := by
  unfold AllPositive missingLocal missingCoefficient missingFixity compensatingFactors
  decide +kernel

/-- Once fixity already uses the normalized coefficient and Tamagawa factor,
the scalar conclusion follows without any additional local recognition data. -/
theorem normalizedFixityAlreadySuffices (d : FactorData)
    (h : d.leading = ((d.sha / d.torsionSquared * d.regulator) * d.period) *
      d.tamagawa) : ScalarBSD d := by
  unfold ScalarBSD
  rw [h]
  simp only [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, ratMulLeftComm]


/-- The two exact comparisons retain more information than their product.
This is an auxiliary return package on the native rational carrier, not a
replacement for the paper's scalar conditional BSD target. -/
def FullComparisonPackage (d : FactorData) : Prop :=
  LocalComparison d ∧ CoefficientComparison d

/-- Once native fixity and scalar BSD are known, retaining either comparison
recovers the other. This does not assert that either original arithmetic
source supplies its required exact comparison. -/
theorem comparisonsEquivalentUnderScalar (d : FactorData)
    (hFix : NativeFixity d) (hBSD : ScalarBSD d)
    (hReg : d.regulator * d.period ≠ 0)
    (hTam : d.tamagawa ≠ 0) (hCoefficient : d.sha / d.torsionSquared ≠ 0) :
    LocalComparison d ↔ CoefficientComparison d := by
  have hc := (scalarIffCombined d hFix hReg).mp hBSD
  unfold LocalComparison CoefficientComparison CombinedComparison at *
  constructor <;> intro h <;> grind

theorem fullPackageIffLocalUnderScalar (d : FactorData)
    (hFix : NativeFixity d) (hBSD : ScalarBSD d)
    (hReg : d.regulator * d.period ≠ 0)
    (hTam : d.tamagawa ≠ 0) (hCoefficient : d.sha / d.torsionSquared ≠ 0) :
    FullComparisonPackage d ↔ LocalComparison d := by
  exact ⟨fun h => h.1, fun h => ⟨h,
    (comparisonsEquivalentUnderScalar d hFix hBSD hReg hTam hCoefficient).mp h⟩⟩

theorem fullPackageIffCoefficientUnderScalar (d : FactorData)
    (hFix : NativeFixity d) (hBSD : ScalarBSD d)
    (hReg : d.regulator * d.period ≠ 0)
    (hTam : d.tamagawa ≠ 0) (hCoefficient : d.sha / d.torsionSquared ≠ 0) :
    FullComparisonPackage d ↔ CoefficientComparison d := by
  exact ⟨fun h => h.2, fun h => ⟨
    (comparisonsEquivalentUnderScalar d hFix hBSD hReg hTam hCoefficient).mpr h, h⟩⟩

/-- All positive solutions of the combined comparison have exactly the
reciprocal rescaling form. Positivity excludes the zero and sign boundaries;
the retained normalization equations are not assumed in this classification. -/
theorem positiveComparisonFiber (d : FactorData)
    (hFix : NativeFixity d) (hPositive : AllPositive d) :
    ScalarBSD d ↔ ∃ u : Rat, 0 < u ∧
      d.coefficient = u * (d.sha / d.torsionSquared) ∧
      d.nativeLocal = d.tamagawa / u := by
  rcases hPositive with ⟨hL, ha, hR, hO, hb, hSha, hTor, hTam⟩
  have hReg : d.regulator * d.period ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hR hO)
  have hRatio : 0 < d.sha / d.torsionSquared := by
    simpa only [Rat.div_def] using Rat.mul_pos hSha (Rat.inv_pos.mpr hTor)
  have hRatioNZ : d.sha / d.torsionSquared ≠ 0 := Rat.ne_of_gt hRatio
  have haNZ : d.coefficient ≠ 0 := Rat.ne_of_gt ha
  constructor
  · intro hBSD
    have hc := (scalarIffCombined d hFix hReg).mp hBSD
    have hu : 0 < d.coefficient / (d.sha / d.torsionSquared) := by
      simpa only [Rat.div_def] using Rat.mul_pos ha (Rat.inv_pos.mpr hRatio)
    refine ⟨d.coefficient / (d.sha / d.torsionSquared), hu, ?_⟩
    unfold CombinedComparison at hc
    grind
  · rintro ⟨u, hu, ha, hb⟩
    have huNZ : u ≠ 0 := Rat.ne_of_gt hu
    apply (scalarIffCombined d hFix hReg).mpr
    unfold CombinedComparison
    grind

/-- The rescaling parameter is determined by the retained coefficient.
This uniqueness is algebraic and does not prescribe a native arithmetic
normalization or select the parameter one. -/
theorem comparisonFiberParameterUnique (d : FactorData) (u v : Rat)
    (hRatio : d.sha / d.torsionSquared ≠ 0)
    (hu : d.coefficient = u * (d.sha / d.torsionSquared))
    (hv : d.coefficient = v * (d.sha / d.torsionSquared)) : u = v := by grind

/-- A full positive family freezing the leading coefficient, regulator,
period, Sha, torsion and Tamagawa factors, and the joint native product. -/
def positiveGauge (u : Rat) : FactorData := ⟨1, u, 1, 1, 1/u, 1, 1, 1⟩

theorem positiveGaugeReturns (u : Rat) (hu : 0 < u) :
    AllPositive (positiveGauge u) ∧ NativeFixity (positiveGauge u) ∧
    ScalarBSD (positiveGauge u) := by
  have huNZ : u ≠ 0 := Rat.ne_of_gt hu
  have hInv : 0 < 1/u := by
    simpa only [Rat.div_def, Rat.one_mul] using Rat.inv_pos.mpr hu
  constructor
  · dsimp [AllPositive, positiveGauge]
    exact ⟨by decide, hu, by decide, by decide, hInv, by decide, by decide, by decide⟩
  · unfold NativeFixity ScalarBSD positiveGauge
    grind

theorem positiveGaugePackageIffOne (u : Rat) :
    FullComparisonPackage (positiveGauge u) ↔ u = 1 := by
  unfold FullComparisonPackage LocalComparison CoefficientComparison positiveGauge
  grind

/-- This lens deliberately erases the two individual native factors while
retaining their joint product and every other scalar field. -/
def scalarFactorLens (d : FactorData) : Rat × Rat × Rat × Rat × Rat × Rat × Rat :=
  (d.leading, d.regulator, d.period, d.sha, d.torsionSquared, d.tamagawa,
    d.coefficient * d.nativeLocal)

theorem positiveGaugeLensConstant (u : Rat) (hu : 0 < u) :
    scalarFactorLens (positiveGauge u) = (1,1,1,1,1,1,1) := by
  have huNZ : u ≠ 0 := Rat.ne_of_gt hu
  unfold scalarFactorLens positiveGauge
  have h : u * (1/u) = 1 := by grind
  rw [h]

/-- No predicate on the declared scalar lens recovers the full comparison
package throughout this positive family. The witness is rational, not a
pair of elliptic curves retaining every named arithmetic source. -/
theorem noFullPackageFromScalarLens :
    ¬ ∃ read : (Rat × Rat × Rat × Rat × Rat × Rat × Rat) → Prop,
      ∀ u : Rat, 0 < u →
        (read (scalarFactorLens (positiveGauge u)) ↔
          FullComparisonPackage (positiveGauge u)) := by
  rintro ⟨read, h⟩
  have hOne : read (scalarFactorLens (positiveGauge 1)) :=
    (h 1 (by decide)).mpr ((positiveGaugePackageIffOne 1).mpr rfl)
  have hSame : scalarFactorLens (positiveGauge 1) =
      scalarFactorLens (positiveGauge 2) :=
    (positiveGaugeLensConstant 1 (by decide)).trans
      (positiveGaugeLensConstant 2 (by decide)).symm
  rw [hSame] at hOne
  have hTwo : (2 : Rat) = 1 :=
    (positiveGaugePackageIffOne 2).mp ((h 2 (by decide)).mp hOne)
  exact (by decide : (2 : Rat) ≠ 1) hTwo


/-- The two cancellation hypotheses above cannot simply be dropped.
These are boundary controls of the totalized rational carrier, outside
the positive arithmetic-factor domain. -/
def zeroTamagawaControl : FactorData := ⟨0,2,1,1,0,1,1,0⟩
def zeroCoefficientControl : FactorData := ⟨0,0,1,1,2,0,1,1⟩

theorem comparisonZeroControls :
    (NativeFixity zeroTamagawaControl ∧ ScalarBSD zeroTamagawaControl ∧
      LocalComparison zeroTamagawaControl ∧
      ¬ CoefficientComparison zeroTamagawaControl) ∧
    (NativeFixity zeroCoefficientControl ∧ ScalarBSD zeroCoefficientControl ∧
      CoefficientComparison zeroCoefficientControl ∧
      ¬ LocalComparison zeroCoefficientControl) := by
  unfold NativeFixity ScalarBSD LocalComparison CoefficientComparison
    zeroTamagawaControl zeroCoefficientControl
  decide +kernel

end SixBirdsBSD.Closure.CoupledFactors
