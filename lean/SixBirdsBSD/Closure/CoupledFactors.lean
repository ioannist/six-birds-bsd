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

end SixBirdsBSD.Closure.CoupledFactors
