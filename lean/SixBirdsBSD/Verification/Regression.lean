import SixBirdsBSD
import Init.Data.Rat.Lemmas

/-! Adversarial checks for the mathematical review. These include impossible
old hypotheses, inhabitation of repaired bridges, actual prime witnesses, and
three independent countermodels for the candidate factor assembly. -/
namespace SixBirdsBSD.Verification.Regression

open SixBirdsBSD.Apparatus

/-- Unrestricted multiplicative cancellation forces any absorbing-zero
scalar model to be a singleton. -/
theorem unrestrictedCancellationCollapses
    {Scalar : Type} (zero : Scalar) (mul : Scalar → Scalar → Scalar)
    (hzero : ∀ a, mul a zero = zero)
    (cancel : ∀ a b c, mul a c = mul b c → a = b) (a b : Scalar) : a = b :=
  cancel a b zero ((hzero a).trans (hzero b).symm)

theorem oldCancellationImpossibleOverRat :
    ¬ (∀ a b c : Rat, a * c = b * c → a = b) := by
  intro h
  have h01 : (0 : Rat) = 1 :=
    unrestrictedCancellationCollapses 0 (fun a b : Rat => a * b)
      Rat.mul_zero h 0 1
  exact (by decide : (0 : Rat) ≠ 1) h01

/-- The original arbitrary-pair bridge was inconsistent, not an import. -/
theorem oldStageIIIBridgeImpossible :
    ¬ (∀ XiMot XiSc : Int, XiMot = 0 → XiSc = 0) := by
  intro h
  exact (by decide : (1 : Int) ≠ 0) (h 0 1 rfl)

/-- The repaired bridge has a nonvacuous instance at the intended zero pair. -/
def zeroStageIIIBridge : Vsrc.StageIIIAnalyticHeightBridge 0 0 := ⟨fun _ => rfl⟩

example : (0 : Int) = 0 → (0 : Int) = 0 :=
  (Vsrc.vsrcStageIIITranslation 0 0 zeroStageIIIBridge).2.1

example : ∃ q, SupportPrimeNoGo.IsPrime q ∧ q ∉ [2, 3, 5] :=
  SupportPrimeNoGo.primeOutsideFiniteList [2, 3, 5] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with h | h | h
    all_goals
      subst p
      unfold SupportPrimeNoGo.IsPrime
      refine ⟨by decide, ?_⟩
      intro d hd
      have hbound : d ≤ 5 := by
        have := Nat.le_of_dvd (by decide) hd
        omega
      have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
      rcases hcases with h | h | h | h | h | h
      all_goals subst d; simp_all +decide)

example : SixBirdsBSD.Closure.CoupledFactors.NativeFixity
      SixBirdsBSD.Closure.CoupledFactors.missingLocal ∧
    ¬ SixBirdsBSD.Closure.CoupledFactors.ScalarBSD
      SixBirdsBSD.Closure.CoupledFactors.missingLocal :=
  ⟨SixBirdsBSD.Closure.CoupledFactors.localInputNecessary.1,
    SixBirdsBSD.Closure.CoupledFactors.localInputNecessary.2.2.2⟩

/-- A nontrivial model separating finite logarithm and dual exponential.
These rational coordinates model the typing/duality laws, not local Galois
cohomology of an actual elliptic curve. -/
def toyFiniteComparison : PAdic.FiniteExponentialComparison Rat Rat :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def toyDualComparison :
    PAdic.DualExponentialReciprocity (Rat × Rat) Rat Rat Rat (Rat × Rat) Rat where
  includeFinite := fun h => (h, 0)
  dualExp := fun q => (q, 0)
  expStar := fun h => h.2
  cup := fun h k => h.2 * k.1 - h.1 * k.2
  deRhamPair := fun f q => f * q
  zeroPair := 0
  zeroFil := 0
  reciprocity := by intro h q; change h.2 * q = h.2 * q - h.1 * 0; grind
  finiteOrthogonal := by intro h q; simp [Rat.sub_def]
  deRhamNondegenerate := by
    intro f h
    simpa using h 1

example : Function.Injective toyFiniteComparison.log :=
  PAdic.finiteLogInjective toyFiniteComparison

example : ¬ Function.Injective
    (fun h => toyDualComparison.expStar (toyDualComparison.includeFinite h)) :=
  PAdic.dualExpFiniteNotInjective toyDualComparison 0 1 (by decide)

example : PAdic.pAdicMap (fun (_ : Unit) h log => log h)
      (fun (_ : Unit) (_ : Unit) (_ : Unit) => (0 : Rat))
      (Sum.inl ((), 1, toyFiniteComparison)) = 1 := rfl

open SixBirdsBSD.Closure.AORPrimitives

def toyRegister (status : DischargeStatus) (secondary : List ResidualType) :
    AORInstanceCarrier where
  carrier_id := "toy"
  observations := []
  routes := []
  sources := ["open source"]
  interfaces := []
  constraints := []
  discharges := [⟨.source, secondary, status⟩]
  nonclaims := ["the arithmetic source remains open"]
  nonclaims_nonempty := by decide

/-- Refinement can genuinely enrich the register with new diagnostic roles. -/
theorem diagnosticEnrichment :
    RegisterRefinement (toyRegister .bridged []) (toyRegister .bridged [.role]) := by
  constructor <;> simp [toyRegister, AtomRefines]

/-- A change to zero is excluded by the relation, even if the source name
and nonclaim text remain present. -/
theorem erasureIsNotRefinement :
    ¬ RegisterRefinement (toyRegister .bridged []) (toyRegister .zero []) := by
  intro h
  have he := h.atomsAccounted ⟨.source, [], .zero⟩ (by simp [toyRegister])
  simp [toyRegister, AtomRefines] at he

example : ClosedAORRegister (toyRegister .bridged [.role]) :=
  closedRegisterUnderRefinement
    (by simp [ClosedAORRegister, toyRegister, ClosedStatus]) diagnosticEnrichment

#print axioms SixBirdsBSD.Closure.Landing.strongBSDConditional
#print axioms SixBirdsBSD.Closure.SelShell.piBSDForcesStrongBSD
#print axioms SixBirdsBSD.Closure.SelShell.compositeSignature
#print axioms SixBirdsBSD.Apparatus.SupportPrimeNoGo.finitePrimeCoverNoGo
#print axioms SixBirdsBSD.Apparatus.Vsrc.vsrcStageIIITranslation
#print axioms SixBirdsBSD.Closure.CoupledFactors.assemble
#print axioms SixBirdsBSD.Closure.CoupledFactors.scalarIffCombined
#print axioms SixBirdsBSD.Closure.CoupledFactors.localInputNecessary
#print axioms SixBirdsBSD.Closure.CoupledFactors.coefficientInputNecessary
#print axioms SixBirdsBSD.Closure.CoupledFactors.fixityInputNecessary
#print axioms SixBirdsBSD.Closure.CoupledFactors.compensatingFactorsWork
#print axioms SixBirdsBSD.Closure.CoupledFactors.countermodelsPositive
#print axioms SixBirdsBSD.Closure.CoupledFactors.normalizedFixityAlreadySuffices
#print axioms SixBirdsBSD.Apparatus.PAdic.finiteLogInjective
#print axioms SixBirdsBSD.Apparatus.PAdic.dualExpKillsFinite
#print axioms SixBirdsBSD.Apparatus.PAdic.dualExpFiniteNotInjective
#print axioms SixBirdsBSD.Apparatus.Vsrc.vsrc2VmulAssoc
#print axioms SixBirdsBSD.Apparatus.Vsrc.vsrc2VmulAdd
#print axioms SixBirdsBSD.Apparatus.Vsrc.vsrc2AddVmul
#print axioms SixBirdsBSD.Apparatus.Vsrc.vsrc2SmulVmul
#print axioms SixBirdsBSD.Apparatus.Vsrc.vsrc2VmulSmul
#print axioms SixBirdsBSD.Closure.AORPrimitives.registerRefinementTrans
#print axioms SixBirdsBSD.Closure.AORPrimitives.closedRegisterUnderRefinement

end SixBirdsBSD.Verification.Regression
