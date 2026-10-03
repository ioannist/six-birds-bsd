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

/-- The Lang-Wake numerical predicate is inhabited away from the excluded
eta anchors. This is only its necessary numerical scope, not a theorem
about an elliptic-curve eta invariant. -/
def langWakeNumericExample : SixBirdsBSD.Closure.EtaApplicability.LangWakeNumericScope 19 5 :=
  ⟨by decide, by decide, by decide +kernel, by decide +kernel, by decide⟩

example : ¬ SixBirdsBSD.Closure.EtaApplicability.LangWakeNumericScope 7 5 :=
  SixBirdsBSD.Closure.EtaApplicability.levelSevenOutsideLangWake 5

example : ¬ SixBirdsBSD.Closure.EtaApplicability.LangWakeNumericScope 11 5 :=
  SixBirdsBSD.Closure.EtaApplicability.levelElevenOutsideLangWake 5

example : ¬ SixBirdsBSD.Apparatus.SupportPrimeNoGo.IsPrime 8 := by decide +kernel

open SixBirdsBSD.Closure.RationalLocalGlobal

/-- Composite-only flags contribute nothing to the prime diagnostic. -/
example : SupportPrimeNoGo.supportPrimeTruncationResidual (fun p => p == 4) 4 = 0 := by
  decide +kernel

example : SupportPrimeNoGo.supportPrimeTruncationResidual (fun _ => true) 10 = 4 := by
  decide +kernel

example : SupportPrimeNoGo.b50ResidualBelow50 .c11a1 = 1 ∧
    SupportPrimeNoGo.b50ResidualBelow50 .c37a1 = 1 ∧
    SupportPrimeNoGo.b50ResidualBelow50 .c121b1 = 1 ∧
    SupportPrimeNoGo.b50ResidualBelow50 .c960d1 = 3 ∧
    SupportPrimeNoGo.b50ResidualBelow50 .c571a1 = 0 := by
  decide +kernel

example : ∃ q, SupportPrimeNoGo.IsPrime q ∧ q ∉ [2, 3, 5] ∧
    SupportPrimeNoGo.AllPrimeRowsCovered SupportPrimeNoGo.coverageBase ∧
    ¬ SupportPrimeNoGo.AllPrimeRowsCovered (SupportPrimeNoGo.coverageVariant q) := by
  obtain ⟨q, hq, hmissing, hbase, hvariant, _⟩ :=
    SupportPrimeNoGo.finitePrimeCoverSeparatesTarget.{0} [2, 3, 5] (by
      intro p hp
      simp at hp
      rcases hp with rfl | rfl | rfl <;> decide +kernel)
  exact ⟨q, hq, hmissing, hbase, hvariant⟩

/-- Both sources are required for exact recovery on the declared {2,3}
support: source A sees prime 2 and source B sees prime 3. -/
example :
    RecoversOnSupport (fun p => p = 2 ∨ p = 3) (fun p => p = 2 ∨ p = 3) ∧
      ¬ RecoversOnSupport (fun p => p = 2 ∨ p = 3) (fun p => p = 2) ∧
      ¬ RecoversOnSupport (fun p => p = 2 ∨ p = 3) (fun p => p = 3) :=
  twoSourcesIndispensable (fun p => p = 2 ∨ p = 3)
    (fun p => p = 2) (fun p => p = 3) (fun _ _ h => h)
    2 3 (by decide +kernel) (by decide +kernel)
    (Or.inl rfl) (Or.inr rfl) (by decide) (by decide)

/-- Positivity is essential for the exact return: -1 is a unit at every
prime but is not one. -/
example : (∀ p, SupportPrimeNoGo.IsPrime p → UnitAt (-1) p) ∧ (-1 : Rat) ≠ 1 := by
  refine ⟨?_, by decide +kernel⟩
  intro p hp
  simpa [UnitAt] using oneUnitAt p hp

/-- The prime 5 is a genuine rational obstruction invisible at primes 2 and 3. -/
example : localRows [2, 3] (5 : Rat) = localRows [2, 3] 1 := by
  funext p hp
  simp at hp
  rcases hp with rfl | rfl <;> unfold localRows <;> decide +kernel

/-- The source-indispensability theorem also reaches the scalar target on
the positive native-factor carrier, using the same explicit private primes. -/
example :
    ForcesScalarOnSupport (fun p => p = 2 ∨ p = 3) (fun p => p = 2 ∨ p = 3) ∧
      ¬ ForcesScalarOnSupport (fun p => p = 2 ∨ p = 3) (fun p => p = 2) ∧
      ¬ ForcesScalarOnSupport (fun p => p = 2 ∨ p = 3) (fun p => p = 3) :=
  twoSourcesIndispensableForScalar (fun p => p = 2 ∨ p = 3)
    (fun p => p = 2) (fun p => p = 3) (fun _ _ h => h)
    2 3 (by decide +kernel) (by decide +kernel)
    (Or.inl rfl) (Or.inr rfl) (by decide) (by decide)

/-- Even checking every odd prime does not remove a possible prime-2
obstruction. No elliptic-curve realization is asserted by this example. -/
example : ¬ ForcesScalarOnSupport (fun p => p = 2) (fun p => p % 2 = 1) :=
  omittedScopePreventsScalarBSD (fun p => p = 2) (fun p => p % 2 = 1)
    2 (by decide +kernel) rfl (by decide)

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
#print axioms SixBirdsBSD.Closure.EtaApplicability.squareRelationForcesHalfValuation
#print axioms SixBirdsBSD.Closure.EtaApplicability.weightTwoCriticalSlopeIncompatible
#print axioms SixBirdsBSD.Closure.EtaApplicability.samePrimeOutsideLangWake
#print axioms SixBirdsBSD.Closure.EtaApplicability.levelThreeOutsideLangWake
#print axioms SixBirdsBSD.Closure.EtaApplicability.levelSevenOutsideLangWake
#print axioms SixBirdsBSD.Closure.EtaApplicability.levelElevenOutsideLangWake
#print axioms SixBirdsBSD.Apparatus.SupportPrimeNoGo.isPrimeIffFiniteCheck
#print axioms SixBirdsBSD.Apparatus.SupportPrimeNoGo.decidableIsPrime
#print axioms SixBirdsBSD.Closure.RationalLocalGlobal.allPrimeUnitsForceOne
#print axioms SixBirdsBSD.Closure.RationalLocalGlobal.unitsOnSupportForceOne
#print axioms SixBirdsBSD.Closure.RationalLocalGlobal.scalarBSDFromPrimeUnits
#print axioms SixBirdsBSD.Closure.RationalLocalGlobal.omittedPrimeWitness
#print axioms SixBirdsBSD.Closure.RationalLocalGlobal.recoversIffCoversSupport
#print axioms SixBirdsBSD.Closure.RationalLocalGlobal.twoSourcesIndispensable
#print axioms SixBirdsBSD.Closure.RationalLocalGlobal.scalarBSDFromTwoScopes
#print axioms SixBirdsBSD.Closure.RationalLocalGlobal.scalarBSDFromPositiveTwoScopes
#print axioms SixBirdsBSD.Closure.RationalLocalGlobal.primeDefectDataProperties
#print axioms SixBirdsBSD.Closure.RationalLocalGlobal.omittedScopePreventsScalarBSD
#print axioms SixBirdsBSD.Closure.RationalLocalGlobal.forcesScalarIffCoversSupport
#print axioms SixBirdsBSD.Closure.RationalLocalGlobal.twoSourcesIndispensableForScalar
#print axioms SixBirdsBSD.Closure.RationalLocalGlobal.fixityNecessaryForUnitAssembly
#print axioms SixBirdsBSD.Closure.RationalLocalGlobal.finitePrimeUnitNoGo
#print axioms SixBirdsBSD.Apparatus.SupportPrimeNoGo.finitePrimeCoverSeparatesTarget
#print axioms SixBirdsBSD.Apparatus.SupportPrimeNoGo.countR4bUpToCongr
#print axioms SixBirdsBSD.Apparatus.NormalizationChecks.pfaffianDependsOnLift
#print axioms SixBirdsBSD.Apparatus.NormalizationChecks.noLiftInvariantNumericalPfaffian
#print axioms SixBirdsBSD.Apparatus.NormalizationChecks.assembledColumnDoubleCounts

example : Closure.CTSignTransport.oddStarkScope 3 := by
  unfold Closure.CTSignTransport.oddStarkScope
  decide +kernel

#print axioms SixBirdsBSD.Closure.CTSignTransport.correctedComparison
#print axioms SixBirdsBSD.Closure.CTSignTransport.twoSignCorrectionsCancel
#print axioms SixBirdsBSD.Closure.CTSignTransport.rawComparisonCannotBePositive
#print axioms SixBirdsBSD.Closure.CTSignTransport.halfPairingCannotDetectNegation
#print axioms SixBirdsBSD.Closure.CTSignTransport.squaredComparisonDoesNotFixSign
#print axioms SixBirdsBSD.Closure.CTSignTransport.oddAndTwoTorsionClassIsZero
#print axioms SixBirdsBSD.Closure.CTSignTransport.oddPrimaryPairedWithTwoTorsionIsZero
#print axioms SixBirdsBSD.Closure.CTSignTransport.halfClassIsNonzeroTwoTorsion
#print axioms SixBirdsBSD.Closure.CTSignTransport.allPrimeUnitsForcePlusMinusOne
#print axioms SixBirdsBSD.Closure.CTSignTransport.allPrimeUnitsIffPlusMinusOne
#print axioms SixBirdsBSD.Closure.CTSignTransport.unsignedUnitAssemblyCanFail
#print axioms SixBirdsBSD.Closure.CTSignTransport.twoOutsideOddStarkScope

#print axioms SixBirdsBSD.Apparatus.FinitePairings.dimensionOnlyShadow
#print axioms SixBirdsBSD.Apparatus.FinitePairings.f2BasisTwo
#print axioms SixBirdsBSD.Apparatus.FinitePairings.f2BasisFourTwoTorsion
#print axioms SixBirdsBSD.Apparatus.FinitePairings.cyclicTargetTwo
#print axioms SixBirdsBSD.Apparatus.FinitePairings.cyclicTargetFour
#print axioms SixBirdsBSD.Apparatus.FinitePairings.cardinalityOnlyShadow
#print axioms SixBirdsBSD.Apparatus.FinitePairings.zeroPairingFailsPerfectness
#print axioms SixBirdsBSD.Apparatus.FinitePairings.noOrderReadoutFromTwoTorsionCount
#print axioms SixBirdsBSD.Apparatus.FinitePairings.noTwoTorsionReadoutFromOrder
#print axioms SixBirdsBSD.Apparatus.FinitePairings.numericalPfaffianChangesWithBasis
#print axioms SixBirdsBSD.Apparatus.FinitePairings.hyperbolicCardinalityNormalization
#print axioms SixBirdsBSD.Apparatus.FiniteSource.dimShaShadow

#print axioms SixBirdsBSD.Apparatus.FinitePresentation.sameResidueIffDifferenceInImage
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.cokernelEquivalence
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.cokernelEquivalenceAdditive
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.cokernelGroupLaws
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.determinantReturnsCokernelOrder
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.pfaffianCongruenceLaw
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.unimodularNormalizedFactor
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.rationalInverse
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.linkingInvariantModuloIntegers
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.recoversPairingTwo
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.recoversPairingFour
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.rawInverseSignMatters
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.finiteBasisChangeHasIntegralRepair
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.singularPresentationFailsInverse
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.modulusOneIsTrivial
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.nonunitChangeFailsNormalization
#print axioms SixBirdsBSD.Apparatus.FinitePresentation.noNormalizedFactorFromTwoTorsionCount

#print axioms SixBirdsBSD.Closure.ChiCTp.chiCTpComparison
#print axioms SixBirdsBSD.Closure.Imports.chiCTpImport.nativeSelectionsAgree
#print axioms SixBirdsBSD.Closure.Imports.chiCTpImport.missingGeneratorPreventsComparison
#print axioms SixBirdsBSD.Closure.Imports.chiCTpImport.missingCTTargetPreventsComparison
#print axioms SixBirdsBSD.Closure.CTInstanceChecks.matchedInstancesReturnDifferentFactors
#print axioms SixBirdsBSD.Closure.CTInstanceChecks.wrongCurveCannotSupplyComparison
#print axioms SixBirdsBSD.Closure.CTInstanceChecks.wrongPrimeCannotSupplyComparison
#print axioms SixBirdsBSD.Closure.CTInstanceChecks.compositeCannotSupplyComparison
#print axioms SixBirdsBSD.Closure.CTInstanceChecks.missingSelectionCannotSupplyComparison
#print axioms SixBirdsBSD.Closure.CTInstanceChecks.applicabilityDoesNotSupplySelections
#print axioms SixBirdsBSD.Closure.CTInstanceChecks.wrongMapFailsNativeReturn
#print axioms SixBirdsBSD.Closure.CTInstanceChecks.comparisonUsesIndexedInstance

#print axioms SixBirdsBSD.Closure.LocalUnitSupport.primaryModelInvariants
#print axioms SixBirdsBSD.Closure.LocalUnitSupport.numericalShallowBranches
#print axioms SixBirdsBSD.Closure.LocalUnitSupport.discriminantPrimeSupport
#print axioms SixBirdsBSD.Closure.LocalUnitSupport.shallowFactorUnitAtOddPlace
#print axioms SixBirdsBSD.Closure.LocalUnitSupport.noExactShallowFactorFromUnitClass
#print axioms SixBirdsBSD.Closure.LocalUnitSupport.noExactCurveBranchReadoutFromUnitClass
#print axioms SixBirdsBSD.Closure.LocalUnitSupport.explicitUnitCongruence
#print axioms SixBirdsBSD.Closure.LocalUnitSupport.badPlaceDoesNotBoundFactorSupport
#print axioms SixBirdsBSD.Closure.LocalUnitSupport.coefficientPrimeRepairsShallowReadout
#print axioms SixBirdsBSD.Closure.LocalUnitSupport.falseBranchControls
#print axioms SixBirdsBSD.Closure.LocalUnitSupport.coefficientPrimeFlagCannotRecoverProducts

#print axioms SixBirdsBSD.Closure.ShaDescent.quarticCoverIdentities
#print axioms SixBirdsBSD.Closure.ShaDescent.curveAndQuarticInvariants
#print axioms SixBirdsBSD.Closure.ShaDescent.fisherJacobianCoordinates
#print axioms SixBirdsBSD.Closure.ShaDescent.fisherCoordinateInverse
#print axioms SixBirdsBSD.Closure.ShaDescent.realSolubilityInputs
#print axioms SixBirdsBSD.Closure.ShaDescent.twoAdicSolubilityInputs
#print axioms SixBirdsBSD.Closure.ShaDescent.badPrimeSolubilityInputs
#print axioms SixBirdsBSD.Closure.ShaDescent.noNonzeroDoubleOfFourTorsion
#print axioms SixBirdsBSD.Closure.ShaDescent.primaryCollapse
#print axioms SixBirdsBSD.Closure.ShaDescent.primaryKernelEquivalence
#print axioms SixBirdsBSD.Closure.ShaDescent.modelTwoPairingHypotheses
#print axioms SixBirdsBSD.Closure.ShaDescent.modelFourFalseControl

#print axioms SixBirdsBSD.Closure.ShaDimensionPair.partnerInvariants
#print axioms SixBirdsBSD.Closure.ShaDimensionPair.halvingEquivalence
#print axioms SixBirdsBSD.Closure.ShaDimensionPair.fourQuadEquivalence
#print axioms SixBirdsBSD.Closure.ShaDimensionPair.enumerateFourFromHalving
#print axioms SixBirdsBSD.Closure.ShaDimensionPair.halvabilityProducesFourEnumeration
#print axioms SixBirdsBSD.Closure.ShaDimensionPair.primaryOrderLowerBound
#print axioms SixBirdsBSD.Closure.ShaDimensionPair.enumerateCollapsedPrimary
#print axioms SixBirdsBSD.Closure.ShaDimensionPair.noPrimaryOrderReadoutFromTwoBasis
#print axioms SixBirdsBSD.Closure.ShaDimensionPair.fourHalvingPositiveControl
#print axioms SixBirdsBSD.Closure.ShaDimensionPair.twoHalvingFalseControl

#print axioms SixBirdsBSD.Closure.ShaFourNormalization.millerNumericalInputs
#print axioms SixBirdsBSD.Closure.ShaFourNormalization.matchedPartnerNumericalInputs
#print axioms SixBirdsBSD.Closure.ShaFourNormalization.primaryCollapseToFour
#print axioms SixBirdsBSD.Closure.ShaFourNormalization.primaryFourEquivalence
#print axioms SixBirdsBSD.Closure.ShaFourNormalization.enumeratePrimaryFromEightStabilization
#print axioms SixBirdsBSD.Closure.ShaFourNormalization.noFiniteFactorReadoutFromCoarseInputs
#print axioms SixBirdsBSD.Closure.ShaFourNormalization.unequalWholeOrdersFromPrimaryLayers
#print axioms SixBirdsBSD.Closure.ShaFourNormalization.noWholeFiniteFactorReadoutFromCoarseInputs
#print axioms SixBirdsBSD.Closure.ShaFourNormalization.eightStabilizationControls
#print axioms SixBirdsBSD.Closure.ShaFourNormalization.formCoefficient
#print axioms SixBirdsBSD.Closure.ShaFourNormalization.nondegenerateCoefficientIsUnit
#print axioms SixBirdsBSD.Closure.ShaFourNormalization.everyPerfectFourFormHasNormalization
#print axioms SixBirdsBSD.Closure.ShaFourNormalization.perfectFourFormIntegralReturn
#print axioms SixBirdsBSD.Closure.ShaFourNormalization.formNormalizationControls

#print axioms SixBirdsBSD.Closure.OddPrimaryBridge.equationAndLocalInputs
#print axioms SixBirdsBSD.Closure.OddPrimaryBridge.ordinaryAtTwoIsAnomalous
#print axioms SixBirdsBSD.Closure.OddPrimaryBridge.matchedPartnerHasLocalAnomaly
#print axioms SixBirdsBSD.Closure.OddPrimaryBridge.anomalousUnitRootControls
#print axioms SixBirdsBSD.Closure.OddPrimaryBridge.frobeniusCartanReturn
#print axioms SixBirdsBSD.Closure.OddPrimaryBridge.cartanFalseControl
#print axioms SixBirdsBSD.Closure.OddPrimaryBridge.threePresentationCohomology
#print axioms SixBirdsBSD.Closure.OddPrimaryBridge.threePairingLaws
#print axioms SixBirdsBSD.Closure.OddPrimaryBridge.everyPerfectThreeFormHasIntegralReturn
#print axioms SixBirdsBSD.Closure.OddPrimaryBridge.squareRootBasisObstruction
#print axioms SixBirdsBSD.Closure.OddPrimaryBridge.fixedSquareMapMissesABasis
#print axioms SixBirdsBSD.Closure.OddPrimaryBridge.unitErasedBasisLosesSquareClass
#print axioms SixBirdsBSD.Closure.OddPrimaryBridge.retainedUnitReturnsSquareClass

#print axioms SixBirdsBSD.Closure.StarkCoreVertices.inertiaInputs
#print axioms SixBirdsBSD.Closure.StarkCoreVertices.frobeniusFourthPowerIsNegative
#print axioms SixBirdsBSD.Closure.StarkCoreVertices.centralNegativeCocycleIsCoboundary
#print axioms SixBirdsBSD.Closure.StarkCoreVertices.transvectionRankOneThree
#print axioms SixBirdsBSD.Closure.StarkCoreVertices.transvectionReturn27
#print axioms SixBirdsBSD.Closure.StarkCoreVertices.unitScalingPreservesPrincipalImages27
#print axioms SixBirdsBSD.Closure.StarkCoreVertices.fittingLadderLosesBasisSquareClass27
#print axioms SixBirdsBSD.Closure.StarkCoreVertices.localisationModelCounts27

#print axioms SixBirdsBSD.Closure.StarkInverseLimit.inverseTwoIdentity
#print axioms SixBirdsBSD.Closure.StarkInverseLimit.twoIsUnit
#print axioms SixBirdsBSD.Closure.StarkInverseLimit.unitScalingPreservesPrincipalImages
#print axioms SixBirdsBSD.Closure.StarkInverseLimit.oneHasSquareRoot
#print axioms SixBirdsBSD.Closure.StarkInverseLimit.twoHasNoSquareRoot
#print axioms SixBirdsBSD.Closure.StarkInverseLimit.noSquareRootReadoutFromIdeal
#print axioms SixBirdsBSD.Closure.StarkInverseLimit.sameEntireIdealFamily
#print axioms SixBirdsBSD.Closure.StarkInverseLimit.noSquareRootReadoutFromIdealFamily

#print axioms SixBirdsBSD.Closure.CTDerivedTransport.explicitChainMap
#print axioms SixBirdsBSD.Closure.CTDerivedTransport.sourceForcedByChainLaw
#print axioms SixBirdsBSD.Closure.CTDerivedTransport.sameCohomologyHomotopy
#print axioms SixBirdsBSD.Closure.CTDerivedTransport.normalizationIsChainMap
#print axioms SixBirdsBSD.Closure.CTDerivedTransport.normalizationDeterminantsAgree
#print axioms SixBirdsBSD.Closure.CTDerivedTransport.normalizationPullsBackDuality
#print axioms SixBirdsBSD.Closure.CTDerivedTransport.cupIsChainMap
#print axioms SixBirdsBSD.Closure.CTDerivedTransport.normalizationLinkingReturn
#print axioms SixBirdsBSD.Closure.CTDerivedTransport.splitBadPrimeInputs
#print axioms SixBirdsBSD.Closure.CTDerivedTransport.splitNodeAndTangents

#print axioms SixBirdsBSD.Closure.StarkCoefficientNaturality.compatibleExt
#print axioms SixBirdsBSD.Closure.StarkCoefficientNaturality.inverseNaturality
#print axioms SixBirdsBSD.Closure.StarkCoefficientNaturality.limitLeftInverse
#print axioms SixBirdsBSD.Closure.StarkCoefficientNaturality.limitRightInverse
#print axioms SixBirdsBSD.Closure.StarkCoefficientNaturality.integralComparisonUnique
#print axioms SixBirdsBSD.Closure.StarkCoefficientNaturality.finiteIsomorphismsNeedNaturality
#print axioms SixBirdsBSD.Closure.StarkCoefficientNaturality.noIntegralLiftForMismatchedComparisons

#print axioms SixBirdsBSD.Closure.CTPfaffianRoot.pairedSkewPresentation
#print axioms SixBirdsBSD.Closure.CTPfaffianRoot.rootTrivializationsCommute
#print axioms SixBirdsBSD.Closure.CTPfaffianRoot.canonicalRootReturn
#print axioms SixBirdsBSD.Closure.CTPfaffianRoot.rootNegationKeepsDeterminant
#print axioms SixBirdsBSD.Closure.CTPfaffianRoot.rawCorrectedRootSigns
#print axioms SixBirdsBSD.Closure.CTPfaffianRoot.actualCoefficientFrameControls

#print axioms SixBirdsBSD.Closure.AdditiveFrobeniusDescent.commonCoverEquations
#print axioms SixBirdsBSD.Closure.AdditiveFrobeniusDescent.residueCoefficientChecks
#print axioms SixBirdsBSD.Closure.AdditiveFrobeniusDescent.goodFiberCounts
#print axioms SixBirdsBSD.Closure.AdditiveFrobeniusDescent.noComponentReadoutFromCoverFrobenius
#print axioms SixBirdsBSD.Closure.AdditiveFrobeniusDescent.jointArithmeticNumericalWitness
#print axioms SixBirdsBSD.Closure.AdditiveFrobeniusDescent.differentFiberControl
#print axioms SixBirdsBSD.Closure.AdditiveFrobeniusDescent.tameCharacterOrders
#print axioms SixBirdsBSD.Closure.AdditiveFrobeniusDescent.markedCharacterRepairsScale
#print axioms SixBirdsBSD.Closure.AdditiveFrobeniusDescent.specializationIterates
#print axioms SixBirdsBSD.Closure.AdditiveFrobeniusDescent.generalizedSpecializationVanishes
#print axioms SixBirdsBSD.Closure.AdditiveFrobeniusDescent.zeroEigenvalueControl

#print axioms SixBirdsBSD.Closure.TameComponentReturn.determinantProduct
#print axioms SixBirdsBSD.Closure.TameComponentReturn.composeAssociative
#print axioms SixBirdsBSD.Closure.TameComponentReturn.traceCyclic
#print axioms SixBirdsBSD.Closure.TameComponentReturn.traceDeterminantReturn
#print axioms SixBirdsBSD.Closure.TameComponentReturn.descentDeterminantBasisInvariant
#print axioms SixBirdsBSD.Closure.TameComponentReturn.shallowInertiaReturn
#print axioms SixBirdsBSD.Closure.TameComponentReturn.companionReturns
#print axioms SixBirdsBSD.Closure.TameComponentReturn.sixCoinvariantsTrivial
#print axioms SixBirdsBSD.Closure.TameComponentReturn.fourImageIffEvenSum
#print axioms SixBirdsBSD.Closure.TameComponentReturn.parityKernelIffImage
#print axioms SixBirdsBSD.Closure.TameComponentReturn.sameParityIffDifferenceInImage
#print axioms SixBirdsBSD.Closure.TameComponentReturn.fourCoinvariantEquivalence
#print axioms SixBirdsBSD.Closure.TameComponentReturn.parityAdds
#print axioms SixBirdsBSD.Closure.TameComponentReturn.twoElementFrobeniusFixed
#print axioms SixBirdsBSD.Closure.TameComponentReturn.threeElementFrobeniusControl
#print axioms SixBirdsBSD.Closure.TameComponentReturn.veluIsogenyPolynomialIdentity
#print axioms SixBirdsBSD.Closure.TameComponentReturn.isogenyBoundaryInputs
#print axioms SixBirdsBSD.Closure.TameComponentReturn.pairingRescalingInputs

#print axioms SixBirdsBSD.Closure.RecognitionSources.oddShallowNondivisibility
#print axioms SixBirdsBSD.Closure.RecognitionSources.numericalScopeControls
#print axioms SixBirdsBSD.Closure.RecognitionSources.gammaPadicDescent.numericApplicability
#print axioms SixBirdsBSD.Closure.RecognitionSources.gammaPadicDescent.p_does_not_divide_c_p_proof
#print axioms SixBirdsBSD.Closure.SelShell.piBSD.padicPrimeScope
#print axioms SixBirdsBSD.Closure.SelShell.piBSD.signedPrimeScope
#print axioms SixBirdsBSD.Closure.GlobalTameProduct.equationInvariants
#print axioms SixBirdsBSD.Closure.GlobalTameProduct.factorPrimes
#print axioms SixBirdsBSD.Closure.GlobalTameProduct.primeDivisorOfPrimeList
#print axioms SixBirdsBSD.Closure.GlobalTameProduct.allPrimeDiscriminantSupport
#print axioms SixBirdsBSD.Closure.GlobalTameProduct.actualShallowPlaces
#print axioms SixBirdsBSD.Closure.GlobalTameProduct.tameCoverInputs
#print axioms SixBirdsBSD.Closure.GlobalTameProduct.nativeProductBasisInvariant
#print axioms SixBirdsBSD.Closure.GlobalTameProduct.nativeProductReturn
#print axioms SixBirdsBSD.Closure.GlobalTameProduct.finiteProfileReturn
#print axioms SixBirdsBSD.Closure.GlobalTameProduct.oddPrimeUnitsMissGlobalFactor
#print axioms SixBirdsBSD.Closure.GlobalTameProduct.shallowPlacesDoNotCoverCoefficientSupport
#print axioms SixBirdsBSD.Closure.GlobalTameProduct.unitFlagsLoseMultiplicity

#print axioms SixBirdsBSD.Closure.CoverBetaRefinement.actualCoverFibers
#print axioms SixBirdsBSD.Closure.CoverBetaRefinement.hasseNumericalControls
#print axioms SixBirdsBSD.Closure.CoverBetaRefinement.frobeniusSquareBezout
#print axioms SixBirdsBSD.Closure.CoverBetaRefinement.squareRelationRequiresZeroTrace
#print axioms SixBirdsBSD.Closure.CoverBetaRefinement.ordinaryCoverSquareIncompatible
#print axioms SixBirdsBSD.Closure.CoverBetaRefinement.ordinaryInverseSquareIncompatible
#print axioms SixBirdsBSD.Closure.CoverBetaRefinement.constructedRefinements
#print axioms SixBirdsBSD.Closure.CoverBetaRefinement.noRefinementFactorFromUnorderedFrobenius
#print axioms SixBirdsBSD.Closure.CoverBetaRefinement.completeRefinementRepair
#print axioms SixBirdsBSD.Closure.CoverBetaRefinement.zeroTraceInverseSquare
#print axioms SixBirdsBSD.Closure.CoverBetaRefinement.finiteRefinementControls
#print axioms SixBirdsBSD.Closure.CoverBetaRefinement.refinementBranchUnique
#print axioms SixBirdsBSD.Closure.CoverBetaRefinement.unramifiedTraceResidues
#print axioms SixBirdsBSD.Closure.CoverBetaRefinement.unramifiedSquareIncompatible

#print axioms SixBirdsBSD.Closure.KummerComponentErasure.quotientRepresentative
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.multipleMembershipReflects
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.inclusionReflectsModRelation
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.quotientInclusionInjective
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.quotientRightInverse
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.quotientLeftInverse
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.kummerImagesEqual
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.oddLevelBezout
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.fourLevelBezout
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.scalarDegreeInverse
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.normalizedCorestrictionLeftInverse
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.oddPrimePowerLevel
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.quotientInclusionReduction
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.twoLevelRightInverse
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.twoLevelLeftInverse
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.twoLevelInverseReduction
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.completedComparison
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.twoComponentKummerImagesEqual
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.entireKummerImageFamilyEqual
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.noMarkedSubgroupReadout
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.coefficientTwoControl
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.evenIntegersKilledQuotient
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.coefficientTwoImageControl
#print axioms SixBirdsBSD.Closure.KummerComponentErasure.actualMarkedPointInputs

#print axioms SixBirdsBSD.Closure.SignedTameTransition.gaussSquarePolynomialIdentity
#print axioms SixBirdsBSD.Closure.SignedTameTransition.quadraticCyclotomicOverlap
#print axioms SixBirdsBSD.Closure.SignedTameTransition.cyclotomicSquareTransition
#print axioms SixBirdsBSD.Closure.SignedTameTransition.nativeUniformizerRelation
#print axioms SixBirdsBSD.Closure.SignedTameTransition.leadingSlopeRepair
#print axioms SixBirdsBSD.Closure.SignedTameTransition.unramifiedPhaseControl
#print axioms SixBirdsBSD.Closure.SignedTameTransition.unramifiedFrobeniusSquareControl
#print axioms SixBirdsBSD.Closure.SignedTameTransition.transitionFactorization
#print axioms SixBirdsBSD.Closure.SignedTameTransition.binomialConstantControls
#print axioms SixBirdsBSD.Closure.SignedTameTransition.squareRootCoefficientsForced
#print axioms SixBirdsBSD.Closure.SignedTameTransition.squareRootCoefficientInputs
#print axioms SixBirdsBSD.Closure.SignedTameTransition.coefficientValuationInputs
#print axioms SixBirdsBSD.Closure.SignedTameTransition.cyclotomicDegreeControl
#print axioms SixBirdsBSD.Closure.SignedTameTransition.normBranchRepair

#print axioms SixBirdsBSD.Closure.SelShell.recognitionAuditLawIffImplication
#print axioms SixBirdsBSD.Closure.SelShell.recognitionAuditLawIffConclusion
#print axioms SixBirdsBSD.Closure.SelShell.recognitionAuditLawControls
#print axioms SixBirdsBSD.Closure.SelShell.selBSDShell.masterApplicabilityFromRule

private def controlPairing (E : Bool) (a b : Int) : Int :=
  if E then a * b else 1

/-- Two fixed instances with an actual additive pairing law. One has the
bilinear multiplication pairing; the other has a constant, nonadditive map.
This is a typing control, not an elliptic-curve arithmetic realization. -/
private def pairingControlContext : SixBirdsBSD.Closure.Imports.aEContext Bool where
  TargetCategory := fun _ => Unit
  Hom := fun _ _ _ => Unit
  SelmerComplex := fun _ => Int
  PairingTarget := fun _ => Int
  pairing := controlPairing
  nekovarSelmerComplexWithIntrinsicCasselsTatePairing := fun _ => True
  burnsFlachMaciasSanoNekovarAESelFormulation := fun _ => True
  pairingBilinearOrCategorical := fun E => ∀ a b c : Int,
    controlPairing E (a + b) c = controlPairing E a c + controlPairing E b c

private def goodPairingControlImport :
    SixBirdsBSD.Closure.Imports.aEImport pairingControlContext true where
  nekovarSelmerComplexWithIntrinsicCasselsTatePairing_proof := True.intro
  burnsFlachMaciasSanoNekovarAESelFormulation_proof := True.intro
  pairingBilinearOrCategorical_proof := by
    intro a b c
    simp [controlPairing, Int.add_mul]

theorem curveMatchedPairingControls :
    Nonempty (SixBirdsBSD.Closure.Imports.aEImport pairingControlContext true) ∧
    ¬ Nonempty (SixBirdsBSD.Closure.Imports.aEImport pairingControlContext false) := by
  constructor
  · exact ⟨goodPairingControlImport⟩
  · apply SixBirdsBSD.Closure.Imports.aEImport.failedPairingPreventsImport
    intro h
    have hbad := h 0 0 0
    simp [controlPairing] at hbad

private def beilinsonControlContext : SixBirdsBSD.Closure.Imports.beilinsonContext Bool where
  rank := fun _ => 2
  ArchimedeanRegulator := fun _ => Rat
  DeterminantLine := fun _ => Rat
  LValueSide := fun _ => Rat
  regulatorToDeterminantLine := fun _ => id
  determinantLValueComparison := fun E => (if E then (2 : Rat) else 3) = 2

/-- Both instances have the same admissible rank. Rank matching alone
cannot transfer the comparison certificate to the other prescribed instance. -/
private def goodBeilinsonControlImport :
    SixBirdsBSD.Closure.Imports.beilinsonImport beilinsonControlContext true where
  rank_ge_two := by decide
  determinantLValueComparison_proof := rfl

theorem curveMatchedBeilinsonControls :
    Nonempty (SixBirdsBSD.Closure.Imports.beilinsonImport beilinsonControlContext true) ∧
    ¬ Nonempty (SixBirdsBSD.Closure.Imports.beilinsonImport beilinsonControlContext false) := by
  constructor
  · exact ⟨goodBeilinsonControlImport⟩
  · apply SixBirdsBSD.Closure.Imports.beilinsonImport.failedComparisonPreventsImport
    exact (by decide : ¬ (3 : Rat) = 2)

#print axioms SixBirdsBSD.Closure.Imports.aEImport.pairingFixed
#print axioms SixBirdsBSD.Closure.Imports.aEImport.failedPairingPreventsImport
#print axioms SixBirdsBSD.Closure.Imports.beilinsonImport.lowRankPreventsComparison
#print axioms SixBirdsBSD.Closure.Imports.beilinsonImport.failedComparisonPreventsImport
#print axioms curveMatchedPairingControls
#print axioms curveMatchedBeilinsonControls


/-- A nontrivial rational scalar model of the full shell. The curve and
formed-data carriers are symbolic, and the named audit predicates are True.
This inhabits the encoded hypotheses for controls; it makes no claim that
the predicates are interpreted arithmetic audits on an elliptic curve. -/
def symbolicShell (rank : Nat) (leading : Rat) (badScope : Nat → Prop) :
    SixBirdsBSD.Closure.SelShell.selBSDShell.{0,0,0,0,0,0} where
  EllipticCurve := Bool
  Scalar := Rat
  LocalLift := Unit
  FormedLayer := Rat
  InvolutiveDatum := Unit
  VisibleReadoutDatum := Unit
  AuditRecordDatum := Unit
  E := true
  analyticRank := rank
  zero := 0
  sub := fun a b => a - b
  mul := fun a b => a * b
  div := fun a b => a / b
  L_derivative_over_factorial := leading
  ShaCard := 1
  Reg_NT := 1
  Omega_E := 1
  Tam := 1
  torsionSquared := 1
  strongBSDRightSide := 1
  strongBSDRightSide_eq := by decide +kernel
  residual := leading - 1
  residual_eq := rfl
  sub_eq_zero_iff := by
    intro a b
    rw [Rat.sub_eq_add_neg]
    constructor
    · intro h
      exact Rat.add_right_cancel (-b) (h.trans (Rat.add_neg_cancel b).symm)
    · intro h
      rw [h]
      exact Rat.add_neg_cancel b
  mulDivLeft := by
    intro a b d
    simp only [Rat.div_def]
    rw [Rat.mul_assoc a d⁻¹ b, Rat.mul_comm d⁻¹ b, ← Rat.mul_assoc a b d⁻¹]
  J_BSD := ()
  Vis_BSD := ()
  Audit_BSD := ()
  closureAssumption := ⟨id, fun _ => rfl⟩
  admissibility := True
  admissibility_proof := True.intro
  antiTautology := True
  antiTautology_proof := True.intro
  lawfulness := True
  lawfulness_proof := True.intro
  additiveBadPrimeInScope := badScope
  inertiaTrivializingLiftInScope := fun _ _ => True
  signedSelmerAdmissiblePrime := fun _ => False
  smuggleAuditPasses := True
  smuggleAuditPasses_proof := True.intro
  masterTheoremApplies := True
  foundationsIVApplicabilityAudit := True
  foundationsIVApplicabilityAudit_proof := True.intro
  masterFromRecognitionAudits :=
    (SixBirdsBSD.Closure.SelShell.recognitionAuditLawIffImplication True True).mpr
      (fun _ => True.intro)
  compositeOperationalPredicate := True
  compositeOperationalPredicate_proof := True.intro
  compositeComputable := True
  compositeComputable_proof := True.intro
  compositeFalsifiable := True
  compositeFalsifiable_proof := True.intro
  genuineDependenceOnFormedBSDLayerData := True
  genuineDependenceOnFormedBSDLayerData_proof := True.intro
  AblationWitness := Unit
  ablatePadicBreaksStrongBSDScalarFactorPackage := fun _ => True
  ablateShaBreaksStrongBSDScalarFactorPackage := fun _ => True
  ablateGZBreaksStrongBSDScalarFactorPackage := fun _ => True
  ablatePadicWitness := ()
  ablatePadicWitness_proof := True.intro
  ablateShaWitness := ()
  ablateShaWitness_proof := True.intro
  ablateGZWitness := ()
  ablateGZWitness_proof := True.intro

/-- The low-rank conditional recognition lane is inhabited. Its local
scopes are empty and its scalar identity is explicit supplied content. -/
def recognizedSymbolicShell :
    SixBirdsBSD.Closure.SelShell.piBSD.{0,0,0,0,0,0,0,0,0,0,0,0} (symbolicShell 0 1 (fun _ => False)) where
  gammaPadicDescentReadout := fun _ _ h _ => False.elim h
  gammaShaPersistenceReadout := fun _ h => False.elim h
  gammaHigherGZFixityReadout := fun h => False.elim (by
    change 2 ≤ 0 at h
    omega)
  lowerRankAnalogLane := fun _ => rfl

theorem recognizedShellReadoutControl :
    (symbolicShell 0 1 (fun _ => False)).residual =
      (symbolicShell 0 1 (fun _ => False)).zero :=
  SixBirdsBSD.Closure.SelShell.piBSDForcesResidualZero _ recognizedSymbolicShell

/-- The same idempotent operator and opaque audit receipts permit a false
scalar target, but the recognition premise then fails. This tests the exact
conditional implication rather than asking idempotence to prove arithmetic. -/
theorem falseTargetRecognitionControl :
    ¬ Nonempty (SixBirdsBSD.Closure.SelShell.piBSD.{0,0,0,0,0,0,0,0,0,0,0,0} (symbolicShell 0 2 (fun _ => False))) ∧
    (symbolicShell 0 2 (fun _ => False)).residual ≠
      (symbolicShell 0 2 (fun _ => False)).zero := by
  constructor
  · rintro ⟨recognition⟩
    have h := recognition.lowerRankAnalogLane (Or.inl rfl)
    exact (by decide : (2 : Rat) ≠ 1) h
  · exact (by decide +kernel : (2 : Rat) - 1 ≠ 0)

/-- Scalar equality does not validate the declared source scopes. Prime
two is a genuine prime, but the padic source requires an odd prime. This is
a control of the unrestricted symbolic shell, not an arithmetic example
within the correctly restricted odd-prime source domain. -/
theorem scalarDoesNotRecoverRecognitionControl :
    (symbolicShell 0 1 (fun p => p = 2)).L_derivative_over_factorial =
      (symbolicShell 0 1 (fun p => p = 2)).strongBSDRightSide ∧
    ¬ Nonempty (SixBirdsBSD.Closure.SelShell.piBSD.{0,0,0,0,0,0,0,0,0,0,0,0} (symbolicShell 0 1 (fun p => p = 2))) := by
  constructor
  · rfl
  · rintro ⟨recognition⟩
    have h := SixBirdsBSD.Closure.SelShell.piBSD.padicPrimeScope
      _ recognition 2 () rfl True.intro
    exact (by decide : (2 : Nat) % 2 ≠ 1) h.2

/-- The readout theorem cannot be strengthened to an unrestricted reverse
construction of all the source records. -/
theorem noUnrestrictedSourceReconstruction :
    ¬ (∀ shell : SixBirdsBSD.Closure.SelShell.selBSDShell.{0,0,0,0,0,0},
      shell.L_derivative_over_factorial = shell.strongBSDRightSide →
      Nonempty (SixBirdsBSD.Closure.SelShell.piBSD.{0,0,0,0,0,0,0,0,0,0,0,0} shell)) := by
  intro h
  exact scalarDoesNotRecoverRecognitionControl.2
    (h _ scalarDoesNotRecoverRecognitionControl.1)


/-- Symbolic imported content for the end-to-end conditional control.
No arithmetic theorem is asserted about the two Bool-labelled instances. -/
private def symbolicChiContext : SixBirdsBSD.Closure.Imports.chiCTpContext Bool where
  finiteSha := fun _ _ => True
  nondegenerateCTPairing := fun _ _ => True
  selmerComplexHypotheses := fun _ _ => True
  primeNotDividingTamagawa := fun _ _ => True
  T_E1 := fun _ _ => True
  T_E2 := fun _ _ => True
  T_E3 := fun _ _ => True
  T_E4 := fun _ _ => True
  T_E5 := fun _ _ => True
  T_E6 := fun _ _ => True
  T_E7 := fun _ _ => True
  T_E8 := fun _ _ => True
  Sigma_NekCT := fun _ _ => 1
  SqrtFittCTDomain := fun _ _ => Unit
  VctpCodomain := fun _ _ => Unit
  sqrtStarkGenerator := fun _ _ => some ()
  h_p_CT := fun _ _ => some ()
  canonicalProperty := fun _ _ f => f () = ()

private def symbolicChiImport :
    SixBirdsBSD.Closure.Imports.chiCTpImport symbolicChiContext true 3 where
  applicability :=
    { prime := by decide
      finiteSha := True.intro
      nondegenerateCTPairing := True.intro
      selmerComplexHypotheses := True.intro
      primeNotDividingTamagawa := True.intro }
  T_E1_proof := True.intro
  T_E2_proof := True.intro
  T_E3_proof := True.intro
  T_E4_proof := True.intro
  T_E5_proof := True.intro
  T_E6_proof := True.intro
  T_E7_proof := True.intro
  T_E8_proof := True.intro
  Sigma_NekCT_eq_plus_one := rfl
  sqrtStarkGenerator := ()
  sqrtStarkGenerator_selected := rfl
  h_p_CT := ()
  h_p_CT_selected := rfl
  canonicalPfaffian := id
  canonicalProperty_proof := rfl
  pfaffianSends := rfl

private def lowRankBIContext : SixBirdsBSD.Closure.Imports.beilinsonContext Bool :=
  { beilinsonControlContext with rank := fun _ => 0 }

/-- The complete conditional landing has an inhabited low-rank instance
while its higher-rank comparison record is uninhabited. This exercises the
rank gate and all three curve-indexed headline import interfaces. -/
theorem lowRankConditionalLandingControl :
    ¬ Nonempty (SixBirdsBSD.Closure.Imports.beilinsonImport lowRankBIContext true) ∧
    (symbolicShell 0 1 (fun _ => False)).L_derivative_over_factorial =
      (symbolicShell 0 1 (fun _ => False)).strongBSDRightSide := by
  constructor
  · exact SixBirdsBSD.Closure.Imports.beilinsonImport.lowRankPreventsComparison (by decide)
  · have h := SixBirdsBSD.Closure.Landing.strongBSDConditional
      (symbolicShell 0 1 (fun _ => False))
      (symbolicShell 0 1 (fun _ => False)).closureAssumption rfl
      recognizedSymbolicShell symbolicChiContext 3 symbolicChiImport
      pairingControlContext goodPairingControlImport lowRankBIContext
      (fun hr => False.elim (by change 2 ≤ 0 at hr; omega))
    exact h.1


/-- Normalized fixity is explicit supplied content in this higher-rank
symbolic control. None of its predicates is asserted about an actual curve. -/
private def goodGZControl :
    SixBirdsBSD.Closure.RecognitionSources.gammaHigherGZFixity.{0,0}
      Bool Rat 0 (fun a b => a-b) (fun a b => a*b) where
  E := true
  analyticRank := 2
  analyticRank_ge_two := by decide
  nonCM := True
  nonCM_proof := True.intro
  L_derivative_over_factorial := 1
  kappa_r_E := 1
  Reg_NT_E := 1
  Omega_E := 1
  Tam_E := 1
  psi_minus := 0
  antiInvariantReadout_eq := by decide +kernel
  higherGZFixity := (0 : Rat) = 0
  higherGZFixity_iff_psi_minus_eq_zero := Iff.rfl
  higherGZFixity_proof := rfl
  equivalentRankIdentity := (0 : Rat) = 0
  equivalentRankIdentity_iff_fixity := Iff.rfl
  f14DualityFixity := True
  f14DualityFixity_proof := True.intro
  f27ConservationAsOrbitDescent := True
  f27ConservationAsOrbitDescent_proof := True.intro
  f40AnomalySymmetryObstruction := True
  f40AnomalySymmetryObstruction_proof := True.intro
  stage6_FP_trace_ii := True
  stage6_FP_trace_ii_proof := True.intro
  stage6_SAU_trace_iii := True
  stage6_SAU_trace_iii_proof := True.intro
  stage6_VDE_trace_ii := True
  stage6_VDE_trace_ii_proof := True.intro

private def recognizedHighRankShell :
    SixBirdsBSD.Closure.SelShell.piBSD.{0,0,0,0,0,0,0,0,0,0,0,0}
      (symbolicShell 2 1 (fun _ => False)) where
  gammaPadicDescentReadout := fun _ _ h _ => False.elim h
  gammaShaPersistenceReadout := fun _ h => False.elim h
  gammaHigherGZFixityReadout := fun _ => ⟨goodGZControl, by
    dsimp [goodGZControl, symbolicShell]
    decide +kernel⟩
  lowerRankAnalogLane := fun h => False.elim (by
    change 2 = 0 ∨ 2 = 1 at h
    omega)

/-- The higher-rank branch of the complete conditional landing consumes
curve-matched normalized fixity and the rank-matched comparison import. -/
theorem highRankConditionalLandingControl :
    (symbolicShell 2 1 (fun _ => False)).L_derivative_over_factorial =
      (symbolicShell 2 1 (fun _ => False)).strongBSDRightSide := by
  have h := SixBirdsBSD.Closure.Landing.strongBSDConditional
    (symbolicShell 2 1 (fun _ => False))
    (symbolicShell 2 1 (fun _ => False)).closureAssumption rfl
    recognizedHighRankShell symbolicChiContext 3 symbolicChiImport
    pairingControlContext goodPairingControlImport beilinsonControlContext
    (fun _ => ⟨goodBeilinsonControlImport, rfl⟩)
  exact h.1

/-- Changing the leading coefficient defeats the normalized higher-rank
recognition premise. The other shell data and closure operator are retained. -/
theorem falseHighRankRecognitionControl :
    ¬ Nonempty (SixBirdsBSD.Closure.SelShell.piBSD.{0,0,0,0,0,0,0,0,0,0,0,0}
      (symbolicShell 2 2 (fun _ => False))) := by
  rintro ⟨recognition⟩
  have h := SixBirdsBSD.Closure.SelShell.piBSDForcesStrongBSD _ recognition
  exact (by decide : (2 : Rat) ≠ 1) h

#print axioms recognizedShellReadoutControl
#print axioms falseTargetRecognitionControl
#print axioms scalarDoesNotRecoverRecognitionControl
#print axioms noUnrestrictedSourceReconstruction
#print axioms lowRankConditionalLandingControl
#print axioms highRankConditionalLandingControl
#print axioms falseHighRankRecognitionControl

#print axioms SixBirdsBSD.Closure.CoupledFactors.comparisonsEquivalentUnderScalar
#print axioms SixBirdsBSD.Closure.CoupledFactors.fullPackageIffLocalUnderScalar
#print axioms SixBirdsBSD.Closure.CoupledFactors.fullPackageIffCoefficientUnderScalar
#print axioms SixBirdsBSD.Closure.CoupledFactors.positiveComparisonFiber
#print axioms SixBirdsBSD.Closure.CoupledFactors.comparisonFiberParameterUnique
#print axioms SixBirdsBSD.Closure.CoupledFactors.positiveGaugeReturns
#print axioms SixBirdsBSD.Closure.CoupledFactors.positiveGaugePackageIffOne
#print axioms SixBirdsBSD.Closure.CoupledFactors.positiveGaugeLensConstant
#print axioms SixBirdsBSD.Closure.CoupledFactors.noFullPackageFromScalarLens
#print axioms SixBirdsBSD.Closure.CoupledFactors.comparisonZeroControls


private def heightControlMatrix : HeightRegulator.SymmetricHeight2 Rat := ⟨2,1,3⟩

/-- A genuinely fractional derived row, with pre-source energy 17/25,
instantiates the generalized Schur theorem. -/
theorem fractionalHeightSchurControl :
    HeightRegulator.dot (HeightRegulator.logDetRow2 heightControlMatrix)
      (HeightRegulator.logDetRow2 heightControlMatrix) = (17/25 : Rat) ∧
    HeightRegulator.dot (HeightRegulator.logDetRow2 heightControlMatrix)
      (HeightRegulator.logDetRow2 heightControlMatrix) -
      HeightRegulator.dot (HeightRegulator.logDetRow2 heightControlMatrix)
        (HeightRegulator.mulVec HeightRegulator.heightKLL
          (HeightRegulator.logDetRow2 heightControlMatrix)) = 0 := by
  constructor
  · decide +kernel
  · exact HeightRegulator.heightDifferentialSchurCollapse heightControlMatrix (by decide +kernel)

/-- The off-diagonal vech coordinate appears twice in the matrix trace. -/
theorem offDiagonalHeightControl :
    HeightRegulator.dot (HeightRegulator.logDetRow2 heightControlMatrix)
      (HeightRegulator.tangentCoordinates2 (⟨0,1,0⟩ : HeightRegulator.SymmetricHeight2 Rat)) =
      (-2/5 : Rat) ∧
    HeightRegulator.dot (HeightRegulator.logDetRow2 heightControlMatrix)
      (HeightRegulator.tangentCoordinates2 (⟨0,1,0⟩ : HeightRegulator.SymmetricHeight2 Rat)) ≠
      (-1/5 : Rat) := by decide +kernel

/-- Totalized division at a singular matrix does not create an inverse. -/
theorem singularHeightInverseControl :
    let H : HeightRegulator.SymmetricHeight2 Rat := ⟨1,1,1⟩
    HeightRegulator.det2 H = 0 ∧
      H.a*(HeightRegulator.inverse2 H).a + H.b*(HeightRegulator.inverse2 H).b ≠ 1 := by
  decide +kernel

/-- Both unimodular orientations preserve the regulator, while an index-two
basis scaling multiplies it by four. This is an exact matrix control. -/
theorem heightBasisChangeControls :
    HeightRegulator.det2 heightControlMatrix = (5 : Rat) ∧
    HeightRegulator.det2 (HeightRegulator.heightBasisChange heightControlMatrix 1 1 0 1) = 5 ∧
    HeightRegulator.det2 (HeightRegulator.heightBasisChange heightControlMatrix 0 1 1 0) = 5 ∧
    HeightRegulator.det2 (HeightRegulator.heightBasisChange heightControlMatrix 2 0 0 1) = 20 ∧
    HeightRegulator.det2 (HeightRegulator.heightBasisChange heightControlMatrix 2 0 0 1) ≠ 5 := by
  decide +kernel

#print axioms SixBirdsBSD.Apparatus.HeightRegulator.heightSchurCollapse
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.heightKLLSymmetric
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.heightIdentityLeftProduct
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.heightIdentityRightProduct
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.heightIdentityTranspose
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.heightIdentityPenrose
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.heightIdentityPenroseUnique
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.heightZeroRank
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.determinantVariationPolynomial
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.inverse2Correct
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.logDetRow2Correct
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.heightDifferentialSchurCollapse
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.determinantBasisChange
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.unimodularRegulatorInvariant
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.heightPairing2Symmetric
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.heightPairing2Additive
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.heightPairing2Scalar
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.heightRegulatorMapRank2
#print axioms SixBirdsBSD.Apparatus.HeightRegulator.heightBasisChangeFromPairing
#print axioms fractionalHeightSchurControl
#print axioms offDiagonalHeightControl
#print axioms singularHeightInverseControl
#print axioms heightBasisChangeControls

/-- Closing a false pair changes BOTH scalar values. Closedness of the
returned pair cannot establish BSD for the unchanged original pair. -/
theorem scalarClosureFalseTargetControl :
    SixBirdsBSD.Closure.ScalarClosure.average ((2 : Rat),1) = (3/2,3/2) ∧
    SixBirdsBSD.Closure.ScalarClosure.residual
      (SixBirdsBSD.Closure.ScalarClosure.average ((2 : Rat),1)) = 0 ∧
    SixBirdsBSD.Closure.ScalarClosure.residual ((2 : Rat),1) ≠ 0 ∧
    ¬ ClosureOp.IsClosed
      (SixBirdsBSD.Closure.ScalarClosure.scalarClosure (R := Rat) (by decide))
      ((2 : Rat),1) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  rw [SixBirdsBSD.Closure.ScalarClosure.scalarClosedIffEqual]
  decide

/-- Recognition fixes the input pair on both inhabited rank branches. -/
theorem recognizedPairClosureControl :
    ClosureOp.IsClosed
      (SixBirdsBSD.Closure.ScalarClosure.scalarClosure (R := Rat) (by decide))
      (SixBirdsBSD.Closure.ScalarClosure.shellPair (symbolicShell 0 1 (fun _ => False))) ∧
    ClosureOp.IsClosed
      (SixBirdsBSD.Closure.ScalarClosure.scalarClosure (R := Rat) (by decide))
      (SixBirdsBSD.Closure.ScalarClosure.shellPair (symbolicShell 2 1 (fun _ => False))) := by
  constructor
  · letI : Lean.Grind.Field (symbolicShell 0 1 (fun _ => False)).Scalar :=
      inferInstanceAs (Lean.Grind.Field Rat)
    exact SixBirdsBSD.Closure.ScalarClosure.recognitionFixesShellPair
      (symbolicShell 0 1 (fun _ => False)) (by change (2 : Rat) ≠ 0; decide)
      recognizedSymbolicShell
  · letI : Lean.Grind.Field (symbolicShell 2 1 (fun _ => False)).Scalar :=
      inferInstanceAs (Lean.Grind.Field Rat)
    exact SixBirdsBSD.Closure.ScalarClosure.recognitionFixesShellPair
      (symbolicShell 2 1 (fun _ => False)) (by change (2 : Rat) ≠ 0; decide)
      recognizedHighRankShell

#print axioms SixBirdsBSD.Closure.ScalarClosure.swapInvolutive
#print axioms SixBirdsBSD.Closure.ScalarClosure.residualSwap
#print axioms SixBirdsBSD.Closure.ScalarClosure.averageIdempotent
#print axioms SixBirdsBSD.Closure.ScalarClosure.scalarClosure
#print axioms SixBirdsBSD.Closure.ScalarClosure.averageConservesSum
#print axioms SixBirdsBSD.Closure.ScalarClosure.averageSwapInvariant
#print axioms SixBirdsBSD.Closure.ScalarClosure.averageUnique
#print axioms SixBirdsBSD.Closure.ScalarClosure.averageResidualZero
#print axioms SixBirdsBSD.Closure.ScalarClosure.scalarClosedIffEqual
#print axioms SixBirdsBSD.Closure.ScalarClosure.scalarClosedIffResidualZero
#print axioms SixBirdsBSD.Closure.ScalarClosure.averagePreservesFirstIffClosed
#print axioms SixBirdsBSD.Closure.ScalarClosure.characteristicTwoControl
#print axioms SixBirdsBSD.Closure.ScalarClosure.shellClosedIffStrongBSD
#print axioms SixBirdsBSD.Closure.ScalarClosure.shellClosedIffResidualZero
#print axioms SixBirdsBSD.Closure.ScalarClosure.recognitionFixesShellPair
#print axioms scalarClosureFalseTargetControl
#print axioms recognizedPairClosureControl

/-- The field normalization uses a fractional Sha/torsion-square ratio
and returns the same nonintegral leading term in both product conventions. -/
theorem fractionalKappaControl :
    (3/2 : Rat)*(4/3)*6=12 ∧
    (4/9 : Rat)*((3/2)*(4/3)*6)=16/3 ∧
    ((((4 : Rat)*(4/3))*(3/2))*6)/9=16/3 ∧
    ((((4 : Rat)*(4/3))*(3/2))*6)/3 ≠ 16/3 := by
  decide +kernel

/-- A zero common factor cannot determine kappa. -/
theorem zeroCommonKappaControl :
    (1 : Rat)*((0 : Rat)*1*1) = (2 : Rat)*((0 : Rat)*1*1) ∧
    (1 : Rat) ≠ 2 := by
  decide +kernel

/-- Totalized quotient comparison at zero does not license clearing its
denominator. The two products agree but the cross-product equation fails. -/
theorem zeroDenominatorKappaControl :
    (0 : Rat)*(1*1*1) = ((4*1)*1)*1/0 ∧
    (0 : Rat)=4/0 ∧ (0 : Rat)*0 ≠ 4 := by
  decide +kernel

/-- Ordinary nonzero field factors construct the cancellation package
used by the existing composite-signature theorem. -/
def fieldFactorCancellationControl :
    SixBirdsBSD.Closure.SelShell.FactorCancellation
      (symbolicShell 0 1 (fun _ => False)) := by
  letI : Lean.Grind.Field (symbolicShell 0 1 (fun _ => False)).Scalar :=
    inferInstanceAs (Lean.Grind.Field Rat)
  exact SixBirdsBSD.Closure.SelShell.factorCancellationFromField
    _ rfl rfl (by change (1 : Rat) ≠ 0; decide)
    (by change (1 : Rat) ≠ 0; decide)
    (by change (1 : Rat) ≠ 0; decide)
    (by change (1 : Rat) ≠ 0; decide)
    (by change (1 : Rat) ≠ 0; decide)

#print axioms SixBirdsBSD.Apparatus.KappaNormalization.kappaNormalizationOverField
#print axioms SixBirdsBSD.Apparatus.KappaNormalization.commonFactorNonzero
#print axioms SixBirdsBSD.Apparatus.KappaNormalization.cascadeProductIffNormalization
#print axioms SixBirdsBSD.Apparatus.KappaNormalization.normalizationIffCrossProduct
#print axioms SixBirdsBSD.Apparatus.KappaNormalization.cascadeProductIffCrossProduct
#print axioms SixBirdsBSD.Apparatus.KappaNormalization.normalizedLeadingFormsEquivalent
#print axioms SixBirdsBSD.Closure.SelShell.factorCancellationFromField
#print axioms fractionalKappaControl
#print axioms zeroCommonKappaControl
#print axioms zeroDenominatorKappaControl
#print axioms fieldFactorCancellationControl

/-- Nonzero factors and their derived cancellation laws alone do not
prove the BSD scalar target; recognition still carries substantive content. -/
theorem fieldCancellationFalseTargetControl :
    SixBirdsBSD.Closure.SelShell.FactorCancellation
      (symbolicShell 0 2 (fun _ => False)) ∧
    (symbolicShell 0 2 (fun _ => False)).L_derivative_over_factorial ≠
      (symbolicShell 0 2 (fun _ => False)).strongBSDRightSide := by
  constructor
  · letI : Lean.Grind.Field (symbolicShell 0 2 (fun _ => False)).Scalar :=
      inferInstanceAs (Lean.Grind.Field Rat)
    apply (SixBirdsBSD.Closure.SelShell.factorCancellationIffNonzero _ rfl rfl).mpr
    change (1 : Rat) ≠ 0 ∧ (1 : Rat) ≠ 0 ∧ (1 : Rat) ≠ 0 ∧
      (1 : Rat) ≠ 0 ∧ (1 : Rat) ≠ 0
    decide
  · change (2 : Rat) ≠ 1
    decide

#print axioms SixBirdsBSD.Closure.SelShell.factorCancellationIffNonzero
#print axioms fieldCancellationFalseTargetControl

/-- Two false leading-term equations can be logically equivalent at a
fixed input without their normalization coefficients agreeing. -/
theorem fixedLeadingEquivalenceControl :
    (((0 : Rat)=1) ↔ ((0 : Rat)=2)) ∧ (1 : Rat) ≠ 2 := by
  decide +kernel

#print axioms SixBirdsBSD.Apparatus.KappaNormalization.allLeadingFormsIffNormalization
#print axioms fixedLeadingEquivalenceControl

/-- A symbolic stack for testing the exact legacy cascade dependency.
The True fields are formal receipts, not arithmetic theorem instances. -/
private def trueCascadeImport : SixBirdsBSD.Closure.TCascade.tCascadeImport where
  T_E1 := True
  T_E1_proof := True.intro
  T_E2 := True
  T_E2_proof := True.intro
  T_E3 := True
  T_E3_proof := True.intro
  T_E4 := True
  T_E4_proof := True.intro
  T_E5 := True
  T_E5_proof := True.intro
  T_E6 := True
  T_E6_proof := True.intro
  T_E7 := True
  T_E7_proof := True.intro
  T_E8 := True
  T_E8_proof := True.intro
  T_CM1 := True
  T_CM1_proof := True.intro
  T_CM2 := True
  T_CM2_proof := True.intro
  T_CM3 := True
  T_CM3_proof := True.intro
  T_CM4 := True
  T_CM4_proof := True.intro
  T_CM5 := True
  T_CM5_proof := True.intro
  T_CM6 := True
  T_CM6_proof := True.intro
  T_SS1 := True
  T_SS1_proof := True.intro
  T_SS2 := True
  T_SS2_proof := True.intro
  T_SS3 := True
  T_SS3_proof := True.intro
  T_SS4 := True
  T_SS4_proof := True.intro
  T_SS5 := True
  T_SS5_proof := True.intro
  T_SS6 := True
  T_SS6_proof := True.intro
  T_SS7 := True
  T_SS7_proof := True.intro
  T_ARC1 := True
  T_ARC1_proof := True.intro
  T_ARC2 := True
  T_ARC2_proof := True.intro
  T_ARC3 := True
  T_ARC3_proof := True.intro
  T_ARC4 := True
  T_ARC4_proof := True.intro
  T_ARC5 := True
  T_ARC5_proof := True.intro
  T_ARC6 := True
  T_ARC6_proof := True.intro
  T_UNI1 := True
  T_UNI1_proof := True.intro
  T_UNI2 := True
  T_UNI2_proof := True.intro
  T_UNI3 := True
  T_UNI3_proof := True.intro
  T_UNI4 := True
  T_UNI4_proof := True.intro
  T_UNI5 := True
  T_UNI5_proof := True.intro
  T_UNI6 := True
  T_UNI6_proof := True.intro
  T_UNI7 := True
  T_UNI7_proof := True.intro
  T_nC1 := True
  T_nC1_proof := True.intro
  T_nC2 := True
  T_nC2_proof := True.intro
  T_nC3 := True
  T_nC3_proof := True.intro
  T_nC4 := True
  T_nC4_proof := True.intro
  T_nC5 := True
  T_nC5_proof := True.intro
  T_nC6 := True
  T_nC6_proof := True.intro

/-- False branches allow a vacuous comparison rule, while a true branch
cannot produce a false valuation comparison from the supplied stack. -/
theorem cascadeComparisonRuleControls :
    SixBirdsBSD.Closure.TCascade.CascadeAuditRule Unit Unit trueCascadeImport False False ∧
    ¬ SixBirdsBSD.Closure.TCascade.CascadeAuditRule Unit Unit trueCascadeImport True False := by
  constructor
  · exact (SixBirdsBSD.Closure.TCascade.cascadeAuditRuleIffImplication
      () () trueCascadeImport False False).mpr id
  · intro h
    exact (SixBirdsBSD.Closure.TCascade.cascadeAuditRuleIffImplication
      () () trueCascadeImport True False).mp h True.intro

#print axioms SixBirdsBSD.Closure.TCascade.cascadeAuditRuleIffImplication
#print axioms SixBirdsBSD.Closure.TCascade.tCascadeRankLeOne
#print axioms cascadeComparisonRuleControls

/-- Inhabitation of the bound index matters for eliminating the adapter.
With an empty curve carrier it holds vacuously even for True -> False. -/
theorem emptyCurveCascadeRuleControl :
    SixBirdsBSD.Closure.TCascade.CascadeAuditRule Empty Unit
      trueCascadeImport True False := by
  intro E
  cases E

#print axioms emptyCurveCascadeRuleControl

open SixBirdsBSD.Closure.ArithmeticClosureBridge
open SixBirdsBSD.Closure.ScalarClosure

/-- A larger carrier with a genuinely forgotten coordinate. -/
def fiberClosure : SixBirdsBSD.F1ClosureOp ((Rat × Rat) × Rat) where
  toFun := fun x => (average x.1, 0)
  idempotent := by
    intro x
    apply Prod.ext
    · exact averageIdempotent (by decide : (2 : Rat) ≠ 0) x.1
    · rfl

theorem fiberReadoutIntertwines : ReadoutIntertwines fiberClosure Prod.fst :=
  fun _ => rfl

/-- Scalar equality leaves full-layer information undetermined, even
under an actually constructed uniform intertwining comparison. -/
theorem scalarClosedDoesNotImplyFormedClosed :
    ClosureOp.IsClosed (scalarClosure (by decide : (2 : Rat) ≠ 0))
      ((1 : Rat), 1) ∧
    ¬ ClosureOp.IsClosed fiberClosure (((1 : Rat), 1), 1) := by
  constructor
  · exact (scalarClosedIffEqual (by decide) _).mpr rfl
  · intro h
    have hLast := congrArg Prod.snd h
    exact (by decide : (0 : Rat) ≠ 1) hLast

/-- Intertwining and idempotence do not fix a false original readout. -/
theorem intertwiningDoesNotProveOriginalBSD :
    ReadoutIntertwines fiberClosure Prod.fst ∧
    ¬ ClosureOp.IsClosed fiberClosure (((2 : Rat), 1), 0) ∧
    ¬ ((2 : Rat) = 1) ∧
    ClosureOp.IsClosed fiberClosure (fiberClosure (((2 : Rat), 1), 0)) := by
  refine ⟨fiberReadoutIntertwines, ?_, by decide,
    ClosureOp.closure_isClosed fiberClosure _⟩
  intro h
  have hEq := formedClosedImpliesEqual (by decide : (2 : Rat) ≠ 0)
    fiberClosure Prod.fst fiberReadoutIntertwines (((2 : Rat), 1), 0) h
  exact (by decide : (2 : Rat) ≠ 1) hEq

/-- An unrelated identity closure can fix the entire state while its
observed analytic/arithmetic entries disagree. The comparison is essential. -/
def unrelatedClosure : SixBirdsBSD.F1ClosureOp (Rat × Rat) := ⟨id, fun _ => rfl⟩

theorem unrelatedClosedStateDoesNotProveBSD :
    ClosureOp.IsClosed unrelatedClosure ((2 : Rat), 1) ∧
    ¬ ReadoutIntertwines unrelatedClosure id := by
  refine ⟨rfl, ?_⟩
  intro hCompare
  have hEq := formedClosedImpliesEqual (by decide : (2 : Rat) ≠ 0)
    unrelatedClosure id hCompare ((2 : Rat), 1) rfl
  exact (by decide : (2 : Rat) ≠ 1) hEq

/-- The exact-data verifier distinguishes the original pair from the
repaired output; it is not an arithmetic source-construction algorithm. -/
theorem exactScalarVerifierControls :
    verifyScalarReadout ((1 : Rat), 1) = true ∧
    verifyScalarReadout ((2 : Rat), 1) = false ∧
    verifyScalarReadout (average ((2 : Rat), 1)) = true := by decide +kernel

#print axioms SixBirdsBSD.Closure.ScalarBSD.normalizedFixityForcesScalarBSD
#print axioms SixBirdsBSD.Closure.ScalarBSD.rankGatedRecognitionForcesScalarBSD
#print axioms observedClosedIffEqual
#print axioms formedClosedImpliesEqual
#print axioms formedClosedIffEqualOfInjective
#print axioms formedClosureForcesStrongBSD
#print axioms recognitionFixesFormedReadout
#print axioms verifyScalarReadoutIffClosed
#print axioms fiberClosure
#print axioms fiberReadoutIntertwines
#print axioms scalarClosedDoesNotImplyFormedClosed
#print axioms intertwiningDoesNotProveOriginalBSD
#print axioms unrelatedClosedStateDoesNotProveBSD
#print axioms exactScalarVerifierControls

end SixBirdsBSD.Verification.Regression
