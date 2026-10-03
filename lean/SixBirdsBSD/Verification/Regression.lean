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

end SixBirdsBSD.Verification.Regression
