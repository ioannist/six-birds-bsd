import Init.Data.Rat.Lemmas
import SixBirdsBSD.Apparatus.SupportPrimeNoGo
import SixBirdsBSD.Closure.CoupledFactors

/-!
An exact local-to-global return and prime-omission witnesses on actual positive
rational numbers. These results do not identify the quotient with an arithmetic
object attached to an elliptic curve or supply the named recognition sources.
-/
namespace SixBirdsBSD.Closure.RationalLocalGlobal

open SixBirdsBSD.Apparatus.SupportPrimeNoGo
open SixBirdsBSD.Closure.CoupledFactors

/-- A reduced rational number is a unit at a prime exactly when neither its
numerator nor denominator is divisible by that prime. No p-adic field is
constructed here: this is the explicit divisibility predicate used below. -/
def UnitAt (r : Rat) (p : Nat) : Prop :=
  ¬ p ∣ r.num.natAbs ∧ ¬ p ∣ r.den

instance (r : Rat) (p : Nat) : Decidable (UnitAt r p) :=
  inferInstanceAs (Decidable (¬ p ∣ r.num.natAbs ∧ ¬ p ∣ r.den))

private theorem natEqOneOfNoPrimeDivisor (n : Nat) (hn : 0 < n)
    (h : ∀ p, IsPrime p → ¬ p ∣ n) : n = 1 := by
  by_cases hne : n = 1
  · exact hne
  · obtain ⟨p, hp, hpn⟩ := existsPrimeDivisor n (by omega)
    exact False.elim (h p hp hpn)

theorem oneUnitAt (p : Nat) (hp : IsPrime p) : UnitAt 1 p := by
  have hnot : ¬ p ∣ 1 := by
    intro h
    have := Nat.le_of_dvd (by decide) h
    have := hp.1
    omega
  simpa [UnitAt] using And.intro hnot hnot

/-- Positivity removes the sign ambiguity: a rational unit at every prime is
exactly one. The proof uses prime divisors of the actual reduced numerator
and denominator, rather than abstract valuation labels. -/
theorem allPrimeUnitsForceOne (r : Rat) (hpos : 0 < r)
    (h : ∀ p, IsPrime p → UnitAt r p) : r = 1 := by
  have hnumpos : 0 < r.num := by
    have hnonneg : 0 ≤ r.num := Rat.num_nonneg.mpr (Rat.le_of_lt hpos)
    have hne : r.num ≠ 0 := by
      intro hz
      have hr := Rat.num_eq_zero.mp hz
      rw [hr] at hpos
      exact Rat.lt_irrefl hpos
    omega
  have habs : r.num.natAbs = 1 :=
    natEqOneOfNoPrimeDivisor _ (Int.natAbs_pos.mpr (by omega))
      (fun p hp => (h p hp).1)
  have hden : r.den = 1 :=
    natEqOneOfNoPrimeDivisor _ r.den_pos (fun p hp => (h p hp).2)
  apply Rat.ext
  · have hcast := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr (Rat.le_of_lt hpos))
    rw [habs] at hcast
    simpa using hcast.symm
  · simpa using hden

theorem allPrimeUnitsIffOne (r : Rat) (hpos : 0 < r) :
    (∀ p, IsPrime p → UnitAt r p) ↔ r = 1 := by
  constructor
  · exact allPrimeUnitsForceOne r hpos
  · intro h p hp
    rw [h]
    exact oneUnitAt p hp

/-- An independently proved bound on all prime divisors of the quotient.
This is a substantive support hypothesis, not inferred from finitely many
successful local checks. -/
def SupportedOn (r : Rat) (scope : Nat → Prop) : Prop :=
  ∀ p, IsPrime p → (p ∣ r.num.natAbs ∨ p ∣ r.den) → scope p

theorem unitsOnSupportForceOne (r : Rat) (hpos : 0 < r)
    (scope : Nat → Prop) (hsupport : SupportedOn r scope)
    (hunits : ∀ p, IsPrime p → scope p → UnitAt r p) : r = 1 := by
  apply allPrimeUnitsForceOne r hpos
  intro p hp
  by_cases hs : scope p
  · exact hunits p hp hs
  · constructor
    · intro hd
      exact hs (hsupport p hp (Or.inl hd))
    · intro hd
      exact hs (hsupport p hp (Or.inr hd))

/-- Two source scopes suffice when their union contains every prime in the
independently established support of the actual rational quotient. -/
theorem twoScopesForceOne (r : Rat) (hpos : 0 < r)
    (scopeA scopeB : Nat → Prop)
    (hsupport : SupportedOn r (fun p => scopeA p ∨ scopeB p))
    (hA : ∀ p, IsPrime p → scopeA p → UnitAt r p)
    (hB : ∀ p, IsPrime p → scopeB p → UnitAt r p) : r = 1 := by
  apply unitsOnSupportForceOne r hpos _ hsupport
  intro p hp hs
  exact hs.elim (hA p hp) (hB p hp)

/-- The joint comparison quotient before either scalar normalization. -/
def comparisonQuotient (d : FactorData) : Rat :=
  (d.coefficient * d.nativeLocal) / ((d.sha / d.torsionSquared) * d.tamagawa)

/-- An exact return to the original scalar target. Rationality is imposed by
the carrier, positivity and nonzero factors are explicit, and the local unit
conditions refer to the actual joint quotient. Establishing these conditions
from elliptic-curve sources remains separate work. -/
theorem scalarBSDFromPrimeUnits (d : FactorData) (hfix : NativeFixity d)
    (hreg : d.regulator * d.period ≠ 0)
    (htarget : (d.sha / d.torsionSquared) * d.tamagawa ≠ 0)
    (hpos : 0 < comparisonQuotient d)
    (hunits : ∀ p, IsPrime p → UnitAt (comparisonQuotient d) p) :
    ScalarBSD d := by
  have hq := allPrimeUnitsForceOne (comparisonQuotient d) hpos hunits
  have hprod := congrArg
    (fun x : Rat => x * ((d.sha / d.torsionSquared) * d.tamagawa)) hq
  have hc : CombinedComparison d := by
    change ((d.coefficient * d.nativeLocal) /
        ((d.sha / d.torsionSquared) * d.tamagawa)) *
        ((d.sha / d.torsionSquared) * d.tamagawa) =
      1 * ((d.sha / d.torsionSquared) * d.tamagawa) at hprod
    rw [Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ htarget,
      Rat.mul_one, Rat.one_mul] at hprod
    exact hprod
  exact (scalarIffCombined d hfix hreg).mpr hc

theorem primeCastUnitAt (q p : Nat) (hq : IsPrime q) (hp : IsPrime p)
    (hpq : p ≠ q) : UnitAt (q : Rat) p := by
  have hnot : ¬ p ∣ q := by
    intro h
    rcases hq.2 p h with h1 | hsame
    · have := hp.1
      omega
    · exact hpq hsame
  have hnot1 : ¬ p ∣ 1 := (oneUnitAt p hp).2
  simpa [UnitAt] using And.intro hnot hnot1

theorem primeCastNotOne (q : Nat) (hq : IsPrime q) : (q : Rat) ≠ 1 := by
  intro h
  have hnum := congrArg Rat.num h
  have := hq.1
  simp only [Rat.num_natCast, Rat.num_ofNat] at hnum
  omega

/-- Omitting a prime permits a real rational obstruction invisible to every
retained unit test, even if the retained scope is infinite. -/
theorem omittedPrimeWitness (scope : Nat → Prop) (q : Nat)
    (hq : IsPrime q) (hmissing : ¬ scope q) :
    0 < (q : Rat) ∧ (q : Rat) ≠ 1 ∧
      (∀ p, IsPrime p → scope p → UnitAt (q : Rat) p) ∧
      ¬ UnitAt (q : Rat) q := by
  refine ⟨Rat.natCast_pos.mpr (by have := hq.1; omega),
    primeCastNotOne q hq, ?_, ?_⟩
  · intro p hp hs
    apply primeCastUnitAt q p hq hp
    intro heq
    subst p
    exact hmissing hs
  · intro h
    have hdiv : q ∣ (q : Rat).num.natAbs := by simp
    exact h.1 hdiv

theorem omittedPrimePreventsRecovery (scope : Nat → Prop) (q : Nat)
    (hq : IsPrime q) (hmissing : ¬ scope q) :
    ¬ (∀ r : Rat, 0 < r →
      (∀ p, IsPrime p → scope p → UnitAt r p) → r = 1) := by
  intro hrecover
  have hw := omittedPrimeWitness scope q hq hmissing
  exact hw.2.1 (hrecover q hw.1 hw.2.2.1)

/-- Actual prime numbers supply singleton-support rational witnesses. -/
theorem primeCastSupportedOn (support : Nat → Prop) (q : Nat)
    (hq : IsPrime q) (hsq : support q) : SupportedOn (q : Rat) support := by
  intro p hp hd
  simp only [Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast] at hd
  rcases hd with hnum | hden
  · rcases hq.2 p hnum with hone | heq
    · have := hp.1
      omega
    · exact heq ▸ hsq
  · have := Nat.le_of_dvd (by decide) hden
    have := hp.1
    omega

/-- Universal exact recovery on a declared positive rational carrier with
an independently specified support constraint. -/
def RecoversOnSupport (support scope : Nat → Prop) : Prop :=
  ∀ r : Rat, 0 < r → SupportedOn r support →
    (∀ p, IsPrime p → scope p → UnitAt r p) → r = 1

/-- Sharp classification of the unit-comparison construction: the retained
scope recovers every allowed positive rational quotient if and only if it
covers every prime allowed by the support. Both directions are proved;
the necessity direction uses actual prime rational countermodels. -/
theorem recoversIffCoversSupport (support scope : Nat → Prop) :
    RecoversOnSupport support scope ↔
      ∀ p, IsPrime p → support p → scope p := by
  classical
  constructor
  · intro hrecover p hp hsp
    by_cases hscope : scope p
    · exact hscope
    · have hw := omittedPrimeWitness scope p hp hscope
      have heq := hrecover p hw.1 (primeCastSupportedOn support p hp hsp) hw.2.2.1
      exact False.elim (hw.2.1 heq)
  · intro hcover r hpos hsupport hunits
    apply unitsOnSupportForceOne r hpos support hsupport
    intro p hp hsp
    exact hunits p hp (hcover p hp hsp)

/-- Two local sources are indispensable for universal quotient recovery
relative to these explicit support and observation scopes. Each has a
supported prime absent from the other, and their union covers the support.
The sources here are precisely unit observations, not the named arithmetic
recognition records in the existing BSD shell. -/
theorem twoSourcesIndispensable (support scopeA scopeB : Nat → Prop)
    (hcover : ∀ p, IsPrime p → support p → scopeA p ∨ scopeB p)
    (qA qB : Nat) (hqA : IsPrime qA) (hqB : IsPrime qB)
    (hAsupport : support qA) (hBsupport : support qB)
    (hAprivate : ¬ scopeB qA) (hBprivate : ¬ scopeA qB) :
    RecoversOnSupport support (fun p => scopeA p ∨ scopeB p) ∧
      ¬ RecoversOnSupport support scopeA ∧
      ¬ RecoversOnSupport support scopeB := by
  refine ⟨(recoversIffCoversSupport support _).mpr hcover, ?_, ?_⟩
  · intro h
    exact hBprivate ((recoversIffCoversSupport support scopeA).mp h qB hqB hBsupport)
  · intro h
    exact hAprivate ((recoversIffCoversSupport support scopeB).mp h qA hqA hAsupport)

/-- Support-scoped local sources return to scalar BSD through the joint
quotient. Neither individual factor normalization is assumed. -/
theorem scalarBSDFromTwoScopes (d : FactorData) (hfix : NativeFixity d)
    (hreg : d.regulator * d.period ≠ 0)
    (htarget : (d.sha / d.torsionSquared) * d.tamagawa ≠ 0)
    (hpos : 0 < comparisonQuotient d)
    (scopeA scopeB : Nat → Prop)
    (hsupport : SupportedOn (comparisonQuotient d) (fun p => scopeA p ∨ scopeB p))
    (hA : ∀ p, IsPrime p → scopeA p → UnitAt (comparisonQuotient d) p)
    (hB : ∀ p, IsPrime p → scopeB p → UnitAt (comparisonQuotient d) p) :
    ScalarBSD d := by
  have hq := twoScopesForceOne (comparisonQuotient d) hpos scopeA scopeB hsupport hA hB
  apply scalarBSDFromPrimeUnits d hfix hreg htarget hpos
  intro p hp
  rw [hq]
  exact oneUnitAt p hp

/-- The forward return holds on fully positive factor data, with all
nonzero and positivity side conditions derived from that admissibility. -/
theorem scalarBSDFromPositiveTwoScopes (d : FactorData) (hpositive : AllPositive d)
    (hfix : NativeFixity d) (scopeA scopeB : Nat → Prop)
    (hsupport : SupportedOn (comparisonQuotient d) (fun p => scopeA p ∨ scopeB p))
    (hA : ∀ p, IsPrime p → scopeA p → UnitAt (comparisonQuotient d) p)
    (hB : ∀ p, IsPrime p → scopeB p → UnitAt (comparisonQuotient d) p) :
    ScalarBSD d := by
  rcases hpositive with ⟨_, hc, hr, ho, hb, hs, ht, htam⟩
  have htargetpos : 0 < (d.sha / d.torsionSquared) * d.tamagawa := by
    simpa only [Rat.div_def] using
      Rat.mul_pos (Rat.mul_pos hs (Rat.inv_pos.mpr ht)) htam
  have hquotpos : 0 < comparisonQuotient d := by
    change 0 < (d.coefficient * d.nativeLocal) /
      ((d.sha / d.torsionSquared) * d.tamagawa)
    rw [Rat.div_def]
    exact Rat.mul_pos (Rat.mul_pos hc hb) (Rat.inv_pos.mpr htargetpos)
  exact scalarBSDFromTwoScopes d hfix (Rat.ne_of_gt (Rat.mul_pos hr ho))
    (Rat.ne_of_gt htargetpos) hquotpos scopeA scopeB hsupport hA hB

private theorem ratInvOne : (1 : Rat)⁻¹ = 1 := by
  simpa using Rat.mul_inv_cancel (1 : Rat) (by decide)

/-- A positive factor package carrying an omitted prime in its native local
factor. This is rational scalar data, not a realized elliptic curve. -/
def primeDefectData (q : Nat) : FactorData := ⟨q, 1, 1, 1, q, 1, 1, 1⟩

theorem primeDefectDataProperties (q : Nat) (hq : IsPrime q) :
    AllPositive (primeDefectData q) ∧ NativeFixity (primeDefectData q) ∧
      CoefficientComparison (primeDefectData q) ∧
      comparisonQuotient (primeDefectData q) = (q : Rat) ∧
      ¬ ScalarBSD (primeDefectData q) := by
  have hqpos : 0 < (q : Rat) := Rat.natCast_pos.mpr (by have := hq.1; omega)
  have hqne := primeCastNotOne q hq
  have honepos : (0 : Rat) < 1 := by decide
  simp [AllPositive, NativeFixity, CoefficientComparison, comparisonQuotient,
    ScalarBSD, primeDefectData, Rat.div_def, ratInvOne, hqpos, hqne, honepos]

/-- An omitted supported prime prevents even scalar BSD from following
uniformly from native fixity and the retained local unit comparisons. -/
theorem omittedScopePreventsScalarBSD (support scope : Nat → Prop) (q : Nat)
    (hq : IsPrime q) (hsq : support q) (hmissing : ¬ scope q) :
    ¬ (∀ d : FactorData, AllPositive d →
      SupportedOn (comparisonQuotient d) support → NativeFixity d →
      (∀ p, IsPrime p → scope p → UnitAt (comparisonQuotient d) p) →
      ScalarBSD d) := by
  intro hrecover
  have hd := primeDefectDataProperties q hq
  have hw := omittedPrimeWitness scope q hq hmissing
  apply hd.2.2.2.2
  apply hrecover (primeDefectData q) hd.1
  · rw [hd.2.2.2.1]
    exact primeCastSupportedOn support q hq hsq
  · exact hd.2.1
  · rw [hd.2.2.2.1]
    exact hw.2.2.1

/-- The original scalar target, inferred uniformly on positive native factor
data, with independently fixed support and retained local observations. -/
def ForcesScalarOnSupport (support scope : Nat → Prop) : Prop :=
  ∀ d : FactorData, AllPositive d →
    SupportedOn (comparisonQuotient d) support → NativeFixity d →
    (∀ p, IsPrime p → scope p → UnitAt (comparisonQuotient d) p) → ScalarBSD d

/-- The support coverage criterion is sharp for scalar BSD assembly itself,
not merely for the auxiliary quotient-recovery problem. -/
theorem forcesScalarIffCoversSupport (support scope : Nat → Prop) :
    ForcesScalarOnSupport support scope ↔
      ∀ p, IsPrime p → support p → scope p := by
  classical
  constructor
  · intro h p hp hsp
    by_cases hscope : scope p
    · exact hscope
    · exact False.elim (omittedScopePreventsScalarBSD support scope p hp hsp hscope h)
  · intro hcover d hpositive hsupport hfix hunits
    apply scalarBSDFromPositiveTwoScopes d hpositive hfix support support
    · intro p hp hd
      exact Or.inl (hsupport p hp hd)
    · intro p hp hsp
      exact hunits p hp (hcover p hp hsp)
    · intro p hp hsp
      exact hunits p hp (hcover p hp hsp)

/-- Both local inputs are necessary for the scalar assembly rule on this
declared carrier. The actual prime witnesses are constructed above. -/
theorem twoSourcesIndispensableForScalar (support scopeA scopeB : Nat → Prop)
    (hcover : ∀ p, IsPrime p → support p → scopeA p ∨ scopeB p)
    (qA qB : Nat) (hqA : IsPrime qA) (hqB : IsPrime qB)
    (hAsupport : support qA) (hBsupport : support qB)
    (hAprivate : ¬ scopeB qA) (hBprivate : ¬ scopeA qB) :
    ForcesScalarOnSupport support (fun p => scopeA p ∨ scopeB p) ∧
      ¬ ForcesScalarOnSupport support scopeA ∧
      ¬ ForcesScalarOnSupport support scopeB := by
  refine ⟨(forcesScalarIffCoversSupport support _).mpr hcover, ?_, ?_⟩
  · exact omittedScopePreventsScalarBSD support scopeA qB hqB hBsupport hBprivate
  · exact omittedScopePreventsScalarBSD support scopeB qA hqA hAsupport hAprivate

/-- Even exact quotient recovery does not replace native fixity. The leading
term 2 violates BSD while the joint quotient is exactly one. -/
theorem fixityNecessaryForUnitAssembly :
    AllPositive missingFixity ∧ comparisonQuotient missingFixity = 1 ∧
      (∀ p, IsPrime p → UnitAt (comparisonQuotient missingFixity) p) ∧
      ¬ ScalarBSD missingFixity := by
  have hquot : comparisonQuotient missingFixity = 1 := by
    simp [comparisonQuotient, missingFixity, Rat.div_def, ratInvOne]
  exact ⟨countermodelsPositive.2.2.1, hquot,
    fun p hp => hquot ▸ oneUnitAt p hp, fixityInputNecessary.2.2.2⟩

/-- Concrete local records of a rational number, with a fixed prime list. -/
def localRows (ps : List Nat) (r : Rat) : (p : Nat) → p ∈ ps → Bool :=
  fun p _ => decide (UnitAt r p)

/-- No processing of a finite collection of prime-unit records can separate
one from every positive rational number. The counterexample is an actual
prime, not a free Boolean completion. -/
theorem finitePrimeUnitNoGo (ps : List Nat) (hps : ∀ p ∈ ps, IsPrime p) :
    ∃ q, IsPrime q ∧ q ∉ ps ∧ 0 < (q : Rat) ∧ (q : Rat) ≠ 1 ∧
      localRows ps (q : Rat) = localRows ps 1 ∧
      (∀ (α : Sort _) (operator : ((p : Nat) → p ∈ ps → Bool) → α),
        operator (localRows ps (q : Rat)) = operator (localRows ps 1)) := by
  obtain ⟨q, hq, hmissing⟩ := primeOutsideFiniteList ps hps
  have hw := omittedPrimeWitness (fun p => p ∈ ps) q hq hmissing
  have hrows : localRows ps (q : Rat) = localRows ps 1 := by
    funext p hp
    simp [localRows, hw.2.2.1 p (hps p hp) hp, oneUnitAt p (hps p hp)]
  exact ⟨q, hq, hmissing, hw.1, hw.2.1, hrows,
    fun _ operator => congrArg operator hrows⟩

end SixBirdsBSD.Closure.RationalLocalGlobal
