import SixBirdsBSD.Closure.TameComponentReturn

/-!
Equation-derived finite support and a native product of two inertia factors.
The arithmetic component-group and Tate-algorithm identifications are written
in formalization/global_tame_product.md; they are not Lean certificate fields.
No analytic rank, Sha finiteness or paper-native OC comparison is asserted.
-/
namespace SixBirdsBSD.Closure.GlobalTameProduct

open SixBirdsBSD.Apparatus.SupportPrimeNoGo
open LocalUnitSupport RationalLocalGlobal TameComponentReturn CTDerivedTransport

def curve : IntegralModel := ⟨0,0,0,385,1225⟩
def badPlaces : List Nat := [2,5,7,6269]
def discriminantFactors : List Nat := [2,2,2,2,5,5,5,7,7,7,6269]

theorem equationInvariants :
    (c4 curve, c6 curve, discriminant curve) = (-18480,-1058400,-4300534000) ∧
    (discriminant curve).natAbs = primeProduct discriminantFactors ∧
    (c4 curve : Rat)^3 / (discriminant curve : Rat) = 9199872/6269 ∧
    ¬ (discriminant curve) ∣ (c4 curve)^3 := by decide +kernel

private theorem prime6269 : IsPrime 6269 := by
  have hs : ∀ d : Fin 80, d.val ∣ 6269 → d.val = 1 := by decide +kernel
  refine ⟨by decide, ?_⟩
  intro d hd
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  by_cases hdp : d = 6269
  · exact Or.inr hdp
  obtain ⟨k, hk⟩ := hd
  have hd0 : d ≠ 0 := by intro h; simp [h] at hk
  have hk0 : k ≠ 0 := by intro h; simp [h] at hk
  have hk1 : k ≠ 1 := by intro h; simp [h] at hk; omega
  have hdivd : d ∣ 6269 := ⟨k,hk⟩
  have hdivk : k ∣ 6269 := ⟨d,by simpa [Nat.mul_comm] using hk⟩
  have hdB : 80 ≤ d := by
    by_cases h : d < 80
    · exact False.elim (hd1 (hs ⟨d,h⟩ hdivd))
    · omega
  have hkB : 80 ≤ k := by
    by_cases h : k < 80
    · exact False.elim (hk1 (hs ⟨k,h⟩ hdivk))
    · omega
  have hmul := Nat.mul_le_mul hdB hkB
  rw [← hk] at hmul
  omega

theorem factorPrimes : ∀ p ∈ discriminantFactors, IsPrime p := by
  intro p hp
  simp only [discriminantFactors, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h
  all_goals subst p
  all_goals first | exact prime6269 | decide +kernel

private theorem primeDvdProduct (p a b : Nat) (hp : IsPrime p)
    (h : p ∣ a*b) : p ∣ a ∨ p ∣ b := by
  obtain ⟨u,v,hua,hvb,huv⟩ := Nat.dvd_mul.mp h
  have hup : u ∣ p := ⟨v,huv.symm⟩
  rcases hp.2 u hup with hu | hu
  · subst u
    have hv : v = p := by simpa using huv
    exact Or.inr (hv ▸ hvb)
  · subst u
    exact Or.inl hua

/-- Equation support is proved at every prime, rather than inferred from
a finite set of sampled local outputs or from a conductor name. -/
theorem primeDivisorOfPrimeList (ps : List Nat) (hps : ∀ q ∈ ps, IsPrime q)
    (p : Nat) (hp : IsPrime p) (hd : p ∣ primeProduct ps) : p ∈ ps := by
  induction ps with
  | nil =>
    have := Nat.le_of_dvd (by decide : 0 < 1) hd
    have := hp.1
    omega
  | cons q qs ih =>
    rcases primeDvdProduct p q (primeProduct qs) hp hd with h | h
    · rcases (hps q (by simp)).2 p h with h | h
      · have := hp.1; omega
      · simp [h]
    · exact List.mem_cons_of_mem q (ih (fun r hr => hps r (by simp [hr])) h)

theorem allPrimeDiscriminantSupport (p : Nat) (hp : IsPrime p) :
    p ∣ (discriminant curve).natAbs ↔ p ∈ badPlaces := by
  constructor
  · intro hd
    rw [equationInvariants.2.1] at hd
    have hm := primeDivisorOfPrimeList discriminantFactors factorPrimes p hp hd
    simpa [discriminantFactors, badPlaces, or_assoc] using hm
  · intro hm
    simp only [badPlaces, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h <;> subst p <;> decide +kernel

theorem actualShallowPlaces :
    shallowTateBranch curve 5 = some (2,3,2) ∧
    shallowTateBranch curve 7 = some (2,3,2) ∧
    shallowTateBranch curve 2 = none := by decide +kernel

/-- At p=5 or 7, use pi^4=p and scale x=pi^2 X, y=pi^3 Y.
The transformed coefficients are A/p and (B/p^2) pi^2. The equations
below clear denominators; the arithmetic good-reduction return is written. -/
theorem tameCoverInputs :
    385 = 5*77 ∧ 1225 = 5^2*49 ∧
    385 = 7*55 ∧ 1225 = 7^2*25 ∧
    ExactValuation 5 3 (discriminant curve) ∧
    ExactValuation 7 3 (discriminant curve) ∧
    ¬ (5 : Int) ∣ 77 ∧ ¬ (7 : Int) ∣ 55 := by decide +kernel

/-- Tagged places keep distinct local inputs even when their matrices agree.
This factor is defined before the component profile is read. -/
def nativeRows : List (Nat × Matrix2) := [(5,inertiaFour),(7,inertiaFour)]
def integralProduct : List Int → Int
  | [] => 1
  | a :: rest => a * integralProduct rest
def nativeProduct (rows : List (Nat × Matrix2)) : Int :=
  integralProduct (rows.map (fun r => descentDeterminant r.2))

def rebaseRows (rows : List (Nat × Matrix2)) (b c : Nat → Matrix2) :
    List (Nat × Matrix2) := rows.map (fun r => (r.1, compose (b r.1) (compose r.2 (c r.1))))

/-- Bases may change independently at every place. Only rows in this finite
product need inverse matrices; no ambient all-prime certificate is assumed. -/
theorem nativeProductBasisInvariant (rows : List (Nat × Matrix2)) (b c : Nat → Matrix2)
    (hi : ∀ r ∈ rows, compose (c r.1) (b r.1) = identityMatrix) :
    nativeProduct (rebaseRows rows b c) = nativeProduct rows := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    have ht := ih (fun s hs => hi s (by simp [hs]))
    simpa [nativeProduct, rebaseRows, integralProduct,
      descentDeterminantBasisInvariant r.2 (b r.1) (c r.1) (hi r (by simp))]
      using congrArg (fun n => descentDeterminant r.2 * n) ht

theorem nativeProductReturn :
    (nativeRows.map Prod.fst).Nodup ∧ nativeProduct nativeRows = 4 ∧
    nativeProduct [(5,inertiaFour)] = 2 ∧
    nativeProduct [(7,inertiaFour)] = 2 ∧
    nativeProduct [(5,inertiaFour)] ≠ nativeProduct nativeRows ∧
    nativeProduct [(7,inertiaFour)] ≠ nativeProduct nativeRows := by decide +kernel

/-- This is an imported Tate-output trace, not a definition of arithmetic
component groups. The exact PARI reproduction is kept separately. -/
def checkedTateProfile : List (Nat × Nat) := [(2,1),(5,2),(7,2),(6269,1)]

theorem finiteProfileReturn :
    checkedTateProfile.map Prod.fst = badPlaces ∧
    nativeProduct nativeRows = integralProduct (checkedTateProfile.map (fun r => (r.2 : Int))) :=
  by decide +kernel

/-- All odd-prime unit tests miss the native global factor four. The omitted
coefficient prime two is essential even though c_2 itself is one. -/
theorem oddPrimeUnitsMissGlobalFactor :
    (∀ p, IsPrime p → p ≠ 2 → UnitAt (4 : Rat) p) ∧
    ¬ UnitAt (4 : Rat) 2 ∧ (4 : Rat) ≠ 1 := by
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  intro p hp hn
  have hnot : ¬ p ∣ 2 := (primeCastUnitAt 2 p (by decide +kernel) hp hn).1
  have hfour : ¬ p ∣ 4 := by
    intro h
    exact (primeDvdProduct p 2 2 hp h).elim hnot hnot
  simpa [UnitAt] using And.intro hfour (oneUnitAt p hp).2

theorem shallowPlacesDoNotCoverCoefficientSupport :
    ¬ SupportedOn (4 : Rat) (fun p => p = 5 ∨ p = 7) := by
  intro hs
  have h := hs 2 (by decide +kernel) (Or.inl (by decide +kernel))
  omega

/-- Boolean unit flags, even at all primes, lose exponents. Exact quotient
valuation tests in RationalLocalGlobal are stronger than these flags. -/
theorem unitFlagsLoseMultiplicity (p : Nat) (hp : IsPrime p) :
    UnitAt (2 : Rat) p ↔ UnitAt (4 : Rat) p := by
  by_cases hn : p = 2
  · subst p; decide +kernel
  · exact iff_of_true (primeCastUnitAt 2 p (by decide +kernel) hp hn)
      (oddPrimeUnitsMissGlobalFactor.1 p hp hn)

end SixBirdsBSD.Closure.GlobalTameProduct
