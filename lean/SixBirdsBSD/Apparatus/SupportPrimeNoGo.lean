/-!
`SixBirdsBSD.Apparatus.SupportPrimeNoGo` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § SupportPrimeNoGo.
-/

namespace SixBirdsBSD.Apparatus.SupportPrimeNoGo

/-- Elementary primality, using only Lean's core natural-number arithmetic. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- The unbounded divisor definition has an equivalent finite decision
procedure. This supports concrete applicability checks without axioms or
declaring primality merely because an index lies outside a finite list. -/
theorem isPrimeIffFiniteCheck (p : Nat) :
    IsPrime p ↔ (2 ≤ p ∧ ∀ d : Fin (p + 1), d.val ∣ p → d.val = 1 ∨ d.val = p) := by
  constructor
  · intro hp
    exact ⟨hp.1, fun d hd => hp.2 d.val hd⟩
  · rintro ⟨hge, hfinite⟩
    refine ⟨hge, ?_⟩
    intro d hd
    have hle : d ≤ p := Nat.le_of_dvd (by omega) hd
    exact hfinite ⟨d, by omega⟩ hd

instance decidableIsPrime (p : Nat) : Decidable (IsPrime p) :=
  if h : 2 ≤ p ∧ ∀ d : Fin (p + 1), d.val ∣ p → d.val = 1 ∨ d.val = p then
    isTrue ((isPrimeIffFiniteCheck p).mpr h)
  else
    isFalse (fun hp => h ((isPrimeIffFiniteCheck p).mp hp))

/-- Every natural number at least two has a prime divisor. -/
theorem existsPrimeDivisor (n : Nat) (hn : 2 ≤ n) :
    ∃ q, IsPrime q ∧ q ∣ n := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hp : IsPrime n
    · exact ⟨n, hp, Nat.dvd_refl n⟩
    · have hf : ¬ ∀ d : Nat, d ∣ n → d = 1 ∨ d = n := by
        intro h
        exact hp ⟨hn, h⟩
      obtain ⟨d, hd⟩ := Classical.not_forall.mp hf
      have hdiv : d ∣ n := by
        by_cases h : d ∣ n
        · exact h
        · exact False.elim (hd (fun h' => False.elim (h h')))
      have hd1 : d ≠ 1 := fun h => hd (fun _ => Or.inl h)
      have hdn : d ≠ n := fun h => hd (fun _ => Or.inr h)
      have hd0 : d ≠ 0 := by
        intro h
        subst d
        have hz : n = 0 := Nat.zero_dvd.mp hdiv
        omega
      have hdge : 2 ≤ d := by omega
      have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdiv
      obtain ⟨q, hq, hqd⟩ := ih d (by omega) hdge
      exact ⟨q, hq, Nat.dvd_trans hqd hdiv⟩

def primeProduct : List Nat → Nat
  | [] => 1
  | p :: ps => p * primeProduct ps

private theorem primeProductPositive (ps : List Nat)
    (hp : ∀ p ∈ ps, IsPrime p) : 0 < primeProduct ps := by
  induction ps with
  | nil => decide
  | cons p ps ih =>
    have hpos : 0 < p := by have := (hp p (by simp)).1; omega
    have htail := ih (fun q hq => hp q (by simp [hq]))
    exact Nat.mul_pos hpos htail

private theorem memberDividesPrimeProduct {q : Nat} {ps : List Nat}
    (hq : q ∈ ps) : q ∣ primeProduct ps := by
  induction ps with
  | nil => cases hq
  | cons p ps ih =>
    simp only [List.mem_cons] at hq
    rcases hq with h | h
    · subst q
      exact Nat.dvd_mul_right p (primeProduct ps)
    · exact Nat.dvd_mul_left_of_dvd (ih h) p

/-- Euclid's argument supplies an actual prime outside each finite prime list. -/
theorem primeOutsideFiniteList (ps : List Nat) (hp : ∀ p ∈ ps, IsPrime p) :
    ∃ q, IsPrime q ∧ q ∉ ps := by
  have hpos := primeProductPositive ps hp
  obtain ⟨q, hq, hdiv⟩ := existsPrimeDivisor (primeProduct ps + 1) (by omega)
  refine ⟨q, hq, ?_⟩
  intro hmem
  have hprod := memberDividesPrimeProduct hmem
  have hone : q ∣ 1 := (Nat.dvd_add_iff_right hprod).mpr hdiv
  have hle : q ≤ 1 := Nat.le_of_dvd (by decide) hone
  have := hq.1
  omega

structure PrimeCoverageCompletion where
  covered : Nat → Bool

def coverageBase : PrimeCoverageCompletion :=
  ⟨fun _ => false⟩

def coverageVariant (q : Nat) : PrimeCoverageCompletion :=
  ⟨fun p => if p = q then true else false⟩

def agreeOnPrimeSet (P0 : List Nat) (a b : PrimeCoverageCompletion) : Prop :=
  ∀ p, p ∈ P0 → a.covered p = b.covered p

def differAtPrime (q : Nat) (a b : PrimeCoverageCompletion) : Prop :=
  a.covered q ≠ b.covered q

def restrictedRows (P0 : List Nat) (c : PrimeCoverageCompletion) :
    (p : Nat) → p ∈ P0 → Bool :=
  fun p _ => c.covered p

def listMax (P0 : List Nat) : Nat :=
  P0.foldr Nat.max 0

theorem memLeListMax {p : Nat} {P0 : List Nat} (hp : p ∈ P0) : p ≤ listMax P0 := by
  induction P0 with
  | nil => cases hp
  | cons a rest ih =>
      simp [listMax, List.foldr] at hp ⊢
      cases hp with
      | inl h =>
          subst p
          exact Nat.le_max_left a (rest.foldr Nat.max 0)
      | inr h =>
          exact Nat.le_trans (ih h) (Nat.le_max_right a (rest.foldr Nat.max 0))

theorem listMaxSuccNotMem (P0 : List Nat) : listMax P0 + 1 ∉ P0 := by
  intro hmem
  have hle : listMax P0 + 1 ≤ listMax P0 := memLeListMax hmem
  exact Nat.not_succ_le_self (listMax P0) hle

/-- Generic finite-index forgetfulness, without a primality assertion. -/
theorem finiteIndexCoverNoGo (P0 : List Nat) :
    ∃ q, q ∉ P0 ∧
      agreeOnPrimeSet P0 coverageBase (coverageVariant q) ∧
      differAtPrime q coverageBase (coverageVariant q) ∧
      (∀ (α : Sort _) (operator : ((p : Nat) → p ∈ P0 → Bool) → α),
        operator (restrictedRows P0 coverageBase) =
          operator (restrictedRows P0 (coverageVariant q))) := by
  let q := listMax P0 + 1
  have hqnot : q ∉ P0 := by
    dsimp [q]
    exact listMaxSuccNotMem P0
  refine ⟨q, hqnot, ?_, ?_, ?_⟩
  · intro p hp
    have hpne : ¬p = q := by
      intro hp_eq
      subst p
      exact hqnot hp
    simp [coverageBase, coverageVariant, hpne]
  · unfold differAtPrime coverageBase coverageVariant
    intro h
    simp at h
  · intro α operator
    apply congrArg operator
    unfold restrictedRows coverageBase coverageVariant
    funext p hp
    have hpne : ¬p = q := by
      intro hp_eq
      subst p
      exact hqnot hp
    simp [hpne]

/-- No finite list of primes determines all prime coverage rows. The witness
is an actual prime, supplied by the elementary Euclid argument above. -/
theorem finitePrimeCoverNoGo (P0 : List Nat) (hp : ∀ p ∈ P0, IsPrime p) :
    ∃ q, IsPrime q ∧ q ∉ P0 ∧
      agreeOnPrimeSet P0 coverageBase (coverageVariant q) ∧
      differAtPrime q coverageBase (coverageVariant q) ∧
      (∀ (α : Sort _) (operator : ((p : Nat) → p ∈ P0 → Bool) → α),
        operator (restrictedRows P0 coverageBase) =
          operator (restrictedRows P0 (coverageVariant q))) := by
  obtain ⟨q, hprime, hqnot⟩ := primeOutsideFiniteList P0 hp
  refine ⟨q, hprime, hqnot, ?_, ?_, ?_⟩
  · intro p hp
    have hpne : p ≠ q := by intro heq; subst p; exact hqnot hp
    simp [coverageBase, coverageVariant, hpne]
  · simp [differAtPrime, coverageBase, coverageVariant]
  · intro α operator
    apply congrArg operator
    funext p hp
    have hpne : p ≠ q := by intro heq; subst p; exact hqnot hp
    simp [restrictedRows, coverageBase, coverageVariant, hpne]

def countR4bUpTo : Nat → (Nat → Bool) → Nat
  | 0, r4b => if r4b 0 then 1 else 0
  | Nat.succ B, r4b => countR4bUpTo B r4b + if r4b (B + 1) then 1 else 0

/-- Finite diagnostic residual: one unit for each R4b row in the truncation. -/
def supportPrimeTruncationResidual (r4b : Nat → Bool) (B : Nat) : Nat :=
  countR4bUpTo B r4b

inductive B50Curve where
  | c11a1
  | c37a1
  | c121b1
  | c960d1
  | c571a1

def b50ResidualBelow50 : B50Curve → Nat
  | B50Curve.c11a1 => 1
  | B50Curve.c37a1 => 1
  | B50Curve.c121b1 => 1
  | B50Curve.c960d1 => 3
  | B50Curve.c571a1 => 0

end SixBirdsBSD.Apparatus.SupportPrimeNoGo
