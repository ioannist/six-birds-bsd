/-!
`SixBirdsBSD.Apparatus.SupportPrimeNoGo` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § SupportPrimeNoGo.
-/

namespace SixBirdsBSD.Apparatus.SupportPrimeNoGo

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

/-- No finite prime list can certify all support-prime rows. -/
theorem finitePrimeCoverNoGo (P0 : List Nat) :
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
