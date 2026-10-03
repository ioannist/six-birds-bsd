import SixBirdsBSD.Closure.StarkInverseLimit

/-!
The inverse-limit step for coefficient-natural finite comparisons.
This does not formalize arithmetic cochain lifts or determinant functors;
their naturality is proved in the accompanying written construction.
The inverse maps' naturality is derived rather than supplied separately.
-/
namespace SixBirdsBSD.Closure.StarkCoefficientNaturality

universe u v

structure Tower where
  Level : Nat → Type u
  reduce : ∀ n, Level (n+1) → Level n

structure Compatible (t : Tower) where
  val : ∀ n, t.Level n
  law : ∀ n, t.reduce n (val (n+1)) = val n

theorem compatibleExt {t : Tower} {x y : Compatible t}
    (h : ∀ n, x.val n = y.val n) : x = y := by
  cases x
  cases y
  congr
  funext n
  exact h n

structure FiniteComparison (a : Tower.{u}) (b : Tower.{v}) where
  forward : ∀ n, a.Level n → b.Level n
  backward : ∀ n, b.Level n → a.Level n
  backward_forward : ∀ n x, backward n (forward n x) = x
  forward_backward : ∀ n y, forward n (backward n y) = y

def Natural {a : Tower.{u}} {b : Tower.{v}} (f : FiniteComparison a b) : Prop :=
  ∀ n x, b.reduce n (f.forward (n+1) x) = f.forward n (a.reduce n x)

theorem inverseNaturality {a : Tower.{u}} {b : Tower.{v}}
    (f : FiniteComparison a b) (h : Natural f) (n : Nat) (y : b.Level (n+1)) :
    a.reduce n (f.backward (n+1) y) = f.backward n (b.reduce n y) := by
  have hs := h n (f.backward (n+1) y)
  rw [f.forward_backward] at hs
  have hi := congrArg (f.backward n) hs
  rw [f.backward_forward] at hi
  exact hi.symm

def toLimit {a : Tower.{u}} {b : Tower.{v}}
    (f : FiniteComparison a b) (h : Natural f) (x : Compatible a) : Compatible b where
  val n := f.forward n (x.val n)
  law n := by rw [h, x.law]

def fromLimit {a : Tower.{u}} {b : Tower.{v}}
    (f : FiniteComparison a b) (h : Natural f) (y : Compatible b) : Compatible a where
  val n := f.backward n (y.val n)
  law n := by rw [inverseNaturality f h, y.law]

theorem limitLeftInverse {a : Tower.{u}} {b : Tower.{v}}
    (f : FiniteComparison a b) (h : Natural f) (x : Compatible a) :
    fromLimit f h (toLimit f h x) = x := by
  apply compatibleExt
  intro n
  exact f.backward_forward n (x.val n)

theorem limitRightInverse {a : Tower.{u}} {b : Tower.{v}}
    (f : FiniteComparison a b) (h : Natural f) (y : Compatible b) :
    toLimit f h (fromLimit f h y) = y := by
  apply compatibleExt
  intro n
  exact f.forward_backward n (y.val n)

theorem integralComparisonUnique {a : Tower.{u}} {b : Tower.{v}}
    (f : FiniteComparison a b) (h : Natural f)
    (g : Compatible a → Compatible b)
    (hg : ∀ x n, (g x).val n = f.forward n (x.val n)) : g = toLimit f h := by
  funext x
  apply compatibleExt
  exact hg x

/-- Every finite map here is invertible, but the first two are incompatible.
This rejects an inverse-limit inference from freeness or isomorphism alone. -/
abbrev residueTower : Tower where
  Level _ := Fin 3
  reduce _ x := x

def mismatchedFiniteComparison : FiniteComparison residueTower residueTower where
  forward n x := if n = 0 then x else (2 : Fin 3)*(x : Fin 3)
  backward n x := if n = 0 then x else (2 : Fin 3)*(x : Fin 3)
  backward_forward n x := by
    by_cases h : n = 0
    · simp [h]
    · simp only [h, if_false]
      have hi : ∀ x : Fin 3, 2*(2*x) = x := by decide +kernel
      exact hi x
  forward_backward n x := by
    by_cases h : n = 0
    · simp [h]
    · simp only [h, if_false]
      have hi : ∀ x : Fin 3, 2*(2*x) = x := by decide +kernel
      exact hi x

theorem finiteIsomorphismsNeedNaturality : ¬ Natural mismatchedFiniteComparison := by
  intro h
  have hf := h 0 (1 : Fin 3)
  change (2 : Fin 3) = 1 at hf
  exact (by decide : (2 : Fin 3) ≠ 1) hf

theorem noIntegralLiftForMismatchedComparisons :
    ¬ ∃ g : Compatible residueTower → Compatible residueTower,
      ∀ x n, (g x).val n = mismatchedFiniteComparison.forward n (x.val n) := by
  rintro ⟨g,h⟩
  let one : Compatible residueTower := ⟨fun _ => (1 : Fin 3), fun _ => rfl⟩
  have hc := (g one).law 0
  rw [h one 1, h one 0] at hc
  change (2 : Fin 3) = 1 at hc
  exact (by decide : (2 : Fin 3) ≠ 1) hc

end SixBirdsBSD.Closure.StarkCoefficientNaturality
