import Init.Grind

/-!
The scalar conditional BSD argument without the legacy audit shell.

Only subtraction, movement of a fixed denominator, normalization, and
rank-gated recognition content occur in these declarations. No source
necessity, computability, eta, Pfaffian, or master-applicability certificate
is a premise. The arithmetic interpretation of the scalars is supplied.
-/

namespace SixBirdsBSD.Closure.ScalarBSD

universe u

/-- Normalized fixity returns the unchanged scalar BSD product. -/
theorem normalizedFixityForcesScalarBSD {R : Type u}
    (zero : R) (sub mul div : R → R → R)
    (hSub : ∀ a b, sub a b = zero ↔ a = b)
    (hMove : ∀ a b d, mul (div a d) b = div (mul a b) d)
    (leading sha reg period tam torsionSquared kappa : R)
    (hNormalization : kappa = div sha torsionSquared)
    (hFixity : sub leading (mul (mul (mul kappa reg) period) tam) = zero) :
    leading = div (mul (mul (mul sha reg) period) tam) torsionSquared := by
  have hEq := (hSub _ _).mp hFixity
  rw [hNormalization] at hEq
  rw [hMove sha reg torsionSquared,
    hMove (mul sha reg) period torsionSquared,
    hMove (mul (mul sha reg) period) tam torsionSquared] at hEq
  exact hEq

/-- Both rank ranges, with their exact supplied scalar recognition content.
The low-rank premise is the scalar identity; the higher-rank premise is
normalized fixity. Neither is asserted to be independently proved here. -/
theorem rankGatedRecognitionForcesScalarBSD {R : Type u}
    (zero : R) (sub mul div : R → R → R)
    (hSub : ∀ a b, sub a b = zero ↔ a = b)
    (hMove : ∀ a b d, mul (div a d) b = div (mul a b) d)
    (rank : Nat) (leading sha reg period tam torsionSquared : R)
    (lowRank : rank = 0 ∨ rank = 1 →
      leading = div (mul (mul (mul sha reg) period) tam) torsionSquared)
    (highRank : 2 ≤ rank → ∃ kappa,
      kappa = div sha torsionSquared ∧
      sub leading (mul (mul (mul kappa reg) period) tam) = zero) :
    leading = div (mul (mul (mul sha reg) period) tam) torsionSquared := by
  by_cases hr : 2 ≤ rank
  · obtain ⟨kappa, hNorm, hFix⟩ := highRank hr
    exact normalizedFixityForcesScalarBSD zero sub mul div hSub hMove
      leading sha reg period tam torsionSquared kappa hNorm hFix
  · apply lowRank
    omega

end SixBirdsBSD.Closure.ScalarBSD
