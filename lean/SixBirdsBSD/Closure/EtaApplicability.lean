import SixBirdsBSD.Apparatus.SupportPrimeNoGo
import Init.Data.Rat.Lemmas

/-!
Elementary applicability obstructions for the proposed eta import route.
These prove necessary numerical checks, not the cited arithmetic theorems
and not a disproof of a differently constructed eta identity.
-/
namespace SixBirdsBSD.Closure.EtaApplicability

open SixBirdsBSD.Apparatus.SupportPrimeNoGo

universe u

/-- Only the square valuation law at beta is used. Requiring a finite
additive valuation law also at zero would be inconsistent. -/
theorem squareRelationForcesHalfValuation {Scalar : Type u}
    (mul : Scalar → Scalar → Scalar) (neg : Scalar → Scalar)
    (valuation : Scalar → Rat) (beta pScalar : Scalar)
    (hSquare : mul beta beta = neg pScalar)
    (hValSquare : valuation (mul beta beta) = valuation beta + valuation beta)
    (hValNegP : valuation (neg pScalar) = 1) :
    valuation beta = 1 / 2 := by
  have h := congrArg valuation hSquare
  rw [hValSquare, hValNegP] at h
  grind

/-- Under the standard normalization v_p(p)=1, beta^2=-p cannot have
weight-two critical slope 1. This says nothing about other weight or
valuation conventions, which would require a separate comparison. -/
theorem weightTwoCriticalSlopeIncompatible {Scalar : Type u}
    (mul : Scalar → Scalar → Scalar) (neg : Scalar → Scalar)
    (valuation : Scalar → Rat) (beta pScalar : Scalar)
    (hSquare : mul beta beta = neg pScalar)
    (hValSquare : valuation (mul beta beta) = valuation beta + valuation beta)
    (hValNegP : valuation (neg pScalar) = 1) :
    valuation beta ≠ 1 := by
  rw [squareRelationForcesHalfValuation mul neg valuation beta pScalar
    hSquare hValSquare hValNegP]
  decide +kernel

/-- Necessary numerical scope of Lang-Wake Theorem 1.1. The actual theorem
additionally specifies the Hecke algebra and residual representation. This
predicate alone is not a certificate of its applicability to an eta value. -/
structure LangWakeNumericScope (levelPrime residualPrime : Nat) : Prop where
  levelPrimeAtLeastFive : 5 ≤ levelPrime
  residualPrimeAtLeastFive : 5 ≤ residualPrime
  levelIsPrime : IsPrime levelPrime
  residualIsPrime : IsPrime residualPrime
  congruence : residualPrime ∣ levelPrime + 1

theorem langWakePrimesDistinct {levelPrime residualPrime : Nat}
    (scope : LangWakeNumericScope levelPrime residualPrime) :
    levelPrime ≠ residualPrime := by
  intro h
  subst levelPrime
  have hone : residualPrime ∣ 1 :=
    (Nat.dvd_add_iff_right (Nat.dvd_refl residualPrime)).mpr scope.congruence
  have hle := Nat.le_of_dvd (by decide : 0 < (1 : Nat)) hone
  have hge := scope.residualPrimeAtLeastFive
  omega

theorem samePrimeOutsideLangWake (p : Nat) : ¬ LangWakeNumericScope p p :=
  fun scope => langWakePrimesDistinct scope rfl

theorem levelThreeOutsideLangWake (residualPrime : Nat) :
    ¬ LangWakeNumericScope 3 residualPrime := by
  intro scope
  have := scope.levelPrimeAtLeastFive
  omega

theorem levelSevenOutsideLangWake (residualPrime : Nat) :
    ¬ LangWakeNumericScope 7 residualPrime := by
  intro scope
  have hdiv : residualPrime ∣ 8 := scope.congruence
  have hle : residualPrime ≤ 8 := Nat.le_of_dvd (by decide) hdiv
  have hge := scope.residualPrimeAtLeastFive
  have hcases : residualPrime = 5 ∨ residualPrime = 6 ∨
      residualPrime = 7 ∨ residualPrime = 8 := by omega
  rcases hcases with h | h | h | h
  all_goals subst residualPrime
  · simp [Nat.dvd_iff_mod_eq_zero] at hdiv
  · simp [Nat.dvd_iff_mod_eq_zero] at hdiv
  · simp [Nat.dvd_iff_mod_eq_zero] at hdiv
  · have hfactor := scope.residualIsPrime.2 2 (by decide : 2 ∣ 8)
    omega

theorem levelElevenOutsideLangWake (residualPrime : Nat) :
    ¬ LangWakeNumericScope 11 residualPrime := by
  intro scope
  have hdiv : residualPrime ∣ 12 := scope.congruence
  have hle : residualPrime ≤ 12 := Nat.le_of_dvd (by decide) hdiv
  have hge := scope.residualPrimeAtLeastFive
  have hcases : residualPrime = 5 ∨ residualPrime = 6 ∨ residualPrime = 7 ∨
      residualPrime = 8 ∨ residualPrime = 9 ∨ residualPrime = 10 ∨
      residualPrime = 11 ∨ residualPrime = 12 := by omega
  rcases hcases with h | h | h | h | h | h | h | h
  all_goals subst residualPrime
  · simp [Nat.dvd_iff_mod_eq_zero] at hdiv
  · have hfactor := scope.residualIsPrime.2 2 (by decide : 2 ∣ 6)
    omega
  · simp [Nat.dvd_iff_mod_eq_zero] at hdiv
  · simp [Nat.dvd_iff_mod_eq_zero] at hdiv
  · simp [Nat.dvd_iff_mod_eq_zero] at hdiv
  · simp [Nat.dvd_iff_mod_eq_zero] at hdiv
  · simp [Nat.dvd_iff_mod_eq_zero] at hdiv
  · have hfactor := scope.residualIsPrime.2 2 (by decide : 2 ∣ 12)
    omega

end SixBirdsBSD.Closure.EtaApplicability
