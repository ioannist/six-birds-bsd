import SixBirdsBSD.Closure.OddPrimaryBridge

/-!
Finite algebra supporting the written arithmetic core-vertex construction
for 1913b1 at three. Tate uniformization, the closed Galois image and the
core-vertex existence theorems remain explicit external inputs. The cocycle
calculation is uniform over its group carrier, not an enumeration of groups.
-/
namespace SixBirdsBSD.Closure.StarkCoreVertices

open SixBirdsBSD.Apparatus.FinitePairings
open LocalUnitSupport OddPrimaryBridge

theorem inertiaInputs :
    ExactValuation 1913 2 (discriminant curve1913b1) ∧
    c4 curve1913b1 % 1913 ≠ 0 ∧ (2*2 : Fin 3) = 1 := by decide +kernel

theorem frobeniusFourthPowerIsNegative : ∀ a b c d : Fin 3,
    a+d = 2 → a*d-b*c = 2 →
    ∀ x, powerAction (matrixAction a b c d) 4 x = negPlane x := by
  decide +kernel

/-- Sah's central-element argument over the actual residue module.
The explicit coboundary is c(z), since minus two equals one in F_3. -/
theorem centralNegativeCocycleIsCoboundary {G : Type}
    (mul : G → G → G) (act : G → Plane 3 → Plane 3)
    (c : G → Plane 3) (z : G)
    (hz : ∀ g, mul g z = mul z g)
    (hneg : ∀ x, act z x = negPlane x)
    (hc : ∀ g h, c (mul g h) = addPlane (c g) (act g (c h))) :
    ∀ g, c g = addPlane (act g (c z)) (negPlane (c z)) := by
  have hreturn : ∀ a b v : Plane 3,
      addPlane a b = addPlane v (negPlane a) →
      a = addPlane b (negPlane v) := by decide +kernel
  intro g
  have h := congrArg c (hz g)
  rw [hc, hc, hneg] at h
  exact hreturn (c g) (act g (c z)) (c z) h

def transvectionDifference {n : Nat} [NeZero n] (u : Fin n) (x : Plane n) : Plane n :=
  (u*x.2, 0)

theorem transvectionRankOneThree : ∀ u : Fin 3, u ≠ 0 →
    (∀ x, transvectionDifference u x = zeroPlane 3 ↔ x.2 = 0) ∧
    (∀ y, (∃ x, transvectionDifference u x = y) ↔ y.2 = 0) := by
  decide +kernel

/-- At the concrete Stark coefficient level Z/27, the same transvection
has rank-one image and kernel. Fourteen is the inverse of two. -/
theorem transvectionReturn27 :
    (2*14 : Fin 27) = 1 ∧
    (∀ x : Plane 27, transvectionDifference 2 x = zeroPlane 27 ↔ x.2 = 0) ∧
    (∀ y : Plane 27, transvectionDifference 2 (0,14*y.1) = (y.1,0)) := by
  decide +kernel

def principalImage27 (a y : Fin 27) : Prop := ∃ x : Fin 27, a*x = y

instance (a y : Fin 27) : Decidable (principalImage27 a y) :=
  inferInstanceAs (Decidable (∃ x : Fin 27, a*x = y))

/-- Scaling a Stark basis by the unit two changes no generated ideal. -/
theorem unitScalingPreservesPrincipalImages27 : ∀ a y : Fin 27,
    principalImage27 a y ↔ principalImage27 (2*a) y := by
  decide +kernel

/-- All three Fitting levels of the 3J cokernel are unchanged by unit
scaling, whereas lifting the prescribed basis through squaring changes. -/
theorem fittingLadderLosesBasisSquareClass27 :
    (∀ y : Fin 27, principalImage27 9 y ↔ principalImage27 18 y) ∧
    (∀ y : Fin 27, principalImage27 3 y ↔ principalImage27 6 y) ∧
    (∀ y : Fin 27, principalImage27 1 y ↔ principalImage27 2 y) ∧
    (∃ v : Fin 27, v*v = 1) ∧ ¬ (∃ v : Fin 27, v*v = 2) := by
  decide +kernel

def localisationModel27 (x : Plane 27) : Plane 27 := (3*x.2, -(3 : Fin 27)*x.1)

/-- Derived reduction has a nonzero H1, although the compact integral
presentation has zero kernel. At this coefficient level its kernel has
nine elements and its image has eighty-one elements. -/
theorem localisationModelCounts27 :
    (∀ x : Plane 27, localisationModel27 x = zeroPlane 27 ↔
      x.1.val % 9 = 0 ∧ x.2.val % 9 = 0) ∧
    ((elements 27).filter fun x => decide (localisationModel27 x = zeroPlane 27)).length = 9 ∧
    ((elements 27).map localisationModel27).eraseDups.length = 81 := by
  decide +kernel

end SixBirdsBSD.Closure.StarkCoreVertices
