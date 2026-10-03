import SixBirdsBSD.Closure.LocalUnitSupport
import SixBirdsBSD.Apparatus.FinitePairings

/-!
Exact algebra and local checks for the 571a1 two-descent witness, together
with a general pairing-to-two-primary collapse theorem. PARI's certified
descent supplies arithmetic rank and completeness; it is not run by Lean.
No type below is declared to be the actual arithmetic Sha group.
-/
namespace SixBirdsBSD.Closure.ShaDescent

open LocalUnitSupport
open SixBirdsBSD.Apparatus.FinitePairings
open SixBirdsBSD.Apparatus.SupportPrimeNoGo

def curve571a1 : IntegralModel := ⟨0, -1, 1, -929, -10595⟩

def quarticOne (x : Rat) : Rat := -4*x^4 - 60*x^3 - 232*x^2 - 52*x - 3
def quarticTwo (x : Rat) : Rat := -11*x^4 - 68*x^3 - 52*x^2 + 164*x - 64

def xNumeratorOne (x : Rat) : Rat := 69*x^4 + 1036*x^3 + 4006*x^2 + 898*x + 52
def yNumeratorOne (x : Rat) : Rat := -2*x^6 - 16*x^5 - 10*x^4 - 10*x^3 - 30*x^2 - 46*x - 5
def xNumeratorTwo (x : Rat) : Rat := 190*x^4 + 1174*x^3 + 898*x^2 - 2832*x + 1105
def yNumeratorTwo (x : Rat) : Rat := 3*x^6 + 2*x^5 - 20*x^4 + 50*x^3 - 10*x^2 + 12*x - 14

/-- Clearing denominators in the original curve equation for a cover map:
X=N/y^2 and 2Y+1=A/y^3, with y^2=Q. This is the actual polynomial identity,
not a supplied claim that a cover has the desired Jacobian. -/
def ClearedCurveEquation (q n a : Rat) : Prop :=
  a^2 = 4*n^3 - 4*n^2*q - 3716*n*q^2 - 42379*q^3

theorem quarticCoverIdentities (x : Rat) :
    ClearedCurveEquation (quarticOne x) (xNumeratorOne x) (yNumeratorOne x) ∧
    ClearedCurveEquation (quarticTwo x) (xNumeratorTwo x) (yNumeratorTwo x) := by
  simp only [ClearedCurveEquation, quarticOne, quarticTwo,
    xNumeratorOne, yNumeratorOne, xNumeratorTwo, yNumeratorTwo]
  constructor <;> grind

def quarticI (a b c d e : Int) : Int := 12*a*e - 3*b*d + c*c
def quarticJ (a b c d e : Int) : Int :=
  72*a*c*e + 9*b*c*d - 27*a*d*d - 27*b*b*e - 2*c*c*c

theorem curveAndQuarticInvariants :
    (c4 curve571a1, c6 curve571a1, discriminant curve571a1) =
      (44608, 9421480, -571) ∧
    quarticI (-4) (-60) (-232) (-52) (-3) = c4 curve571a1 ∧
    quarticJ (-4) (-60) (-232) (-52) (-3) = 2*c6 curve571a1 ∧
    quarticI (-11) (-68) (-52) 164 (-64) = c4 curve571a1 ∧
    quarticJ (-11) (-68) (-52) 164 (-64) = 2*c6 curve571a1 ∧
    4*(c4 curve571a1)^3 - (2*c6 curve571a1)^2 = 27*(-146176) := by
  decide +kernel

/-- Fisher's Jacobian model is Y^2=X^3-27 I X-27 J. The rational
coordinate change to the repository's integral curve is computed here. -/
def fisherX (x : Rat) : Rat := 36*x - 12
def fisherY (y : Rat) : Rat := 216*y + 108

theorem fisherJacobianCoordinates (x y : Rat)
    (h : y^2 + y = x^3 - x^2 - 929*x - 10595) :
    (fisherY y)^2 = (fisherX x)^3 - 27*44608*(fisherX x) - 27*18842960 := by
  simp only [fisherX, fisherY]
  grind

theorem fisherCoordinateInverse (x y : Rat) :
    ((fisherX x) + 12)/36 = x ∧ ((fisherY y) - 108)/216 = y := by
  simp only [fisherX, fisherY]
  constructor <;> grind

/-- Exact rational evaluations give real solubility through positive
right sides. The real square-root existence theorem is not mechanized. -/
theorem realSolubilityInputs :
    quarticOne (-2/17) = 293/83521 ∧ (0 : Rat) < quarticOne (-2/17) ∧
    quarticTwo (-15/4) = 101/256 ∧ (0 : Rat) < quarticTwo (-15/4) := by
  decide +kernel

/-- Odd values congruent to one modulo eight are squares in Q_2. Lean
checks the exact numerical hypotheses; the local square criterion is imported. -/
theorem twoAdicSolubilityInputs :
    quarticOne 1 = -351 ∧ quarticTwo 1 = -31 ∧
    (-351 : Int) % 8 = 1 ∧ (-31 : Int) % 8 = 1 := by decide +kernel

/-- Smooth residue points at the only odd bad prime, for Hensel lifting. -/
theorem badPrimeSolubilityInputs :
    IsPrime 571 ∧ quarticOne 0 = -3 ∧ quarticTwo 2 = -664 ∧
    ((219 : Int)^2 + 3) % 571 = 0 ∧ (2*219 : Int) % 571 ≠ 0 ∧
    ((139 : Int)^2 + 664) % 571 = 0 ∧ (2*139 : Int) % 571 ≠ 0 := by
  decide +kernel

/-! Generic torsion argument. For an arithmetic group, double means
addition to itself and Value is the actual pairing target (e.g. Q/Z).
Balanced doubling follows from biadditivity in both arguments. -/

def doubleIterate {G : Type} (double : G → G) : Nat → G → G
  | 0, x => x
  | k + 1, x => double (doubleIterate double k x)

theorem iterateCommutes {G : Type} (double : G → G) (k : Nat) (x : G) :
    doubleIterate double k (double x) = doubleIterate double (k+1) x := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg double ih

def NondegenerateOnKernelTwo {G Value : Type} (zeroG : G) (double : G → G)
    (zeroValue : Value) (pair : G → G → Value) : Prop :=
  ∀ x, double x = zeroG →
    (∀ y, double y = zeroG → pair x y = zeroValue) → x = zeroG

/-- A nondegenerate restriction of the full pairing to G[2] excludes
nonzero doubles of G[4]. No finiteness assumption on the ambient G is needed. -/
theorem noNonzeroDoubleOfFourTorsion {G Value : Type}
    (zeroG : G) (double : G → G) (zeroValue : Value) (pair : G → G → Value)
    (hbalanced : ∀ x y, pair (double x) y = pair x (double y))
    (hzero : ∀ x, pair x zeroG = zeroValue)
    (hnd : NondegenerateOnKernelTwo zeroG double zeroValue pair)
    (x : G) (hx : double (double x) = zeroG) : double x = zeroG := by
  apply hnd (double x) hx
  intro y hy
  rw [hbalanced, hy, hzero]

/-- Descend from any power-of-two annihilator, including an ambient group
that is not assumed finite. This also excludes divisible two-primary tails. -/
theorem primaryCollapse {G : Type} (zeroG : G) (double : G → G)
    (hzero : double zeroG = zeroG)
    (hfour : ∀ x, double (double x) = zeroG → double x = zeroG)
    (k : Nat) (x : G) (hx : doubleIterate double k x = zeroG) : double x = zeroG := by
  induction k generalizing x with
  | zero => change x = zeroG at hx; rw [hx, hzero]
  | succ k ih =>
    apply hfour x
    exact ih (double x) ((iterateCommutes double k x).trans hx)

def KernelTwo {G : Type} (zeroG : G) (double : G → G) := {x : G // double x = zeroG}
def TwoPrimary {G : Type} (zeroG : G) (double : G → G) :=
  {x : G // ∃ k, doubleIterate double k x = zeroG}

def kernelToPrimary {G : Type} (zeroG : G) (double : G → G)
    (x : KernelTwo zeroG double) : TwoPrimary zeroG double := ⟨x.val, 1, x.property⟩

def primaryToKernel {G : Type} (zeroG : G) (double : G → G)
    (hzero : double zeroG = zeroG)
    (hfour : ∀ x, double (double x) = zeroG → double x = zeroG)
    (x : TwoPrimary zeroG double) : KernelTwo zeroG double :=
  ⟨x.val, by obtain ⟨k, hk⟩ := x.property; exact primaryCollapse zeroG double hzero hfour k x.val hk⟩

theorem primaryKernelEquivalence {G : Type} (zeroG : G) (double : G → G)
    (hzero : double zeroG = zeroG)
    (hfour : ∀ x, double (double x) = zeroG → double x = zeroG) :
    (∀ x : KernelTwo zeroG double,
      primaryToKernel zeroG double hzero hfour (kernelToPrimary zeroG double x) = x) ∧
    (∀ x : TwoPrimary zeroG double,
      kernelToPrimary zeroG double (primaryToKernel zeroG double hzero hfour x) = x) := by
  constructor <;> intro x <;> apply Subtype.ext <;> rfl

/-- The existing H_2 model satisfies the actual pairing hypotheses. -/
theorem modelTwoPairingHypotheses :
    (∀ x y : Plane 2, pairing (addPlane x x) y = pairing x (addPlane y y)) ∧
    (∀ x : Plane 2, pairing x (zeroPlane 2) = 0) ∧
    NondegenerateOnKernelTwo (zeroPlane 2) (fun x => addPlane x x) (0 : Fin 2) pairing := by
  unfold NondegenerateOnKernelTwo
  decide +kernel

/-- On H_4 the full pairing is perfect, but its restriction to two-torsion
is zero. The four-torsion tail therefore defeats the collapse hypothesis. -/
theorem modelFourFalseControl :
    (∀ x y : Plane 4, addPlane x x = zeroPlane 4 → addPlane y y = zeroPlane 4 →
      pairing x y = 0) ∧
    ¬ NondegenerateOnKernelTwo (zeroPlane 4) (fun x => addPlane x x) (0 : Fin 4) pairing ∧
    ∃ x : Plane 4, addPlane (addPlane x x) (addPlane x x) = zeroPlane 4 ∧
      addPlane x x ≠ zeroPlane 4 := by
  unfold NondegenerateOnKernelTwo
  decide +kernel

end SixBirdsBSD.Closure.ShaDescent
