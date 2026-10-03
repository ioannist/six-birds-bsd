import Init.Grind
import SixBirdsBSD.Closure.SelShell

/-!
An explicit scalar closure and its exact return to the BSD readout.

The carrier is the pair of supplied analytic and arithmetic coefficients.
Swapping its entries is an involution; averaging constructs an idempotent
in the vendored Foundations-I interface. Closedness of the ORIGINAL pair
is equivalent to equality of its coefficients. Applying the closure to
a false pair changes the coefficients and proves nothing about that input.

This is a scalar readout construction, not an identification of the full
arithmetic shell's closure operator or a proof of source indispensability.
-/

namespace SixBirdsBSD.Closure.ScalarClosure

open Lean.Grind
universe u

def swap {R : Type u} (x : R × R) : R × R := (x.2, x.1)

theorem swapInvolutive {R : Type u} (x : R × R) : swap (swap x) = x := by
  cases x
  rfl

def residual {R : Type u} [CommRing R] (x : R × R) : R := x.1-x.2

theorem residualSwap {R : Type u} [CommRing R] (x : R × R) :
    residual (swap x) = -residual x := by
  simp only [residual, swap]
  grind

/-- Averaging is derived from the swap involution, with no BSD premise. -/
def average {R : Type u} [Field R] (x : R × R) : R × R :=
  ((x.1+x.2)/2, (x.1+x.2)/2)

theorem averageIdempotent {R : Type u} [Field R]
    (hTwo : (2 : R) ≠ 0) (x : R × R) :
    average (average x) = average x := by
  apply Prod.ext <;> simp only [average] <;> grind

/-- A native instance of the actual vendored Foundations-I interface. -/
def scalarClosure {R : Type u} [Field R] (hTwo : (2 : R) ≠ 0) :
    SixBirdsBSD.F1ClosureOp (R × R) :=
  ⟨average, averageIdempotent hTwo⟩

theorem averageConservesSum {R : Type u} [Field R]
    (hTwo : (2 : R) ≠ 0) (x : R × R) :
    (average x).1+(average x).2 = x.1+x.2 := by
  simp only [average]
  grind

theorem averageSwapInvariant {R : Type u} [Field R] (x : R × R) :
    average (swap x) = average x ∧ swap (average x) = average x := by
  constructor
  · apply Prod.ext <;> simp only [average, swap] <;> grind
  · rfl

/-- Diagonal output and conservation of the input sum uniquely determine
the average. Constant replacement is not a second conserving closure. -/
theorem averageUnique {R : Type u} [Field R]
    (hTwo : (2 : R) ≠ 0) (x y : R × R)
    (hDiag : y.1=y.2) (hSum : y.1+y.2=x.1+x.2) : y=average x := by
  apply Prod.ext <;> simp only [average] <;> grind

/-- Vanishing at the transformed pair does not imply vanishing at the input. -/
theorem averageResidualZero {R : Type u} [Field R] (x : R × R) :
    residual (average x) = 0 := by
  simp only [residual, average]
  grind

theorem scalarClosedIffEqual {R : Type u} [Field R]
    (hTwo : (2 : R) ≠ 0) (x : R × R) :
    ClosureOp.IsClosed (scalarClosure hTwo) x ↔ x.1=x.2 := by
  change average x = x ↔ x.1=x.2
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [average] at h1 h2
    exact h1.symm.trans h2
  · intro h
    apply Prod.ext <;> simp only [average] <;> grind

theorem scalarClosedIffResidualZero {R : Type u} [Field R]
    (hTwo : (2 : R) ≠ 0) (x : R × R) :
    ClosureOp.IsClosed (scalarClosure hTwo) x ↔ residual x = 0 := by
  rw [scalarClosedIffEqual hTwo]
  simp only [residual]
  grind

/-- Requiring the analytic coefficient to survive this scalar closure is
already equivalent to closedness of the ORIGINAL input. -/
theorem averagePreservesFirstIffClosed {R : Type u} [Field R]
    (hTwo : (2 : R) ≠ 0) (x : R × R) :
    (average x).1=x.1 ↔ ClosureOp.IsClosed (scalarClosure hTwo) x := by
  rw [scalarClosedIffEqual hTwo]
  simp only [average]
  grind

/-- The characteristic restriction matters: in characteristic two,
totalized division by two destroys even the nonzero diagonal point. -/
theorem characteristicTwoControl {R : Type u} [Field R]
    (hTwo : (2 : R)=0) (hOne : (1 : R) ≠ 0) :
    residual ((1 : R),1)=0 ∧ average ((1 : R),1) ≠ (1,1) := by
  constructor
  · simp only [residual]
    grind
  · intro h
    have hFirst := congrArg Prod.fst h
    simp only [average] at hFirst
    grind

/-- The target pair uses the original shell coefficients without alteration. -/
def shellPair (shell : SixBirdsBSD.Closure.SelShell.selBSDShell) :
    shell.Scalar × shell.Scalar :=
  (shell.L_derivative_over_factorial, shell.strongBSDRightSide)

/-- Exact scalar BSD translation. The field structure is explicit; no new
recognition or applicability certificate is supplied to obtain this iff. -/
theorem shellClosedIffStrongBSD
    (shell : SixBirdsBSD.Closure.SelShell.selBSDShell)
    [Field shell.Scalar] (hTwo : (2 : shell.Scalar) ≠ 0) :
    ClosureOp.IsClosed (scalarClosure hTwo) (shellPair shell) ↔
      shell.L_derivative_over_factorial = shell.strongBSDRightSide :=
  scalarClosedIffEqual hTwo (shellPair shell)

/-- Return to the shell's original residual, using its existing subtraction
law rather than assuming its opaque operations are the field operations. -/
theorem shellClosedIffResidualZero
    (shell : SixBirdsBSD.Closure.SelShell.selBSDShell)
    [Field shell.Scalar] (hTwo : (2 : shell.Scalar) ≠ 0) :
    ClosureOp.IsClosed (scalarClosure hTwo) (shellPair shell) ↔
      shell.residual = shell.zero := by
  rw [shellClosedIffStrongBSD shell hTwo]
  exact (SixBirdsBSD.Closure.SelShell.piBSDIffStrongBSD shell).symm

/-- The existing quantified recognition predicate fixes the original
scalar pair. The theorem consumes the original supplied recognition content. -/
theorem recognitionFixesShellPair
    (shell : SixBirdsBSD.Closure.SelShell.selBSDShell)
    [Field shell.Scalar] (hTwo : (2 : shell.Scalar) ≠ 0)
    (recognition : SixBirdsBSD.Closure.SelShell.piBSD shell) :
    ClosureOp.IsClosed (scalarClosure hTwo) (shellPair shell) :=
  (shellClosedIffStrongBSD shell hTwo).mpr
    (SixBirdsBSD.Closure.SelShell.piBSDForcesStrongBSD shell recognition)

end SixBirdsBSD.Closure.ScalarClosure
