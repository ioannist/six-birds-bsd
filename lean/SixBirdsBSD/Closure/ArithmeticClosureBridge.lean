import SixBirdsBSD.Closure.ScalarClosure

/-!
An explicit conditional bridge from a formed-layer closure to its scalar
readout. Intertwining is a uniform comparison law, not a certificate that
the original arithmetic state is closed. No native arithmetic comparison
or interpreted master-theorem application is constructed in this module.
-/

namespace SixBirdsBSD.Closure.ArithmeticClosureBridge

open Lean.Grind
open SixBirdsBSD.Closure.ScalarClosure

universe u v

/-- Fixed data precede this uniform law. It relates the two operations
on every state and contains no distinguished BSD equality. -/
def ReadoutIntertwines {A : Type u} {R : Type v} [Field R]
    (C : SixBirdsBSD.F1ClosureOp A) (readout : A → R × R) : Prop :=
  ∀ x, readout (C x) = average (readout x)

/-- Observed fixedness, unlike full fixedness, permits changes in fibers. -/
theorem observedClosedIffEqual {A : Type u} {R : Type v} [Field R]
    (hTwo : (2 : R) ≠ 0)
    (C : SixBirdsBSD.F1ClosureOp A) (readout : A → R × R)
    (hCompare : ReadoutIntertwines C readout) (x : A) :
    readout (C x) = readout x ↔ (readout x).1 = (readout x).2 := by
  rw [hCompare x]
  exact scalarClosedIffEqual hTwo (readout x)

/-- A closed original state returns scalar equality under the comparison.
Idempotence alone would only close C(x), which is a different state. -/
theorem formedClosedImpliesEqual {A : Type u} {R : Type v} [Field R]
    (hTwo : (2 : R) ≠ 0)
    (C : SixBirdsBSD.F1ClosureOp A) (readout : A → R × R)
    (hCompare : ReadoutIntertwines C readout) (x : A)
    (hClosed : ClosureOp.IsClosed C x) : (readout x).1 = (readout x).2 := by
  apply (observedClosedIffEqual hTwo C readout hCompare x).mp
  exact congrArg readout hClosed

/-- Full equivalence needs information separating the state from its
closure image. Global injectivity is one sufficient, explicit condition;
it must not be assumed for a many-to-one arithmetic scalar projection. -/
theorem formedClosedIffEqualOfInjective {A : Type u} {R : Type v} [Field R]
    (hTwo : (2 : R) ≠ 0)
    (C : SixBirdsBSD.F1ClosureOp A) (readout : A → R × R)
    (hCompare : ReadoutIntertwines C readout)
    (hFaithful : Function.Injective readout) (x : A) :
    ClosureOp.IsClosed C x ↔ (readout x).1 = (readout x).2 := by
  constructor
  · exact formedClosedImpliesEqual hTwo C readout hCompare x
  · intro hEq
    exact hFaithful ((observedClosedIffEqual hTwo C readout hCompare x).mpr hEq)

/-- The arithmetic-layer comparison, original-state fixedness, and exact
readout match are separate conditional hypotheses of this landing. -/
theorem formedClosureForcesStrongBSD
    (shell : SixBirdsBSD.Closure.SelShell.selBSDShell)
    [Field shell.Scalar] (hTwo : (2 : shell.Scalar) ≠ 0)
    (readout : shell.FormedLayer → shell.Scalar × shell.Scalar)
    (hCompare : ReadoutIntertwines shell.closureAssumption readout)
    (original : shell.FormedLayer) (hOriginal : readout original = shellPair shell)
    (hClosed : ClosureOp.IsClosed shell.closureAssumption original) :
    shell.L_derivative_over_factorial = shell.strongBSDRightSide := by
  have hEq := formedClosedImpliesEqual hTwo shell.closureAssumption
    readout hCompare original hClosed
  rw [hOriginal] at hEq
  exact hEq

/-- The existing recognition content fixes the scalar observation, not
necessarily every datum in the formed layer. -/
theorem recognitionFixesFormedReadout
    (shell : SixBirdsBSD.Closure.SelShell.selBSDShell)
    [Field shell.Scalar] (hTwo : (2 : shell.Scalar) ≠ 0)
    (readout : shell.FormedLayer → shell.Scalar × shell.Scalar)
    (hCompare : ReadoutIntertwines shell.closureAssumption readout)
    (original : shell.FormedLayer) (hOriginal : readout original = shellPair shell)
    (recognition : SixBirdsBSD.Closure.SelShell.piBSD shell) :
    readout (shell.closureAssumption original) = readout original := by
  apply (observedClosedIffEqual hTwo shell.closureAssumption
    readout hCompare original).mpr
  rw [hOriginal]
  exact SixBirdsBSD.Closure.SelShell.piBSDForcesStrongBSD shell recognition

/-- Executable equality check on supplied exact scalar data. This does not
compute the BSD factors or decide the quantified arithmetic source records. -/
def verifyScalarReadout {R : Type v} [DecidableEq R] (x : R × R) : Bool :=
  decide (x.1 = x.2)

theorem verifyScalarReadoutIffClosed {R : Type v} [Field R] [DecidableEq R]
    (hTwo : (2 : R) ≠ 0) (x : R × R) :
    verifyScalarReadout x = true ↔
      ClosureOp.IsClosed (scalarClosure hTwo) x := by
  rw [scalarClosedIffEqual hTwo]
  simp [verifyScalarReadout]

end SixBirdsBSD.Closure.ArithmeticClosureBridge
