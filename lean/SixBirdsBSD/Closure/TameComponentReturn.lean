import SixBirdsBSD.Closure.AdditiveFrobeniusDescent
import SixBirdsBSD.Closure.CTDerivedTransport

/-!
Intrinsic tame-inertia determinant algebra, its integral cokernel, and an
equation-derived isogeny boundary control. Arithmetic inertia/cohomology,
component-group and Tate-module identifications are written imports, not
certificate fields in this module. No eta or named-source import is filled.
-/
namespace SixBirdsBSD.Closure.TameComponentReturn

open CTDerivedTransport
open SixBirdsBSD.Apparatus.FinitePresentation
  (IntegerPlane reduceResidue reduceResidueEqIff reduceResidueAdd)
open LocalUnitSupport OddPrimaryBridge

def identityMatrix : Matrix2 := ((1,0),(0,1))
def trace (a : Matrix2) : Int := a.1.1 + a.2.2
def oneMinus (a : Matrix2) : Matrix2 := subtract identityMatrix a
def descentDeterminant (a : Matrix2) : Int := determinant (oneMinus a)

theorem determinantProduct (a b : Matrix2) :
    determinant (compose a b) = determinant a * determinant b := by
  simp only [compose, determinant]
  grind

theorem composeAssociative (a b c : Matrix2) :
    compose (compose a b) c = compose a (compose b c) := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [compose] <;> grind

theorem traceCyclic (a b : Matrix2) : trace (compose a b) = trace (compose b a) := by
  simp only [trace, compose]
  grind

theorem traceDeterminantReturn (a : Matrix2) :
    descentDeterminant a = 1 - trace a + determinant a := by
  simp only [descentDeterminant, oneMinus, subtract, identityMatrix, trace, determinant]
  grind

/-- Exact scalar covariance, stronger than equality modulo units. -/
theorem descentDeterminantBasisInvariant (a b c : Matrix2)
    (hinverse : compose c b = identityMatrix) :
    descentDeterminant (compose b (compose a c)) = descentDeterminant a := by
  have ht : trace (compose b (compose a c)) = trace a := by
    rw [traceCyclic, composeAssociative, hinverse]
    simp [compose, identityMatrix, trace]
  have hd : determinant c * determinant b = 1 := by
    rw [← determinantProduct, hinverse]
    decide +kernel
  rw [traceDeterminantReturn, traceDeterminantReturn, ht,
    determinantProduct, determinantProduct]
  grind

/-- Inertia has determinant one on the elliptic Tate module. Integer
traces zero/one correspond to cyclotomic orders four/six respectively.
The arithmetic identification is external; the return itself is derived. -/
theorem shallowInertiaReturn (a : Matrix2) (hd : determinant a = 1) :
    (trace a = 1 → descentDeterminant a = 1) ∧
    (trace a = 0 → descentDeterminant a = 2) := by
  rw [traceDeterminantReturn, hd]
  constructor <;> intro ht <;> omega

def inertiaSix : Matrix2 := ((0,-1),(1,1))
def inertiaFour : Matrix2 := ((0,-1),(1,0))
def inertiaThree : Matrix2 := ((0,-1),(1,-1))

theorem companionReturns :
    (trace inertiaSix, determinant inertiaSix, descentDeterminant inertiaSix) = (1,1,1) ∧
    (trace inertiaFour, determinant inertiaFour, descentDeterminant inertiaFour) = (0,1,2) ∧
    (trace inertiaThree, determinant inertiaThree, descentDeterminant inertiaThree) = (-1,1,3) ∧
    compose (oneMinus inertiaSix) inertiaSix = identityMatrix := by decide +kernel

def action (a : Matrix2) (x : IntegerPlane) : IntegerPlane :=
  (a.1.1*x.1+a.1.2*x.2, a.2.1*x.1+a.2.2*x.2)

theorem sixCoinvariantsTrivial : ∀ x : IntegerPlane,
    ∃ y, action (oneMinus inertiaSix) y = x := by
  intro x
  refine ⟨(-x.2, x.1+x.2), ?_⟩
  apply Prod.ext <;> simp [action, oneMinus, inertiaSix, subtract, identityMatrix] <;> omega

def parity (x : IntegerPlane) : Fin 2 := reduceResidue 2 (x.1+x.2)

theorem fourImageIffEvenSum (x : IntegerPlane) :
    (∃ y, action (oneMinus inertiaFour) y = x) ↔ (2 : Int) ∣ x.1+x.2 := by
  constructor
  · rintro ⟨y, hy⟩
    have h1 := congrArg Prod.fst hy
    have h2 := congrArg Prod.snd hy
    simp only [action, oneMinus, inertiaFour, subtract, identityMatrix] at h1 h2
    exact ⟨y.2, by omega⟩
  · rintro ⟨k, hk⟩
    refine ⟨(x.1-k,k), ?_⟩
    apply Prod.ext <;> simp [action, oneMinus, inertiaFour, subtract, identityMatrix] <;> omega

theorem parityKernelIffImage (x : IntegerPlane) :
    parity x = 0 ↔ ∃ y, action (oneMinus inertiaFour) y = x := by
  rw [fourImageIffEvenSum]
  have h := reduceResidueEqIff 2 (x.1+x.2) 0
  simpa [parity] using h

theorem sameParityIffDifferenceInImage (x y : IntegerPlane) :
    parity x = parity y ↔
      ∃ z, action (oneMinus inertiaFour) z = (x.1-y.1,x.2-y.2) := by
  rw [fourImageIffEvenSum]
  have h := reduceResidueEqIff 2 (x.1+x.2) (y.1+y.2)
  have heq : x.1+x.2-(y.1+y.2) = x.1-y.1+(x.2-y.2) := by omega
  simpa only [parity, heq] using h

def componentSetoid : Setoid IntegerPlane where
  r := fun x y => parity x = parity y
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

abbrev FourCoinvariants := Quotient componentSetoid

def quotientToParity : FourCoinvariants → Fin 2 := Quotient.lift parity (fun _ _ h => h)
def parityToQuotient (r : Fin 2) : FourCoinvariants :=
  Quotient.mk componentSetoid (r.val,0)

private theorem parityRepresentative : ∀ r : Fin 2, parity (r.val,0) = r := by decide +kernel

/-- This is the quotient by the computed integral image, not a dimension
tag or an assigned component group. Completion at two has the same finite
cokernel; that completion statement is written arithmetic. -/
theorem fourCoinvariantEquivalence :
    (∀ r, quotientToParity (parityToQuotient r) = r) ∧
    (∀ q, parityToQuotient (quotientToParity q) = q) := by
  constructor
  · exact parityRepresentative
  · intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      apply Quotient.sound
      exact parityRepresentative (parity x)

theorem parityAdds (x y : IntegerPlane) :
    parity (x.1+y.1,x.2+y.2) = parity x + parity y := by
  have h := reduceResidueAdd 2 (x.1+x.2) (y.1+y.2)
  have heq : (x.1+x.2)+(y.1+y.2) = x.1+y.1+(x.2+y.2) := by omega
  simpa only [parity, heq] using h

/-- Every group automorphism of the two-element component group fixes
both elements. This supplies the Frobenius step in the order-two lane. -/
theorem twoElementFrobeniusFixed (f : Fin 2 → Fin 2)
    (hzero : f 0 = 0) (hinj : ∀ x y, f x = f y → x = y) : ∀ x, f x = x := by
  intro x
  have hx := x.isLt
  have hfx := (f x).isLt
  by_cases hx0 : x = 0
  · simpa [hx0] using hzero
  · have hf0 : f x ≠ 0 := by
      intro h
      exact hx0 (hinj x 0 (h.trans hzero.symm))
    apply Fin.ext
    have : x.val ≠ 0 := fun h => hx0 (Fin.ext h)
    have : (f x).val ≠ 0 := fun h => hf0 (Fin.ext h)
    omega

/-- At order three, geometric cardinality alone does not fix the rational
component number. Identity and negation have three and one fixed points. -/
theorem threeElementFrobeniusControl :
    (List.finRange 3).filter (fun x => decide (x = x)) = List.finRange 3 ∧
    ((List.finRange 3).filter (fun x => decide (-x = x))).length = 1 := by decide +kernel

def isogenySource : IntegralModel := ⟨11,0,11,0,0⟩
def isogenyTarget : IntegralModel := ⟨11,0,11,-605,-15488⟩

/-- Clearing x^6 verifies the actual Velu map between the two non-CM
equations. The right side is a multiple of the original curve equation,
so no target equation or isogeny certificate is assumed. -/
theorem veluIsogenyPolynomialIdentity (x y : Int) :
    let f := x^3+121*x+121
    let g := y*x^3-1331*x^2-121*x*y-2662*x-242*y-1331
    g^2+11*f*g*x+11*g*x^3-f^3+605*f*x^4+15488*x^6 =
      (x^3-121*x-242)^2 * (y^2+11*x*y+11*y-x^3) := by grind

theorem isogenyBoundaryInputs :
    isogenyTarget.a4 = -5*isogenySource.a1*isogenySource.a3 ∧
    isogenyTarget.a6 =
      -isogenySource.a3*(isogenySource.a1^3+7*isogenySource.a3) ∧
    (c4 isogenySource, c6 isogenySource, discriminant isogenySource) =
      (11737,-1270621,1376254) ∧
    (c4 isogenyTarget, c6 isogenyTarget, discriminant isogenyTarget) =
      (40777,6840251,12160580344) ∧
    (c4 isogenySource)^3 % discriminant isogenySource ≠ 0 ∧
    (c4 isogenyTarget)^3 % discriminant isogenyTarget ≠ 0 ∧
    ExactValuation 11 4 (discriminant isogenySource) ∧
    ExactValuation 11 4 (discriminant isogenyTarget) ∧
    shallowTateBranch isogenySource 11 = none ∧
    shallowTateBranch isogenyTarget 11 = none ∧
    pointCount ⟨0,0,0,0,3⟩ 11 = 12 ∧ pointCount ⟨0,0,0,0,7⟩ 11 = 12 ∧
    ¬ (11 : Int) ∣ (3 : Int) := by decide +kernel

/-- The degree-three similitude can be normalized over Z_11: five is a
simple root of X^2-3 modulo eleven. A nonsquare unit rejects a blanket
claim that every prime-to-eleven isogeny has this scalar normalization. -/
theorem pairingRescalingInputs :
    ((5 : Int)^2-3) % 11 = 0 ∧ (2*5 : Int) % 11 ≠ 0 ∧
    (27 : Int)^2 % 121 = 3 ∧ (753 : Int)^2 % 1331 = 3 ∧
    (∀ r : Fin 11, r*r ≠ 2) := by decide +kernel

end SixBirdsBSD.Closure.TameComponentReturn
