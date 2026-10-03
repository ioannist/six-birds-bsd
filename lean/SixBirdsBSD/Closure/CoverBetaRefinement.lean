import SixBirdsBSD.Closure.GlobalTameProduct

/-!
Actual good-fiber counts and characteristic-zero polynomial/refinement algebra.
Written arithmetic identifies these fibers and constructs the five-adic root.
Cover Frobenius eigenvalues are not identified with the manuscript's U_p beta.
-/
namespace SixBirdsBSD.Closure.CoverBetaRefinement

open LocalUnitSupport OddPrimaryBridge
open Lean.Grind
attribute [local instance] Ring.intCast

def goodFiberFive : IntegralModel := ⟨0,0,0,2,0⟩
def goodFiberSeven : IntegralModel := ⟨0,0,0,6,0⟩

theorem actualCoverFibers :
    (77 : Int) % 5 = 2 ∧ (55 : Int) % 7 = 6 ∧
    discriminant goodFiberFive % 5 ≠ 0 ∧
    discriminant goodFiberSeven % 7 ≠ 0 ∧
    pointCount goodFiberFive 5 = 2 ∧ pointCount goodFiberSeven 7 = 8 ∧
    ((6-(pointCount goodFiberFive 5 : Int), 5) : Int × Int) = (4,5) ∧
    ((8-(pointCount goodFiberSeven 7 : Int), 7) : Int × Int) = (0,7) := by
  decide +kernel

/-- At characteristics five and seven these are the usual Hasse-invariant
formula inputs c4 and -c6. The arithmetic criterion is an external import. -/
theorem hasseNumericalControls :
    c4 goodFiberFive % 5 = 4 ∧ -c6 goodFiberSeven % 7 = 0 := by decide +kernel

/-- A polynomial Bezout identity, valid over every commutative ring.
For trace four and determinant five it gives the nonzero scalar twenty. -/
theorem frobeniusSquareBezout {K : Type} [CommRing K] (a p b : K) :
    b*(b*b-a*b+p) - (b-a)*(b*b+p) = a*p := by grind

/-- A Frobenius eigenvalue can obey beta^2=-q only when its trace is zero.
The hypotheses are ordinary field laws and two explicit polynomial equations. -/
theorem squareRelationRequiresZeroTrace {K : Type} [Field K] [IsCharP K 0]
    (a p b : K) (hp : p ≠ 0)
    (hf : b*b-a*b+p=0) (hs : b*b+p=0) : a=0 := by grind

theorem ordinaryCoverSquareIncompatible {K : Type} [CommRing K] [IsCharP K 0]
    (b : K) (hf : b*b-4*b+5=0) : b*b+5 ≠ 0 := by
  intro hs
  grind

/-- Inverting beta squared cannot give -1/p on the ordinary cover either. -/
theorem ordinaryInverseSquareIncompatible {K : Type} [Field K] [IsCharP K 0]
    (b : K) (hf : b*b-4*b+5=0) : (b*b)⁻¹ ≠ -(5:K)⁻¹ := by
  intro h
  grind

/-- Both roots of T^2-4T+5 are constructed once i^2=-1 is given. Existence
of the five-adic i is proved by the written compatible digit lift. -/
theorem constructedRefinements {K : Type} [Field K] [IsCharP K 0]
    (i : K) (hi : i*i+1=0) :
    (2+i)*(2+i)-4*(2+i)+5=0 ∧
    (2-i)*(2-i)-4*(2-i)+5=0 ∧
    (2+i)*(2-i)=5 ∧ (2+i) ≠ (2-i) ∧
    ((2+i)*(2+i))⁻¹ = (3-4*i)/25 ∧
    ((2-i)*(2-i))⁻¹ = (3+4*i)/25 ∧
    ((2+i)*(2+i))⁻¹ ≠ ((2-i)*(2-i))⁻¹ := by grind

/-- The lens retains the inertia determinant, trace and Frobenius determinant,
but erases the selected eigenline. It cannot return both inverse-square
factors. This is not a no-go for a normalized eta value with a moving moment. -/
theorem noRefinementFactorFromUnorderedFrobenius
    {K : Type} [Field K] [IsCharP K 0] (i : K) (hi : i*i+1=0) :
    ¬ ∃ readout : Int × Int × Int → K,
      readout (2,4,5) = ((2+i)*(2+i))⁻¹ ∧
      readout (2,4,5) = ((2-i)*(2-i))⁻¹ := by
  rintro ⟨readout,hplus,hminus⟩
  have h := constructedRefinements i hi
  exact h.2.2.2.2.2.2 (hplus.symm.trans hminus)

def recoverInverseSquare {K : Type} [Field K] (i : K) (isUnit : Bool) : K :=
  if isUnit then ((2+i)*(2+i))⁻¹ else ((2-i)*(2-i))⁻¹

/-- Retaining the selected root's unit status repairs BOTH branches of the
readout. The actual five-adic unit predicate satisfies the two observational
conditions by the written lift; they do not assert the desired factor. -/
theorem completeRefinementRepair {K : Type} [Field K] [IsCharP K 0]
    (i b : K) (hi : i*i+1=0) (hb : b*b-4*b+5=0)
    (observeUnit : K → Bool)
    (hu : observeUnit (2+i)=true) (hn : observeUnit (2-i)=false) :
    recoverInverseSquare i (observeUnit b) = (b*b)⁻¹ := by
  have hroots : b=2+i ∨ b=2-i := by grind
  rcases hroots with h | h
  · rw [h,hu]; rfl
  · rw [h,hn]; rfl

/-- The zero-trace cover has exactly the square relation; the inverse-square
factor there is independent of which of its two eigenvalues is selected. -/
theorem zeroTraceInverseSquare {K : Type} [Field K] [IsCharP K 0]
    (b : K) (h : b*b+7=0) : (b*b)⁻¹ = -(7:K)⁻¹ := by grind

/-- Modulo five the unique nonzero root is four. The lift modulo twenty-five
is nine, while the other root twenty is divisible by five exactly once. -/
theorem finiteRefinementControls :
    (∀ b : Fin 5, b*b-4*b+5=0 ↔ b=0 ∨ b=4) ∧
    (9*9-4*9+5 : Fin 25)=0 ∧ (20*20-4*20+5 : Fin 25)=0 ∧
    (9*9+5 : Fin 25) ≠ 0 ∧ (20*20+5 : Fin 25) ≠ 0 ∧
    ExactValuation 5 1 20 ∧
    (0*0-4*0+5 : Fin 5)=0 ∧ (0*0+5 : Fin 5)=0 := by decide +kernel

/-- Once a residue branch makes b+c-4 nonzero, the Frobenius polynomial
has at most one root on that branch. The written five-adic reduction
argument supplies this condition for either residue root zero or four. -/
theorem refinementBranchUnique {K : Type} [Field K] (b c : K)
    (hb : b*b-4*b+5=0) (hc : c*c-4*c+5=0)
    (hsum : b+c ≠ 4) : b=c := by grind

/-- Traces of powers of the actual five-adic good-fiber Frobenius.
This is the characteristic-polynomial recurrence, with t_0=2 and t_1=4. -/
def tracePair : Nat → Int × Int
  | 0 => (2,4)
  | n+1 => ((tracePair n).2, 4*(tracePair n).2-5*(tracePair n).1)

theorem unramifiedTraceResidues (n : Nat) :
    ((tracePair (n+1)).1 % 5 = 1 ∨ (tracePair (n+1)).1 % 5 = 4) ∧
    ((tracePair (n+1)).2 % 5 = 1 ∨ (tracePair (n+1)).2 % 5 = 4) := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    change ((tracePair (n+1)).2 % 5 = 1 ∨ (tracePair (n+1)).2 % 5 = 4) ∧
      ((4*(tracePair (n+1)).2-5*(tracePair (n+1)).1) % 5 = 1 ∨
       (4*(tracePair (n+1)).2-5*(tracePair (n+1)).1) % 5 = 4)
    rcases ih.2 with h | h
    all_goals constructor
    · exact Or.inl h
    · right; omega
    · exact Or.inr h
    · left; omega

/-- Every positive unramified residue degree still has nonzero trace, so
passing to a larger residue field cannot repair the square relation. -/
theorem unramifiedSquareIncompatible {K : Type} [Field K] [IsCharP K 0]
    (n : Nat) (b : K)
    (hf : b*b-((tracePair (n+1)).1 : K)*b+5^(n+1)=0) :
    b*b+5^(n+1) ≠ 0 := by
  intro hs
  have hp : (5 : K)^(n+1) ≠ 0 := by
    intro h
    have := Field.of_pow_eq_zero (5 : K) (n+1) h
    grind
  have ht := squareRelationRequiresZeroTrace _ _ b hp hf hs
  have hz : (tracePair (n+1)).1=0 := by
    simpa using (IsCharP.intCast_eq_zero_iff (α := K) 0 _).mp ht
  have hr := (unramifiedTraceResidues n).1
  rw [hz] at hr
  omega

end SixBirdsBSD.Closure.CoverBetaRefinement
