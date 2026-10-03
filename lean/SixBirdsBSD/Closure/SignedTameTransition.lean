import SixBirdsBSD.Closure.CoverBetaRefinement

/-!
Native seven-adic cyclotomic/tame transition algebra. The written construction
supplies the actual local fields, valuation and norm. These polynomial and
coefficient proofs do not instantiate a signed Selmer or OC certificate.
-/
namespace SixBirdsBSD.Closure.SignedTameTransition

open Lean.Grind
attribute [local instance] Ring.intCast

def phiSeven {K : Type} [CommRing K] (z : K) : K :=
  1+z+z^2+z^3+z^4+z^5+z^6
def gaussSeven {K : Type} [CommRing K] (z : K) : K :=
  z+z^2+z^4-z^3-z^5-z^6
def gaussQuotient {K : Type} [CommRing K] (z : K) : K :=
  z^6+z^5-3*z^4+z^3+z^2-7*z+7

/-- Explicit quadratic cyclotomic overlap, not a disjointness premise. -/
theorem gaussSquarePolynomialIdentity {K : Type} [CommRing K] (z : K) :
    gaussSeven z * gaussSeven z+7=phiSeven z * gaussQuotient z := by
  simp only [gaussSeven,phiSeven,gaussQuotient]
  grind

theorem quadraticCyclotomicOverlap {K : Type} [Field K] [IsCharP K 0]
    (z : K) (hz : phiSeven z=0) :
    gaussSeven z * gaussSeven z= -7 ∧ gaussSeven z ≠ 0 := by
  have h := gaussSquarePolynomialIdentity z
  rw [hz] at h
  grind

def transitionSeven {K : Type} [CommRing K] (x : K) : K :=
  7*x^2-21*x^4+35*x^6-35*x^8+21*x^10-7*x^12+x^14

theorem cyclotomicSquareTransition {K : Type} [CommRing K] (x : K) :
    transitionSeven x=1-(1-x*x)^7 := by
  simp only [transitionSeven]
  grind

/-- Derived from compatible roots of unity and square-root coordinates. -/
theorem nativeUniformizerRelation {K : Type} [CommRing K] (x y z : K)
    (hx : x*x=1-z) (hy : y*y=1-z^7) : y*y=transitionSeven x := by
  rw [cyclotomicSquareTransition,hx]
  grind

theorem leadingSlopeRepair {K : Type} [Field K] [IsCharP K 0]
    (i pi : K) (hi : i*i= -1) (hpi : pi^4= -7) :
    (i*pi^2)*(i*pi^2)=7 ∧ pi*pi ≠ 7 ∧ pi^2*pi^2 ≠ 7 := by
  grind

/-- A native eighth-root residue in F_49=F_7(i). Its simple Hensel lift
changes the sign of the quartic cover parameter without changing inertia. -/
theorem unramifiedPhaseControl {K : Type} [Field K] [IsCharP K 7]
    (i : K) (hi : i*i= -1) :
    (2+2*i)*(2+2*i)=i ∧ (2+2*i)^4= -1 ∧ (2+2*i)^8=1 := by grind

/-- Passing from residue degree one to two squares Frobenius. The
trace-zero square relation cannot be copied unchanged to that operator. -/
theorem unramifiedFrobeniusSquareControl {K : Type} [Field K] [IsCharP K 0]
    (b : K) (hb : b*b= -7) :
    (b*b)*(b*b)=49 ∧ (b*b)*(b*b)+49 ≠ 0 := by grind

def unitPolynomial {K : Type} [Field K] (x : K) : K :=
  1-3*x^2+5*x^4-5*x^6+3*x^8-x^10+x^12/7

theorem transitionFactorization {K : Type} [Field K] [IsCharP K 0] (x : K) :
    transitionSeven x=7*x^2*unitPolynomial x := by
  simp only [transitionSeven,unitPolynomial]
  grind

/-- The literal binomial argument is U, whose constant term is one.
The corrected argument U-1 has constant term zero. -/
theorem binomialConstantControls :
    unitPolynomial (0 : Rat)=1 ∧ unitPolynomial (0 : Rat)-1=0 := by decide +kernel

/-- Exact recurrence for the unique formal square root of U in Q[[X]].
The coefficient of X^12 is forced, rather than fitted to a target. -/
theorem squareRootCoefficientsForced (b1 b2 b3 b4 b5 b6 : Rat)
    (h1 : 2*b1= -3) (h2 : 2*b2+b1*b1=5)
    (h3 : 2*b3+2*b1*b2= -5)
    (h4 : 2*b4+2*b1*b3+b2*b2=3)
    (h5 : 2*b5+2*b1*b4+2*b2*b3= -1)
    (h6 : 2*b6+2*b1*b5+2*b2*b4+b3*b3=1/7) :
    b1= -3/2 ∧ b2=11/8 ∧ b3= -7/16 ∧ b4= -13/128 ∧
    b5= -13/256 ∧ b6=281/7168 := by grind

theorem squareRootCoefficientInputs :
    2*(-3/2 : Rat)= -3 ∧
    2*(11/8 : Rat)+(-3/2)*(-3/2)=5 ∧
    2*(-7/16 : Rat)+2*(-3/2)*(11/8)= -5 ∧
    2*(-13/128 : Rat)+2*(-3/2)*(-7/16)+(11/8)*(11/8)=3 ∧
    2*(-13/256 : Rat)+2*(-3/2)*(-13/128)+2*(11/8)*(-7/16)= -1 ∧
    2*(281/7168 : Rat)+2*(-3/2)*(-13/256)+2*(11/8)*(-13/128)+
      (-7/16)*(-7/16)=1/7 := by decide +kernel

/-- The coefficient has seven-adic valuation -1. Multiplying by a
slope of valuation 1/2 leaves a negative valuation, not integrality. -/
theorem coefficientValuationInputs :
    7168=7*1024 ∧ ¬ (7 : Nat) ∣ 281 ∧ ¬ (7 : Nat) ∣ 1024 ∧
    (2 : Int)-4= -2 := by decide +kernel

theorem cyclotomicDegreeControl (n : Nat) : (6*7^n)%4=2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have heq : 6*7^(n+1)=(6*7^n)*7 := by rw [Nat.pow_succ]; omega
    rw [heq,Nat.mul_mod,ih]

/-- An odd-degree field norm changes sign under x -> -x. Its square
relation therefore supplies a legal branch repair using that native norm. -/
theorem normBranchRepair {K L : Type} [Field K] [Field L]
    (norm : L → K) (hneg : ∀ x, norm (-x)= -norm x) (x : L) (y : K)
    (hsquare : norm x * norm x=y*y) :
    ∃ z, (z=x ∨ z= -x) ∧ norm z=y ∧ z*z=x*x := by
  have hcases : norm x=y ∨ norm x= -y := by grind
  rcases hcases with h | h
  · exact ⟨x,Or.inl rfl,h,rfl⟩
  · refine ⟨-x,Or.inr rfl,?_,?_⟩
    · rw [hneg,h]; grind
    · grind

end SixBirdsBSD.Closure.SignedTameTransition
