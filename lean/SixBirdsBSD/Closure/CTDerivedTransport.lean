import SixBirdsBSD.Closure.OddPrimaryBridge

/-!
Explicit chain maps and homotopies for P=[Z^2 --3J--> Z^2] and its
shifted dual. These are integral algebra, not a mechanization of Galois
cohomology or the arithmetic Nekovar--Flach comparison.
-/
namespace SixBirdsBSD.Closure.CTDerivedTransport

open SixBirdsBSD.Apparatus.FinitePresentation
open OddPrimaryBridge LocalUnitSupport

abbrev Matrix2 := (Int × Int) × (Int × Int)

def compose (a b : Matrix2) : Matrix2 :=
  ((a.1.1*b.1.1+a.1.2*b.2.1, a.1.1*b.1.2+a.1.2*b.2.2),
   (a.2.1*b.1.1+a.2.2*b.2.1, a.2.1*b.1.2+a.2.2*b.2.2))

def subtract (a b : Matrix2) : Matrix2 :=
  ((a.1.1-b.1.1,a.1.2-b.1.2),(a.2.1-b.2.1,a.2.2-b.2.2))

def scale (u : Int) (a : Matrix2) : Matrix2 :=
  ((u*a.1.1,u*a.1.2),(u*a.2.1,u*a.2.2))

def differential : Matrix2 := ((0,3),(-3,0))
def dualDifferential : Matrix2 := ((0,-3),(3,0))

/-- J B J is the forced degree-one component when B is in degree two. -/
def dualSource (b : Matrix2) : Matrix2 := ((-b.2.2,b.2.1),(b.1.2,-b.1.1))

theorem explicitChainMap (b : Matrix2) :
    compose b differential = compose dualDifferential (dualSource b) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp [compose, differential, dualDifferential, dualSource] <;> omega

/-- No extra degree-one choice survives the chain-map equation. -/
theorem sourceForcedByChainLaw (a b : Matrix2)
    (h : compose b differential = compose dualDifferential a) : a = dualSource b := by
  have h11 := congrArg (fun m : Matrix2 => m.1.1) h
  have h12 := congrArg (fun m : Matrix2 => m.1.2) h
  have h21 := congrArg (fun m : Matrix2 => m.2.1) h
  have h22 := congrArg (fun m : Matrix2 => m.2.2) h
  simp [compose, differential, dualDifferential] at h11 h12 h21 h22
  apply Prod.ext <;> apply Prod.ext <;> simp [dualSource] <;> omega

def homotopy (k : Matrix2) : Matrix2 := ((k.2.1,k.2.2),(-k.1.1,-k.1.2))

/-- If two target matrices differ by 3K, the displayed H=JK is an
actual chain homotopy. Thus equal cokernel maps have equal derived maps. -/
theorem sameCohomologyHomotopy (b c k : Matrix2)
    (h : subtract b c = scale 3 k) :
    subtract (dualSource b) (dualSource c) = compose (homotopy k) differential ∧
    subtract b c = compose dualDifferential (homotopy k) := by
  have h11 := congrArg (fun m : Matrix2 => m.1.1) h
  have h12 := congrArg (fun m : Matrix2 => m.1.2) h
  have h21 := congrArg (fun m : Matrix2 => m.2.1) h
  have h22 := congrArg (fun m : Matrix2 => m.2.2) h
  simp [subtract, scale] at h11 h12 h21 h22
  constructor <;> apply Prod.ext <;> apply Prod.ext <;>
    simp [subtract, dualSource, compose, homotopy, differential, dualDifferential] <;> omega

def normalizationSource (u : Int) : Matrix2 := ((1,0),(0,u))
def normalizationTarget (u : Int) : Matrix2 := ((u,0),(0,1))
def cupSource (u : Int) : Matrix2 := ((u,0),(0,u))
def cupTarget (u : Int) : Matrix2 := ((-u,0),(0,-u))
def determinant (a : Matrix2) : Int := a.1.1*a.2.2-a.1.2*a.2.1

theorem normalizationIsChainMap (u : Int) :
    compose (normalizationTarget u) differential =
      compose differential (normalizationSource u) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp [compose, normalizationTarget, normalizationSource, differential] <;> omega

theorem normalizationDeterminantsAgree (u : Int) :
    determinant (normalizationSource u) = u ∧
    determinant (normalizationTarget u) = u := by
  simp [determinant, normalizationSource, normalizationTarget]

/-- The two degree components of the pulled-back standard duality. -/
theorem normalizationPullsBackDuality (u : Int) :
    compose (normalizationTarget u) (normalizationSource u) = cupSource u ∧
    scale (-1) (compose (normalizationSource u) (normalizationTarget u)) = cupTarget u := by
  constructor <;> apply Prod.ext <;> apply Prod.ext <;>
    simp [compose, scale, normalizationSource, normalizationTarget, cupSource, cupTarget]

theorem cupIsChainMap (u : Int) :
    compose (cupTarget u) differential = compose dualDifferential (cupSource u) := by
  simpa [cupTarget, dualSource, cupSource] using explicitChainMap (cupTarget u)

def normalizeIntegerCoordinates (u : Int) (x : IntegerPlane) : IntegerPlane :=
  (u*x.1,x.2)

/-- The same chain normalization returns the coefficient of the linking
form, not just the unpaired cokernel. -/
theorem normalizationLinkingReturn (u : Int) (x y : IntegerPlane) :
    linkingLift 3 (normalizeIntegerCoordinates u x) (normalizeIntegerCoordinates u y) =
      (u : Rat) * linkingLift 3 x y := by
  simp only [linkingLiftFormula, normalizeIntegerCoordinates,
    Rat.intCast_sub, Rat.intCast_mul, Rat.div_def]
  grind

/-- The split multiplicative criterion has an explicit square witness;
its invariant-line Frobenius minus one is a three-adic unit. -/
theorem splitBadPrimeInputs :
    ((295 : Int)^2 + c6 curve1913b1) % 1913 = 0 ∧
    (1913-1 : Nat) % 3 = 1 ∧
    (∀ x : Fin 3, (1913-1)*x = x) := by decide +kernel

/-- The singular point and its two distinct rational tangent slopes
also establish splitness directly from the given Weierstrass equation. -/
theorem splitNodeAndTangents :
    onAffineEquation curve1913b1 1913 (485,714) ∧
    (714-3*485^2-2*485+34 : Int) % 1913 = 0 ∧
    (2*714+485 : Int) % 1913 = 0 ∧
    (346+1566 : Fin 1913) = -1 ∧
    (346*1566 : Fin 1913) = -(3*485+1) ∧
    (346 : Fin 1913) ≠ 1566 := by decide +kernel

end SixBirdsBSD.Closure.CTDerivedTransport
