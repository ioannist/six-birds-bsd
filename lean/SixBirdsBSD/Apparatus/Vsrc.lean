/-!
`SixBirdsBSD.Apparatus.Vsrc` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § Vsrc.
-/

namespace SixBirdsBSD.Apparatus.Vsrc

universe u

structure Vsrc2 where
  c0 : Int
  c1 : Int
  c2 : Int
  c12 : Int
  deriving DecidableEq

def vsrc2Zero : Vsrc2 := ⟨0, 0, 0, 0⟩
def vsrc2One : Vsrc2 := ⟨1, 0, 0, 0⟩
def vsrc2J1 : Vsrc2 := ⟨0, 1, 0, 0⟩
def vsrc2J2 : Vsrc2 := ⟨0, 0, 1, 0⟩
def vsrc2J12 : Vsrc2 := ⟨0, 0, 0, 1⟩

def vsrc2Neg (x : Vsrc2) : Vsrc2 :=
  ⟨-x.c0, -x.c1, -x.c2, -x.c12⟩

def vsrc2Add (x y : Vsrc2) : Vsrc2 :=
  ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2, x.c12 + y.c12⟩

def vsrc2Smul (a : Int) (x : Vsrc2) : Vsrc2 :=
  ⟨a * x.c0, a * x.c1, a * x.c2, a * x.c12⟩

/-- Exterior multiplication in the explicit rank-2 basis `1,J1,J2,J12`. -/
def vsrc2Vmul (x y : Vsrc2) : Vsrc2 :=
  ⟨x.c0 * y.c0,
   x.c0 * y.c1 + x.c1 * y.c0,
   x.c0 * y.c2 + x.c2 * y.c0,
   x.c0 * y.c12 + x.c1 * y.c2 - x.c2 * y.c1 + x.c12 * y.c0⟩

theorem vsrc2OneVmul (x : Vsrc2) : vsrc2Vmul vsrc2One x = x := by
  cases x
  simp [vsrc2Vmul, vsrc2One]

theorem vsrc2VmulOne (x : Vsrc2) : vsrc2Vmul x vsrc2One = x := by
  cases x
  simp [vsrc2Vmul, vsrc2One]

/-- The displayed table is an associative multiplication, not just a set
of generator relations. -/
theorem vsrc2VmulAssoc (x y z : Vsrc2) :
    vsrc2Vmul (vsrc2Vmul x y) z = vsrc2Vmul x (vsrc2Vmul y z) := by
  cases x; cases y; cases z
  simp only [vsrc2Vmul, Vsrc2.mk.injEq]
  grind

theorem vsrc2VmulAdd (x y z : Vsrc2) :
    vsrc2Vmul x (vsrc2Add y z) = vsrc2Add (vsrc2Vmul x y) (vsrc2Vmul x z) := by
  cases x; cases y; cases z
  simp only [vsrc2Vmul, vsrc2Add, Vsrc2.mk.injEq]
  grind

theorem vsrc2AddVmul (x y z : Vsrc2) :
    vsrc2Vmul (vsrc2Add x y) z = vsrc2Add (vsrc2Vmul x z) (vsrc2Vmul y z) := by
  cases x; cases y; cases z
  simp only [vsrc2Vmul, vsrc2Add, Vsrc2.mk.injEq]
  grind

theorem vsrc2SmulVmul (a : Int) (x y : Vsrc2) :
    vsrc2Vmul (vsrc2Smul a x) y = vsrc2Smul a (vsrc2Vmul x y) := by
  cases x; cases y
  simp only [vsrc2Vmul, vsrc2Smul, Vsrc2.mk.injEq]
  grind

theorem vsrc2VmulSmul (a : Int) (x y : Vsrc2) :
    vsrc2Vmul x (vsrc2Smul a y) = vsrc2Smul a (vsrc2Vmul x y) := by
  cases x; cases y
  simp only [vsrc2Vmul, vsrc2Smul, Vsrc2.mk.injEq]
  grind

theorem vsrc2J1Sq : vsrc2Vmul vsrc2J1 vsrc2J1 = vsrc2Zero := by
  decide

theorem vsrc2J2Sq : vsrc2Vmul vsrc2J2 vsrc2J2 = vsrc2Zero := by
  decide

theorem vsrc2J1MulJ2 : vsrc2Vmul vsrc2J1 vsrc2J2 = vsrc2J12 := by
  decide

theorem vsrc2J2MulJ1 : vsrc2Vmul vsrc2J2 vsrc2J1 = vsrc2Neg vsrc2J12 := by
  decide

theorem vsrc2J1J2Anticomm : vsrc2Vmul vsrc2J1 vsrc2J2 = vsrc2Neg (vsrc2Vmul vsrc2J2 vsrc2J1) := by
  decide

def vsrc2BasisDistinct : Prop :=
    vsrc2One ≠ vsrc2J1 ∧ vsrc2One ≠ vsrc2J2 ∧ vsrc2One ≠ vsrc2J12 ∧
      vsrc2J1 ≠ vsrc2J2 ∧ vsrc2J1 ≠ vsrc2J12 ∧ vsrc2J2 ≠ vsrc2J12

theorem vsrc2BasisDistinctProof : vsrc2BasisDistinct := by
  unfold vsrc2BasisDistinct
  decide

structure VsrcRank2Algebra where
  Carrier : Type
  zero : Carrier
  one : Carrier
  J1 : Carrier
  J2 : Carrier
  J12 : Carrier
  neg : Carrier → Carrier
  add : Carrier → Carrier → Carrier
  smul : Int → Carrier → Carrier
  vmul : Carrier → Carrier → Carrier
  vmul_assoc : ∀ x y z, vmul (vmul x y) z = vmul x (vmul y z)
  vmul_add : ∀ x y z, vmul x (add y z) = add (vmul x y) (vmul x z)
  add_vmul : ∀ x y z, vmul (add x y) z = add (vmul x z) (vmul y z)
  smul_vmul : ∀ a x y, vmul (smul a x) y = smul a (vmul x y)
  vmul_smul : ∀ a x y, vmul x (smul a y) = smul a (vmul x y)

/-- Virtual source exterior algebra, instantiated by the explicit rank-2 carrier. -/
def vsrcAlgebra : VsrcRank2Algebra where
  Carrier := Vsrc2
  zero := vsrc2Zero
  one := vsrc2One
  J1 := vsrc2J1
  J2 := vsrc2J2
  J12 := vsrc2J12
  neg := vsrc2Neg
  add := vsrc2Add
  smul := vsrc2Smul
  vmul := vsrc2Vmul
  vmul_assoc := vsrc2VmulAssoc
  vmul_add := vsrc2VmulAdd
  add_vmul := vsrc2AddVmul
  smul_vmul := vsrc2SmulVmul
  vmul_smul := vsrc2VmulSmul

def vsrcDimensionSlots (r : Nat) (Scalar : Type u) : Type u :=
  Fin (2 ^ r) → Scalar

/-- Stage I: the explicit exterior relations and low-rank dimensions are consistent. -/
theorem vsrcStageIConsistency :
    (∀ x : Vsrc2, vsrc2Vmul vsrc2One x = x ∧ vsrc2Vmul x vsrc2One = x) ∧
      vsrc2Vmul vsrc2J1 vsrc2J1 = vsrc2Zero ∧
      vsrc2Vmul vsrc2J2 vsrc2J2 = vsrc2Zero ∧
      vsrc2Vmul vsrc2J1 vsrc2J2 = vsrc2J12 ∧
      vsrc2Vmul vsrc2J2 vsrc2J1 = vsrc2Neg vsrc2J12 ∧
      vsrc2Vmul vsrc2J1 vsrc2J2 = vsrc2Neg (vsrc2Vmul vsrc2J2 vsrc2J1) ∧
      vsrc2BasisDistinct ∧
      (2 ^ 0 = 1) ∧ (2 ^ 1 = 2) ∧ (2 ^ 2 = 4) := by
  constructor
  · intro x
    exact ⟨vsrc2OneVmul x, vsrc2VmulOne x⟩
  · exact ⟨vsrc2J1Sq, vsrc2J2Sq, vsrc2J1MulJ2, vsrc2J2MulJ1,
      vsrc2J1J2Anticomm, vsrc2BasisDistinctProof, by decide, by decide, by decide⟩

inductive Vsrc1Symbol where
  | one
  | J1
  deriving DecidableEq

inductive GZDescentTarget where
  | unit
  | PK
  | NTHeight
  deriving DecidableEq

def rGZ : Vsrc1Symbol → GZDescentTarget
  | Vsrc1Symbol.one => GZDescentTarget.unit
  | Vsrc1Symbol.J1 => GZDescentTarget.PK

def hVsrc : Vsrc1Symbol → Vsrc1Symbol → GZDescentTarget
  | Vsrc1Symbol.J1, Vsrc1Symbol.J1 => GZDescentTarget.NTHeight
  | _, _ => GZDescentTarget.unit

/-- Stage II recovers the GZ source/regulator side but leaves analytic-height import residual. -/
theorem vsrcStageIIGzPartial :
    let Xi_GZ : Int := 1
    rGZ Vsrc1Symbol.J1 = GZDescentTarget.PK ∧
      hVsrc Vsrc1Symbol.J1 Vsrc1Symbol.J1 = GZDescentTarget.NTHeight ∧
      Xi_GZ ≠ 0 := by
  decide

inductive Vsrc2Symbol where
  | one
  | J1
  | J2
  | J12
  deriving DecidableEq

def wedge2 : Vsrc2Symbol → Vsrc2Symbol → Vsrc2Symbol
  | Vsrc2Symbol.J1, Vsrc2Symbol.J2 => Vsrc2Symbol.J12
  | _, _ => Vsrc2Symbol.one

structure StageIIIAnalyticHeightBridge (XiMot XiSc : Int) where
  forward : XiMot = 0 → XiSc = 0

structure StageIIIExternalReverseContent (XiMot XiSc : Int) where
  reverse : XiSc = 0 → XiMot = 0

/-- Stage III is one-way under the bridge; reverse translation is explicit external content. -/
theorem vsrcStageIIITranslation (XiMot XiSc : Int)
    (bridge : StageIIIAnalyticHeightBridge XiMot XiSc) :
    wedge2 Vsrc2Symbol.J1 Vsrc2Symbol.J2 = Vsrc2Symbol.J12 ∧
      (XiMot = 0 → XiSc = 0) ∧
      (StageIIIExternalReverseContent XiMot XiSc → XiSc = 0 → XiMot = 0) := by
  constructor
  · rfl
  · constructor
    · exact bridge.forward
    · intro ext hsc
      exact ext.reverse hsc

end SixBirdsBSD.Apparatus.Vsrc
