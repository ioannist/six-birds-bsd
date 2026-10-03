import SixBirdsBSD.Closure.GlobalTameProduct

/-!
Canonical quotient comparison for a prime-to-level finite-index subgroup.
The actual E(Q_p)/E_0(Q_p) instantiation is written mathematics, using the
independently computed component groups. No cohomology or source comparison
conclusion is included in these ordinary subgroup and Bezout hypotheses.
-/
namespace SixBirdsBSD.Closure.KummerComponentErasure

open Lean.Grind

structure AdditiveSubgroup (A : Type) [IntModule A] where
  mem : A → Prop
  zero_mem : mem 0
  add_mem : ∀ a b, mem a → mem b → mem (a+b)
  smul_mem : ∀ k : Int, ∀ a, mem a → mem (k • a)

def ModRelation {A : Type} [IntModule A] (m : Int) (a b : A) : Prop :=
  ∃ x, a-b=m • x

def RestrictedRelation {A : Type} [IntModule A]
    (H : AdditiveSubgroup A) (m : Int) (a b : A) : Prop :=
  ∃ x, H.mem x ∧ a-b=m • x

private theorem subgroupSub {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (a b : A) (ha : H.mem a) (hb : H.mem b) : H.mem (a-b) := by
  have h := H.add_mem a ((-1 : Int) • b) ha (H.smul_mem (-1) b hb)
  have heq : a+(-1 : Int) • b=a-b := by
    rw [IntModule.neg_zsmul,IntModule.one_zsmul,AddCommGroup.sub_eq_add_neg]
  rw [heq] at h
  exact h

/-- An explicit representative in H for every ambient quotient class. -/
theorem quotientRepresentative {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (c m u v : Int) (hbez : c*u+m*v=1)
    (hc : ∀ a, H.mem (c • a)) (a : A) :
    H.mem (c • (u • a)) ∧ ModRelation m (c • (u • a)) a := by
  refine ⟨hc _, -v • a, ?_⟩
  calc
    c • (u • a)-a = (c*u-1) • a := by
      rw [IntModule.sub_zsmul,IntModule.mul_zsmul,IntModule.one_zsmul]
    _ = (m*(-v)) • a := by congr 1; grind
    _ = m • (-v • a) := IntModule.mul_zsmul _ _ _

/-- Divisibility of a quotient class cannot gain a spurious kernel when
the quotient A/H is killed by c and c is coprime to the level m. -/
theorem multipleMembershipReflects {A : Type} [IntModule A]
    (H : AdditiveSubgroup A) (c m u v : Int) (hbez : c*u+m*v=1)
    (hc : ∀ a, H.mem (c • a)) (a : A) (ha : H.mem (m • a)) : H.mem a := by
  have hb := H.add_mem _ _ (hc (u • a)) (H.smul_mem v (m • a) ha)
  have heq : c • (u • a)+v • (m • a)=a := by
    rw [← IntModule.mul_zsmul,← IntModule.mul_zsmul,← IntModule.add_zsmul]
    have hcoef : c*u+v*m=1 := by grind
    rw [hcoef,IntModule.one_zsmul]
  rw [heq] at hb
  exact hb

theorem inclusionReflectsModRelation {A : Type} [IntModule A]
    (H : AdditiveSubgroup A) (c m u v : Int) (hbez : c*u+m*v=1)
    (hc : ∀ a, H.mem (c • a)) (a b : A) (ha : H.mem a) (hb : H.mem b) :
    ModRelation m a b ↔ RestrictedRelation H m a b := by
  constructor
  · rintro ⟨x,hx⟩
    have hmx : H.mem (m • x) := hx ▸ subgroupSub H a b ha hb
    exact ⟨x,multipleMembershipReflects H c m u v hbez hc x hmx,hx⟩
  · rintro ⟨x,_,hx⟩
    exact ⟨x,hx⟩

private theorem modRefl {A : Type} [IntModule A] (m : Int) (a : A) :
    ModRelation m a a := by
  refine ⟨0, ?_⟩
  rw [IntModule.zsmul_zero]
  grind

private theorem modSymm {A : Type} [IntModule A] (m : Int) (a b : A)
    (h : ModRelation m a b) : ModRelation m b a := by
  obtain ⟨x,hx⟩ := h
  refine ⟨-x, ?_⟩
  rw [IntModule.zsmul_neg]
  grind

private theorem modTrans {A : Type} [IntModule A] (m : Int) (a b d : A)
    (h : ModRelation m a b) (h' : ModRelation m b d) : ModRelation m a d := by
  obtain ⟨x,hx⟩ := h
  obtain ⟨y,hy⟩ := h'
  refine ⟨x+y, ?_⟩
  rw [IntModule.zsmul_add]
  grind

def ambientSetoid (A : Type) [IntModule A] (m : Int) : Setoid A where
  r := ModRelation m
  iseqv := ⟨modRefl m,fun {_ _} => modSymm m _ _,fun {_ _ _} => modTrans m _ _ _⟩

def restrictedSetoid {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (m : Int) : Setoid {a : A // H.mem a} where
  r := fun a b => RestrictedRelation H m a.val b.val
  iseqv := by
    constructor
    · intro a
      refine ⟨0,H.zero_mem,?_⟩
      rw [IntModule.zsmul_zero]
      grind
    · intro a b h
      obtain ⟨x,hmem,hx⟩ := h
      refine ⟨(-1 : Int) • x,H.smul_mem (-1) x hmem,?_⟩
      rw [IntModule.neg_zsmul,IntModule.one_zsmul,IntModule.zsmul_neg]
      grind
    · intro a b d h h'
      obtain ⟨x,hmem,hx⟩ := h
      obtain ⟨y,hmem',hy⟩ := h'
      refine ⟨x+y,H.add_mem x y hmem hmem',?_⟩
      rw [IntModule.zsmul_add]
      grind

abbrev AmbientQuotient (A : Type) [IntModule A] (m : Int) :=
  Quotient (ambientSetoid A m)
abbrev RestrictedQuotient {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (m : Int) := Quotient (restrictedSetoid H m)

/-- The forward map is induced by inclusion, with no Bezout choices. -/
def quotientInclusion {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (m : Int) : RestrictedQuotient H m → AmbientQuotient A m :=
  Quotient.lift (fun a => Quotient.mk (ambientSetoid A m) a.val) (by
    intro a b h
    obtain ⟨x,_,hx⟩ := h
    exact Quotient.sound ⟨x,hx⟩)

theorem quotientInclusionInjective {A : Type} [IntModule A]
    (H : AdditiveSubgroup A) (c m u v : Int) (hbez : c*u+m*v=1)
    (hc : ∀ a, H.mem (c • a)) (x y : RestrictedQuotient H m)
    (h : quotientInclusion H m x=quotientInclusion H m y) : x=y := by
  induction x,y using Quotient.inductionOn₂ with
  | _ a b =>
    exact Quotient.sound ((inclusionReflectsModRelation H c m u v hbez hc
      a.val b.val a.property b.property).mp (Quotient.exact h))

/-- Explicit inverse: [a] maps to [c*u*a], derived from the subgroup laws. -/
def quotientInverse {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (c m u v : Int) (hbez : c*u+m*v=1) (hc : ∀ a, H.mem (c • a)) :
    AmbientQuotient A m → RestrictedQuotient H m :=
  Quotient.lift (fun a => Quotient.mk (restrictedSetoid H m)
    ⟨c • (u • a),hc _⟩) (by
      intro a b h
      apply Quotient.sound
      apply (inclusionReflectsModRelation H c m u v hbez hc _ _ (hc _) (hc _)).mp
      obtain ⟨x,hx⟩ := h
      refine ⟨c • (u • x),?_⟩
      rw [← IntModule.zsmul_sub,← IntModule.zsmul_sub,hx]
      simp only [← IntModule.mul_zsmul]
      congr 1
      grind)

theorem quotientRightInverse {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (c m u v : Int) (hbez : c*u+m*v=1) (hc : ∀ a, H.mem (c • a))
    (x : AmbientQuotient A m) :
    quotientInclusion H m (quotientInverse H c m u v hbez hc x)=x := by
  induction x using Quotient.inductionOn with
  | _ a => exact Quotient.sound (quotientRepresentative H c m u v hbez hc a).2

theorem quotientLeftInverse {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (c m u v : Int) (hbez : c*u+m*v=1) (hc : ∀ a, H.mem (c • a))
    (x : RestrictedQuotient H m) :
    quotientInverse H c m u v hbez hc (quotientInclusion H m x)=x := by
  apply quotientInclusionInjective H c m u v hbez hc
  exact quotientRightInverse H c m u v hbez hc _

/-- Equality of the ACTUAL subsets in any target of a map factoring through
the quotient. The Kummer boundary has this property by its defining exact
sequence, not by a component-comparison certificate. -/
theorem kummerImagesEqual {A B : Type} [IntModule A] (H : AdditiveSubgroup A)
    (c m u v : Int) (hbez : c*u+m*v=1) (hc : ∀ a, H.mem (c • a))
    (kummer : A → B)
    (hrespect : ∀ a b, ModRelation m a b → kummer a=kummer b) (y : B) :
    (∃ a, kummer a=y) ↔ ∃ a, H.mem a ∧ kummer a=y := by
  constructor
  · rintro ⟨a,ha⟩
    have hr := quotientRepresentative H c m u v hbez hc a
    exact ⟨c • (u • a),hr.1,(hrespect _ _ hr.2).trans ha⟩
  · rintro ⟨a,_,ha⟩
    exact ⟨a,ha⟩

/-- This elementary modulus equation is the all-level input for c=2.
It applies at every odd coefficient prime, including all powers. -/
theorem oddLevelBezout (m : Int) (hodd : m % 2=1) :
    2*((m+1)/2)+m*(-1)=1 := by omega

theorem fourLevelBezout (m : Int) (hodd : m % 2=1) :
    4*((m+1)/2)^2+m*(-(m+2))=1 := by
  have h := oddLevelBezout m hodd
  grind

/-- Normalizing a prime-to-level degree gives a genuine inverse on a
module killed by the coefficient level. This concerns degree, not c_p. -/
theorem scalarDegreeInverse {A : Type} [IntModule A] (c m u v : Int)
    (hbez : c*u+m*v=1) (hkill : ∀ a : A, m • a=0) (a : A) :
    u • (c • a)=a := by
  have hcoef : u*c=1-m*v := by grind
  rw [← IntModule.mul_zsmul,hcoef,IntModule.sub_zsmul,IntModule.one_zsmul]
  have hzero : (m*v) • a=0 := by
    have hcomm : m*v=v*m := by grind
    rw [hcomm,IntModule.mul_zsmul,hkill,IntModule.zsmul_zero]
  rw [hzero]
  grind

/-- The standard Cor-Res degree identity yields a normalized LEFT inverse.
No isomorphism of the entire cover-side cohomology is asserted. -/
theorem normalizedCorestrictionLeftInverse {A B : Type} [IntModule A]
    (c m u v : Int) (hbez : c*u+m*v=1) (hkill : ∀ a : A, m • a=0)
    (res : A → B) (cor : B → A) (hdegree : ∀ a, cor (res a)=c • a) :
    ∀ a, u • (cor (res a))=a := by
  intro a
  rw [hdegree]
  exact scalarDegreeInverse c m u v hbez hkill a

theorem oddPrimePowerLevel (p n : Nat) (hodd : p % 2=1) :
    (p^n : Int) % 2=1 := by
  have hn : p^n % 2=1 := by
    induction n with
    | zero => simp
    | succ n ih => simp [Nat.pow_succ,Nat.mul_mod,ih,hodd]
  exact_mod_cast hn

private theorem powerRelationReduces {A : Type} [IntModule A] (p n : Nat)
    (a b : A) (h : ModRelation (p^(n+1) : Int) a b) :
    ModRelation (p^n : Int) a b := by
  obtain ⟨x,hx⟩ := h
  refine ⟨(p : Int) • x,?_⟩
  rw [← IntModule.mul_zsmul,← Int.pow_succ]
  exact hx

def ambientReduction (A : Type) [IntModule A] (p n : Nat) :
    AmbientQuotient A (p^(n+1)) → AmbientQuotient A (p^n) :=
  Quotient.lift (fun a => Quotient.mk (ambientSetoid A (p^n)) a)
    (fun a b h => Quotient.sound (powerRelationReduces p n a b h))

def restrictedReduction {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (p n : Nat) : RestrictedQuotient H (p^(n+1)) → RestrictedQuotient H (p^n) :=
  Quotient.lift (fun a => Quotient.mk (restrictedSetoid H (p^n)) a) (by
    intro a b h
    obtain ⟨x,hmem,hx⟩ := h
    apply Quotient.sound
    refine ⟨(p : Int) • x,H.smul_mem p x hmem,?_⟩
    rw [← IntModule.mul_zsmul,← Int.pow_succ]
    exact hx)

theorem quotientInclusionReduction {A : Type} [IntModule A]
    (H : AdditiveSubgroup A) (p n : Nat) (x : RestrictedQuotient H (p^(n+1))) :
    ambientReduction A p n (quotientInclusion H (p^(n+1)) x)=
      quotientInclusion H (p^n) (restrictedReduction H p n x) := by
  induction x using Quotient.inductionOn with
  | _ a => rfl

def twoLevelInverse {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (htwo : ∀ a, H.mem ((2 : Int) • a)) (p : Nat) (hodd : p % 2=1) (n : Nat) :
    AmbientQuotient A (p^n) → RestrictedQuotient H (p^n) :=
  quotientInverse H 2 (p^n) (((p^n : Int)+1)/2) (-1)
    (oddLevelBezout _ (oddPrimePowerLevel p n hodd)) htwo

theorem twoLevelRightInverse {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (htwo : ∀ a, H.mem ((2 : Int) • a)) (p : Nat) (hodd : p % 2=1) (n : Nat)
    (x : AmbientQuotient A (p^n)) :
    quotientInclusion H (p^n) (twoLevelInverse H htwo p hodd n x)=x :=
  quotientRightInverse H 2 (p^n) (((p^n : Int)+1)/2) (-1)
    (oddLevelBezout _ (oddPrimePowerLevel p n hodd)) htwo x

theorem twoLevelLeftInverse {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (htwo : ∀ a, H.mem ((2 : Int) • a)) (p : Nat) (hodd : p % 2=1) (n : Nat)
    (x : RestrictedQuotient H (p^n)) :
    twoLevelInverse H htwo p hodd n (quotientInclusion H (p^n) x)=x :=
  quotientLeftInverse H 2 (p^n) (((p^n : Int)+1)/2) (-1)
    (oddLevelBezout _ (oddPrimePowerLevel p n hodd)) htwo x

/-- Compatibility of the explicit inverses is proved by the canonical
inclusion's injectivity, not assumed as a completed comparison field. -/
theorem twoLevelInverseReduction {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (htwo : ∀ a, H.mem ((2 : Int) • a)) (p : Nat) (hodd : p % 2=1) (n : Nat)
    (x : AmbientQuotient A (p^(n+1))) :
    restrictedReduction H p n (twoLevelInverse H htwo p hodd (n+1) x)=
      twoLevelInverse H htwo p hodd n (ambientReduction A p n x) := by
  apply quotientInclusionInjective H 2 (p^n) (((p^n : Int)+1)/2) (-1)
    (oddLevelBezout _ (oddPrimePowerLevel p n hodd)) htwo
  rw [← quotientInclusionReduction,twoLevelRightInverse,twoLevelRightInverse]

/-- Actual compatible sequences of quotient classes, including the trivial
level n=0. No compactness or Mittag-Leffler premise is needed for these maps. -/
abbrev AmbientCompletion (A : Type) [IntModule A] (p : Nat) :=
  {x : (n : Nat) → AmbientQuotient A (p^n) //
    ∀ n, ambientReduction A p n (x (n+1))=x n}
abbrev RestrictedCompletion {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (p : Nat) := {x : (n : Nat) → RestrictedQuotient H (p^n) //
    ∀ n, restrictedReduction H p n (x (n+1))=x n}

def completionInclusion {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (p : Nat) (x : RestrictedCompletion H p) : AmbientCompletion A p :=
  ⟨fun n => quotientInclusion H (p^n) (x.val n),by
    intro n
    rw [quotientInclusionReduction,x.property n]⟩

def completionInverse {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (htwo : ∀ a, H.mem ((2 : Int) • a)) (p : Nat) (hodd : p % 2=1)
    (x : AmbientCompletion A p) : RestrictedCompletion H p :=
  ⟨fun n => twoLevelInverse H htwo p hodd n (x.val n),by
    intro n
    rw [twoLevelInverseReduction,x.property n]⟩

theorem completedComparison {A : Type} [IntModule A] (H : AdditiveSubgroup A)
    (htwo : ∀ a, H.mem ((2 : Int) • a)) (p : Nat) (hodd : p % 2=1) :
    (∀ x, completionInclusion H p (completionInverse H htwo p hodd x)=x) ∧
    (∀ x, completionInverse H htwo p hodd (completionInclusion H p x)=x) := by
  constructor
  · intro x
    apply Subtype.ext
    funext n
    exact twoLevelRightInverse H htwo p hodd n (x.val n)
  · intro x
    apply Subtype.ext
    funext n
    exact twoLevelLeftInverse H htwo p hodd n (x.val n)

theorem twoComponentKummerImagesEqual {A B : Type} [IntModule A]
    (H : AdditiveSubgroup A) (htwo : ∀ a, H.mem ((2 : Int) • a))
    (p n : Nat) (hodd : p % 2=1) (kummer : A → B)
    (hrespect : ∀ a b, ModRelation (p^n : Int) a b → kummer a=kummer b) (y : B) :
    (∃ a, kummer a=y) ↔ ∃ a, H.mem a ∧ kummer a=y :=
  kummerImagesEqual H 2 (p^n) (((p^n : Int)+1)/2) (-1)
    (oddLevelBezout _ (oddPrimePowerLevel p n hodd)) htwo kummer hrespect y

def fullSubgroup (A : Type) [IntModule A] : AdditiveSubgroup A where
  mem := fun _ => True
  zero_mem := True.intro
  add_mem := fun _ _ _ _ => True.intro
  smul_mem := fun _ _ _ => True.intro

/-- The whole family of embedded image subsets is retained, not their
dimensions or a finite sample of coefficient levels. -/
def kummerImageFamily {A : Type} [IntModule A] {B : Nat → Type}
    (kummer : (n : Nat) → A → B n) (H : AdditiveSubgroup A) :
    (n : Nat) → B n → Prop := fun n y => ∃ a, H.mem a ∧ kummer n a=y

theorem entireKummerImageFamilyEqual {A : Type} [IntModule A] {B : Nat → Type}
    (H : AdditiveSubgroup A) (htwo : ∀ a, H.mem ((2 : Int) • a))
    (p : Nat) (hodd : p % 2=1) (kummer : (n : Nat) → A → B n)
    (hrespect : ∀ n a b, ModRelation (p^n : Int) a b → kummer n a=kummer n b) :
    kummerImageFamily kummer H=kummerImageFamily kummer (fullSubgroup A) := by
  funext n y
  apply propext
  change (∃ a, H.mem a ∧ kummer n a=y) ↔ ∃ a, True ∧ kummer n a=y
  constructor
  · rintro ⟨a,_,ha⟩
    exact ⟨a,True.intro,ha⟩
  · rintro ⟨a,_,ha⟩
    exact (twoComponentKummerImagesEqual H htwo p n hodd (kummer n)
      (hrespect n) y).mp ⟨a,ha⟩

/-- A scoped non-descent theorem for marked subgroups, not an ablation of
the named BSD sources or recovery of canonical E_0 from the curve equation. -/
theorem noMarkedSubgroupReadout {A : Type} [IntModule A] {B : Nat → Type}
    (H : AdditiveSubgroup A) (htwo : ∀ a, H.mem ((2 : Int) • a))
    (hproper : ∃ a, ¬ H.mem a) (p : Nat) (hodd : p % 2=1)
    (kummer : (n : Nat) → A → B n)
    (hrespect : ∀ n a b, ModRelation (p^n : Int) a b → kummer n a=kummer n b) :
    ¬ ∃ readout : ((n : Nat) → B n → Prop) → Prop,
      ∀ G : AdditiveSubgroup A, (∀ a, G.mem ((2 : Int) • a)) →
        (readout (kummerImageFamily kummer G) ↔ ∀ a, G.mem a) := by
  rintro ⟨readout,hr⟩
  have heq := entireKummerImageFamilyEqual H htwo p hodd kummer hrespect
  have hfull := (hr (fullSubgroup A) (fun _ => True.intro)).mpr
    (fun _ => True.intro)
  rw [← heq] at hfull
  obtain ⟨a,ha⟩ := hproper
  exact ha ((hr H htwo).mp hfull a)

/-- A prime-two control: for H=2Z, ambient divisibility modulo two differs
from divisibility inside H. Thus the prime-to-index hypothesis matters. -/
def evenIntegers : AdditiveSubgroup Int where
  mem a := 2 ∣ a
  zero_mem := ⟨0,by decide⟩
  add_mem a b ha hb := Int.dvd_add ha hb
  smul_mem k a ha := by
    change 2 ∣ k*a
    obtain ⟨t,ht⟩ := ha
    refine ⟨k*t,?_⟩
    rw [ht]
    grind

theorem coefficientTwoControl :
    evenIntegers.mem 2 ∧ evenIntegers.mem 0 ∧ ModRelation 2 (2 : Int) 0 ∧
    ¬ RestrictedRelation evenIntegers 2 (2 : Int) 0 := by
  refine ⟨⟨1,by decide⟩,evenIntegers.zero_mem,⟨1,by decide⟩,?_⟩
  rintro ⟨x,hx,heq⟩
  change 2 ∣ x at hx
  change 2-0=2*x at heq
  have hx1 : x=1 := by omega
  rw [hx1] at hx
  exact (by decide : ¬ (2 : Int) ∣ 1) hx

open SixBirdsBSD.Apparatus.FinitePresentation (reduceResidue reduceResidueEqIff)

theorem evenIntegersKilledQuotient :
    (∀ a : Int, evenIntegers.mem ((2 : Int) • a)) ∧ ¬ evenIntegers.mem 1 := by
  constructor
  · intro a
    exact ⟨a,rfl⟩
  · exact (by decide : ¬ (2 : Int) ∣ 1)

/-- At the coefficient prime dividing the index, even the embedded image
subsets differ. The map is actual reduction modulo two. -/
theorem coefficientTwoImageControl :
    (∀ a b : Int, ModRelation 2 a b → reduceResidue 2 a=reduceResidue 2 b) ∧
    (∃ a : Int, reduceResidue 2 a=1) ∧
    ¬ (∃ a : Int, evenIntegers.mem a ∧ reduceResidue 2 a=1) := by
  refine ⟨?_,⟨1,by decide⟩,?_⟩
  · intro a b h
    obtain ⟨x,hx⟩ := h
    exact (reduceResidueEqIff 2 a b).mpr ⟨x,hx⟩
  · rintro ⟨a,ha,heq⟩
    change 2 ∣ a at ha
    have hz := (reduceResidueEqIff 2 a 0).mpr (by simpa using ha)
    have hne : (0 : Fin 2) ≠ 1 := by decide
    have hzero : reduceResidue 2 (0 : Int)=0 := by decide
    exact hne (hzero.symm.trans (hz.symm.trans heq))

/-- Equation-derived point and doubling inputs for the two actual type-III
places. Interpreting singular/nonsingular reduction uses the written local
group definition; no curve ID or subgroup-index answer is assigned here. -/
theorem actualMarkedPointInputs :
    (35 : Int)^2=1225 ∧ 2*35*11=2*385 ∧
    (1611 : Int)^2=121^3+385*121*16+1225*64 ∧
    (385 : Int)%5=0 ∧ (1225 : Int)%5=0 ∧ (35 : Int)%5=0 ∧
    (385 : Int)%7=0 ∧ (1225 : Int)%7=0 ∧ (35 : Int)%7=0 ∧
    (121 : Int)%5=1 ∧ (1611 : Int)%5=1 ∧
    (121 : Int)%7=2 ∧ (1611 : Int)%7=1 := by decide +kernel

end SixBirdsBSD.Closure.KummerComponentErasure
