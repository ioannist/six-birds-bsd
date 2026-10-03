import SixBirdsBSD.Closure.StarkCoreVertices

/-!
The full inverse-limit coefficient carrier, not a bounded sample of residues.
It is the usual compatible-residue construction of Z_3. Arithmetic Stark
freeness and coefficient comparison remain external, as recorded in
formalization/stark_inverse_limit_construction.md.
-/
namespace SixBirdsBSD.Closure.StarkInverseLimit

def modulus (n : Nat) : Nat := 3^(n+1)

theorem modulus_succ (n : Nat) : modulus (n+1) = modulus n * 3 := by
  simp [modulus, Nat.pow_succ]

theorem modulus_large (n : Nat) : 2 < modulus n := by
  induction n with
  | zero => decide
  | succ n ih => rw [modulus_succ]; omega

/-- All positive coefficient levels, with actual reduction compatibility. -/
structure ThreeAdic where
  val : Nat → Nat
  bound : ∀ n, val n < modulus n
  compatible : ∀ n, val (n+1) % modulus n = val n

theorem ext {x y : ThreeAdic} (h : ∀ n, x.val n = y.val n) : x = y := by
  cases x
  cases y
  congr
  funext n
  exact h n

def fromNat (a : Nat) : ThreeAdic where
  val n := a % modulus n
  bound n := Nat.mod_lt _ (by have := modulus_large n; omega)
  compatible n := by rw [modulus_succ, Nat.mod_mul_right_mod]

def mul (x y : ThreeAdic) : ThreeAdic where
  val n := (x.val n * y.val n) % modulus n
  bound n := Nat.mod_lt _ (by have := modulus_large n; omega)
  compatible n := by
    rw [modulus_succ, Nat.mod_mul_right_mod, Nat.mul_mod,
      x.compatible, y.compatible]

theorem mul_comm (x y : ThreeAdic) : mul x y = mul y x := by
  apply ext
  intro n
  simp [mul, Nat.mul_comm]

theorem mul_assoc (x y z : ThreeAdic) : mul (mul x y) z = mul x (mul y z) := by
  apply ext
  intro n
  simp only [mul]
  rw [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

theorem one_mul (x : ThreeAdic) : mul (fromNat 1) x = x := by
  apply ext
  intro n
  simp only [mul, fromNat]
  rw [Nat.mod_mul_mod, Nat.one_mul, Nat.mod_eq_of_lt (x.bound n)]

def inverseTwoValue : Nat → Nat
  | 0 => 2
  | n+1 => inverseTwoValue n + modulus n

theorem inverseTwoIdentity (n : Nat) : 2 * inverseTwoValue n = modulus n + 1 := by
  induction n with
  | zero => decide
  | succ n ih => rw [inverseTwoValue, modulus_succ]; omega

def inverseTwo : ThreeAdic where
  val := inverseTwoValue
  bound n := by have := inverseTwoIdentity n; have := modulus_large n; omega
  compatible n := by
    rw [inverseTwoValue, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by have := inverseTwoIdentity n; have := modulus_large n; omega)]

/-- A single compatible inverse, rather than unrelated finite inverses. -/
theorem twoIsUnit : mul (fromNat 2) inverseTwo = fromNat 1 := by
  apply ext
  intro n
  change ((2 % modulus n) * inverseTwoValue n) % modulus n = 1 % modulus n
  rw [Nat.mod_mul_mod, inverseTwoIdentity]
  simp

def principalImage (a y : ThreeAdic) : Prop := ∃ x, mul a x = y

/-- Equality of generated ideals on the completed coefficient carrier. -/
theorem unitScalingPreservesPrincipalImages (a y : ThreeAdic) :
    principalImage a y ↔ principalImage (mul (fromNat 2) a) y := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨mul inverseTwo x, ?_⟩
    calc
      mul (mul (fromNat 2) a) (mul inverseTwo x) =
          mul (mul (fromNat 2) inverseTwo) (mul a x) := by
        rw [mul_assoc, ← mul_assoc a, mul_comm a inverseTwo, mul_assoc,
          ← mul_assoc]
      _ = y := by rw [twoIsUnit, one_mul, hx]
  · rintro ⟨x, hx⟩
    refine ⟨mul (fromNat 2) x, ?_⟩
    rw [← mul_assoc, mul_comm a, mul_assoc]
    simpa only [mul_assoc] using hx

def HasSquareRoot (u : ThreeAdic) : Prop := ∃ v, mul v v = u

theorem oneHasSquareRoot : HasSquareRoot (fromNat 1) := by
  exact ⟨fromNat 1, one_mul _⟩

/-- A necessary equation at the first coordinate refutes a root in the
entire inverse limit; no compactness or finite-search inference is used. -/
theorem twoHasNoSquareRoot : ¬ HasSquareRoot (fromNat 2) := by
  rintro ⟨v, hv⟩
  have h := congrArg (fun x : ThreeAdic => x.val 0) hv
  have hb := v.bound 0
  change (v.val 0 * v.val 0) % 3 = 2 at h
  change v.val 0 < 3 at hb
  have hf : ∀ a : Fin 3, (a.val*a.val) % 3 ≠ 2 := by decide +kernel
  exact hf ⟨v.val 0, hb⟩ h

/-- No readout of the full principal ideal can decide prescribed-root
existence. The witnesses are compatible coefficients one and two. -/
theorem noSquareRootReadoutFromIdeal :
    ¬ ∃ readout : (ThreeAdic → Prop) → Prop,
      ∀ u, readout (principalImage u) ↔ HasSquareRoot u := by
  rintro ⟨readout, hr⟩
  have hi : principalImage (fromNat 1) = principalImage (fromNat 2) := by
    funext y
    apply propext
    simpa [mul_comm (fromNat 2) (fromNat 1), one_mul] using
      unitScalingPreservesPrincipalImages (fromNat 1) y
  have h := (hr (fromNat 1)).mpr oneHasSquareRoot
  rw [hi] at h
  exact twoHasNoSquareRoot ((hr (fromNat 2)).mp h)

/-- An arbitrary family of component ideals, including every Fitting
level, still loses the same unit. No truncation of the family is used. -/
def idealFamily {I : Type} (g : I → ThreeAdic) (u : ThreeAdic) : I → ThreeAdic → Prop :=
  fun i => principalImage (mul u (g i))

theorem sameEntireIdealFamily {I : Type} (g : I → ThreeAdic) :
    idealFamily g (fromNat 1) = idealFamily g (fromNat 2) := by
  funext i y
  apply propext
  simp only [idealFamily, one_mul]
  exact unitScalingPreservesPrincipalImages (g i) y

theorem noSquareRootReadoutFromIdealFamily {I : Type} (g : I → ThreeAdic) :
    ¬ ∃ readout : (I → ThreeAdic → Prop) → Prop,
      ∀ u, readout (idealFamily g u) ↔ HasSquareRoot u := by
  rintro ⟨readout, hr⟩
  have h := (hr (fromNat 1)).mpr oneHasSquareRoot
  rw [sameEntireIdealFamily g] at h
  exact twoHasNoSquareRoot ((hr (fromNat 2)).mp h)

end SixBirdsBSD.Closure.StarkInverseLimit
