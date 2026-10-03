import Init.Grind

/-!
`SixBirdsBSD.Apparatus.KappaNormalization` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § KappaNormalization.
-/

namespace SixBirdsBSD.Apparatus.KappaNormalization

open Lean.Grind
universe u

/-- Canonical `kappa_r` normalization is exactly cancellation of the BSD common factor. -/
theorem kappaRNormalizationEquivalence
    (Omega_E Reg_r Tam_E kappa_r sha_over_tors_sq : Int)
    (h_common : Omega_E * Reg_r * Tam_E ≠ 0) :
    let common := Omega_E * Reg_r * Tam_E
    let cascadeForm := kappa_r * common
    let standardBSDForm := sha_over_tors_sq * common
    cascadeForm = standardBSDForm ↔ kappa_r = sha_over_tors_sq := by
  dsimp only
  constructor
  · intro h
    exact Int.eq_of_mul_eq_mul_right h_common h
  · intro h
    rw [h]

/-- Native field normalization, including fractional coefficients. The
normalization is an equality of supplied factors, not an arithmetic theorem. -/
theorem kappaNormalizationOverField {R : Type u} [Field R]
    (Omega Reg Tam kappa shaOverTorsionSquared : R)
    (hCommon : Omega*Reg*Tam ≠ 0) :
    kappa*(Omega*Reg*Tam) = shaOverTorsionSquared*(Omega*Reg*Tam) ↔
      kappa=shaOverTorsionSquared := by
  grind

/-- Nonvanishing of the actual common factor follows from nonvanishing
of its period, regulator and Tamagawa entries. -/
theorem commonFactorNonzero {R : Type u} [Field R]
    (Omega Reg Tam : R) (hOmega : Omega ≠ 0) (hReg : Reg ≠ 0)
    (hTam : Tam ≠ 0) : Omega*Reg*Tam ≠ 0 := by
  grind

/-- Exact reordering and quotient comparison in the standard BSD product.
This algebra uses totalized field division; its zero-denominator scope is
separately checked below rather than interpreted as arithmetic. -/
theorem cascadeProductIffNormalization {R : Type u} [Field R]
    (Omega Reg Tam kappa sha torsionSquared : R)
    (hCommon : Omega*Reg*Tam ≠ 0) :
    kappa*(Omega*Reg*Tam) = ((sha*Reg)*Omega)*Tam/torsionSquared ↔
      kappa=sha/torsionSquared := by
  grind

/-- Eliminating the denominator requires its explicit nonzero condition. -/
theorem normalizationIffCrossProduct {R : Type u} [Field R]
    (kappa sha torsionSquared : R) (hTorsion : torsionSquared ≠ 0) :
    kappa=sha/torsionSquared ↔ kappa*torsionSquared=sha := by
  grind

theorem cascadeProductIffCrossProduct {R : Type u} [Field R]
    (Omega Reg Tam kappa sha torsionSquared : R)
    (hCommon : Omega*Reg*Tam ≠ 0) (hTorsion : torsionSquared ≠ 0) :
    kappa*(Omega*Reg*Tam) = ((sha*Reg)*Omega)*Tam/torsionSquared ↔
      kappa*torsionSquared=sha := by
  rw [cascadeProductIffNormalization _ _ _ _ _ _ hCommon]
  exact normalizationIffCrossProduct _ _ _ hTorsion

/-- With the normalization supplied, the two leading-term statements are
equivalent. Neither statement's truth is an input to this rewriting proof. -/
theorem normalizedLeadingFormsEquivalent {R : Type u} [Field R]
    (leading Omega Reg Tam kappa sha torsionSquared : R)
    (hNormalization : kappa=sha/torsionSquared) :
    (leading=kappa*(Omega*Reg*Tam)) ↔
      (leading=((sha*Reg)*Omega)*Tam/torsionSquared) := by
  grind

/-- Uniform equivalence of the leading-term formulas characterizes the
normalization. Equivalence at just one leading value can hold because
both formulas are false and is not sufficient for this converse. -/
theorem allLeadingFormsIffNormalization {R : Type u} [Field R]
    (Omega Reg Tam kappa sha torsionSquared : R)
    (hCommon : Omega*Reg*Tam ≠ 0) :
    (∀ leading : R, (leading=kappa*(Omega*Reg*Tam)) ↔
      (leading=((sha*Reg)*Omega)*Tam/torsionSquared)) ↔
      kappa=sha/torsionSquared := by
  constructor
  · intro h
    exact (cascadeProductIffNormalization _ _ _ _ _ _ hCommon).mp
      ((h (kappa*(Omega*Reg*Tam))).mp rfl)
  · intro h leading
    exact normalizedLeadingFormsEquivalent leading _ _ _ _ _ _ h

end SixBirdsBSD.Apparatus.KappaNormalization
