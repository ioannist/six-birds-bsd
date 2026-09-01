/-!
`SixBirdsBSD.Apparatus.KappaNormalization` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § KappaNormalization.
-/

namespace SixBirdsBSD.Apparatus.KappaNormalization

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

end SixBirdsBSD.Apparatus.KappaNormalization
