/-!
`SixBirdsBSD.Apparatus.Decomposition` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § Decomposition.
-/

namespace SixBirdsBSD.Apparatus.Decomposition

universe u

/-- The Bloch--Kato component-assembly map over the five typed BSD columns. -/
def bkComponentMap
    {Prime C_an C_ht C_fin C_BK _C_stat C_BK_E _M_E _Delta_f _z_BK _tau_BK : Type u}
    {C_p : Prime → Type u}
    (rho_an : C_an → C_BK_E)
    (rho_ht : C_ht → C_BK_E)
    (rho_fin : C_fin → C_BK_E)
    (rho_p : (p : Prime) → C_p p → C_BK_E)
    (rho_det : C_BK → C_BK_E) :
    Sum C_an (Sum C_ht (Sum C_fin (Sum (Sigma C_p) C_BK))) → C_BK_E
  | Sum.inl x => rho_an x
  | Sum.inr (Sum.inl x) => rho_ht x
  | Sum.inr (Sum.inr (Sum.inl x)) => rho_fin x
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl x))) => rho_p x.1 x.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr x))) => rho_det x

/-- The additive bridge-defect comparison equation after trivialization. -/
def bridgeDefectEquation {Prime : Type u}
    (Delta_BSD_BK E_an_period E_ht_reg E_finite sum_p_E_p E_det : Int)
    (_E_p : Prime → Int) : Prop :=
  Delta_BSD_BK = E_an_period + E_ht_reg + E_finite + sum_p_E_p + E_det

/-- Component killing and its legal-comparison contrapositive. -/
theorem componentKilling {Prime : Type u}
    {Delta_BSD_BK E_an_period E_ht_reg E_finite sum_p_E_p E_det : Int}
    {E_p : Prime → Int} :
    ((bridgeDefectEquation Delta_BSD_BK E_an_period E_ht_reg E_finite
        sum_p_E_p E_det E_p ∧
        ((∀ p, E_p p = 0) → sum_p_E_p = 0)) →
      E_an_period = 0 →
      E_ht_reg = 0 →
      E_finite = 0 →
      (∀ p, E_p p = 0) →
      E_det = 0 →
      Delta_BSD_BK = 0) ∧
    (Delta_BSD_BK ≠ 0 →
      ¬ (bridgeDefectEquation Delta_BSD_BK E_an_period E_ht_reg E_finite
          sum_p_E_p E_det E_p ∧
          ((∀ p, E_p p = 0) → sum_p_E_p = 0)) ∨
        E_an_period ≠ 0 ∨
        E_ht_reg ≠ 0 ∨
        E_finite ≠ 0 ∨
        (∃ p, E_p p ≠ 0) ∨
        E_det ≠ 0) := by
  classical
  let kill :
      (bridgeDefectEquation Delta_BSD_BK E_an_period E_ht_reg E_finite
        sum_p_E_p E_det E_p ∧
        ((∀ p, E_p p = 0) → sum_p_E_p = 0)) →
      E_an_period = 0 →
      E_ht_reg = 0 →
      E_finite = 0 →
      (∀ p, E_p p = 0) →
      E_det = 0 →
      Delta_BSD_BK = 0 := by
    intro hlegal h_an h_ht h_fin h_p h_det
    rcases hlegal with ⟨h_eq, h_sum⟩
    unfold bridgeDefectEquation at h_eq
    rw [h_an, h_ht, h_fin, h_sum h_p, h_det] at h_eq
    simpa using h_eq
  constructor
  · exact kill
  · intro h_nonzero
    by_cases hlegal :
        bridgeDefectEquation Delta_BSD_BK E_an_period E_ht_reg E_finite
          sum_p_E_p E_det E_p ∧
          ((∀ p, E_p p = 0) → sum_p_E_p = 0)
    · by_cases h_an : E_an_period = 0
      · by_cases h_ht : E_ht_reg = 0
        · by_cases h_fin : E_finite = 0
          · by_cases h_p : ∀ p, E_p p = 0
            · by_cases h_det : E_det = 0
              · exact False.elim (h_nonzero (kill hlegal h_an h_ht h_fin h_p h_det))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_det))))
            · have h_exists : ∃ p, E_p p ≠ 0 :=
                Classical.not_forall.mp h_p
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_exists))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h_fin)))
        · exact Or.inr (Or.inr (Or.inl h_ht))
      · exact Or.inr (Or.inl h_an)
    · exact Or.inl hlegal

/-- The NG-1 witness: the finite scalar row is a non-injective public shadow. -/
theorem finiteScalarPublicShadow :
    let C_fin := Int × Int × Int × Bool
    let q_p : C_fin → Int := fun x => x.1 + x.2.1 - 2 * x.2.2.1
    let casselsTate : C_fin → Bool := fun x => x.2.2.2
    let shaBlock : C_fin := (1, 0, 0, false)
    let tamagawaBlock : C_fin := (0, 1, 0, false)
    let ct0 : C_fin := (0, 0, 0, false)
    let ct1 : C_fin := (0, 0, 0, true)
    ¬ Function.Injective q_p ∧
      q_p shaBlock = 1 ∧
      q_p tamagawaBlock = 1 ∧
      shaBlock ≠ tamagawaBlock ∧
      q_p shaBlock = q_p tamagawaBlock ∧
      casselsTate ct0 ≠ casselsTate ct1 ∧
      q_p ct0 = q_p ct1 := by
  dsimp only
  constructor
  · intro h_inj
    have hq :
        (fun x : Int × Int × Int × Bool => x.1 + x.2.1 - 2 * x.2.2.1)
            ((1 : Int), (0 : Int), (0 : Int), false) =
          (fun x : Int × Int × Int × Bool => x.1 + x.2.1 - 2 * x.2.2.1)
            ((0 : Int), (1 : Int), (0 : Int), false) := by
      decide
    have h_eq :
        ((1 : Int), (0 : Int), (0 : Int), false) =
          ((0 : Int), (1 : Int), (0 : Int), false) :=
      h_inj hq
    exact (by decide :
      ¬ (((1 : Int), (0 : Int), (0 : Int), false) =
          ((0 : Int), (1 : Int), (0 : Int), false))) h_eq
  · constructor
    · decide
    · constructor
      · decide
      · constructor
        · decide
        · constructor
          · decide
          · constructor
            · decide
            · decide

end SixBirdsBSD.Apparatus.Decomposition
