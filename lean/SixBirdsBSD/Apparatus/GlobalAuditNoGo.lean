/-!
`SixBirdsBSD.Apparatus.GlobalAuditNoGo` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § GlobalAuditNoGo.
-/

namespace SixBirdsBSD.Apparatus.GlobalAuditNoGo

structure GlobalCompletion where
  row : Nat → Bool

def windowRows (c : GlobalCompletion) : Fin 5 → Bool :=
  fun i => c.row i.val

def agreeOnW50 (a b : GlobalCompletion) : Prop :=
  windowRows a = windowRows b

def differOutsideW50 (a b : GlobalCompletion) : Prop :=
  ∃ n, 5 ≤ n ∧ a.row n ≠ b.row n

def completionBase : GlobalCompletion :=
  ⟨fun _ => false⟩

def completionTailVariant : GlobalCompletion :=
  ⟨fun n => if n = 5 then true else false⟩

def traceXiB (M : Nat) : Nat :=
  M - 5

/-- Finite-window data has unbounded tail residual and cannot distinguish completions. -/
theorem finiteWindowNoGo :
    (∀ t : Nat, ∃ M : Nat, 5 ≤ M ∧ traceXiB M = t) ∧
      agreeOnW50 completionBase completionTailVariant ∧
      differOutsideW50 completionBase completionTailVariant ∧
      (∀ (α : Sort _) (operator : (Fin 5 → Bool) → α),
        operator (windowRows completionBase) = operator (windowRows completionTailVariant)) := by
  constructor
  · intro t
    refine ⟨t + 5, ?_, ?_⟩
    · exact Nat.le_add_left 5 t
    · unfold traceXiB
      exact Nat.add_sub_cancel t 5
  · constructor
    · unfold agreeOnW50 windowRows completionBase completionTailVariant
      funext i
      have hlt : i.val < 5 := i.isLt
      have hne : ¬i.val = 5 := Nat.ne_of_lt hlt
      simp [hne]
    · constructor
      · refine ⟨5, Nat.le_refl 5, ?_⟩
        unfold completionBase completionTailVariant
        decide
      · intro α operator
        apply congrArg operator
        unfold windowRows completionBase completionTailVariant
        funext i
        have hlt : i.val < 5 := i.isLt
        have hne : ¬i.val = 5 := Nat.ne_of_lt hlt
        simp [hne]

end SixBirdsBSD.Apparatus.GlobalAuditNoGo
