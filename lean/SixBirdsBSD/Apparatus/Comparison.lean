import SixBirdsBSD.Apparatus.HeightRegulator

/-!
`SixBirdsBSD.Apparatus.Comparison` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § Comparison.
-/

namespace SixBirdsBSD.Apparatus.Comparison

open SixBirdsBSD.Apparatus.HeightRegulator

universe u

/-- The five-column tensor assembling the separated typed columns. -/
def fiveColumnTensor {An Ht Finite PAdic Det Target : Type u}
    (tensor5 : An → Ht → Finite → PAdic → Det → Target) :
    An × Ht × Finite × PAdic × Det → Target
  | (an, ht, finite, padic, det) => tensor5 an ht finite padic det

def comparisonBKRow : Fin 5 → Int :=
  fun i => if i = 4 then 0 else 1

def comparisonDetRow : Fin 5 → Int :=
  fun i => if i = 4 then 1 else 0

/-- The five-column source is adequate for the BK scalar contraction. -/
theorem fiveColBkComparison :
    let d := comparisonBKRow
    let K_DD := dot d d
    let projection := dot d (mulVec heightKLL d)
    let Xi := K_DD - projection
    K_DD = 4 ∧ projection = 4 ∧ Xi = 0 ∧
      dot d comparisonDetRow = 0 ∧ comparisonDetRow ≠ (fun _ => 0) := by
  let d := comparisonBKRow
  have hproj : mulVec heightKLL d = d := heightKLLMulVec d
  dsimp only
  constructor
  · decide
  · constructor
    · rw [hproj]
      decide
    · constructor
      · rw [hproj]
        decide
      · constructor
        · decide
        · intro h
          have h4 : comparisonDetRow 4 = (fun _ : Fin 5 => (0 : Int)) 4 := congrFun h 4
          exact (by decide : ¬ comparisonDetRow 4 = (fun _ : Fin 5 => (0 : Int)) 4) h4

end SixBirdsBSD.Apparatus.Comparison
