import SixBirdsBSD.Apparatus.HeightRegulator

/-!
`SixBirdsBSD.Apparatus.FiniteSource` — per-section module (apparatus axis).

Mechanization of `anti_loc/extracted_math/apparatus_master.md` § FiniteSource.
-/

namespace SixBirdsBSD.Apparatus.FiniteSource

open SixBirdsBSD.Apparatus.HeightRegulator

universe u

/-- The real finite-source map tensors the Tamagawa, torsion, and Sha--CT rows. -/
def finiteSourceMap {Tam Tors ShaCT Target : Type u}
    (rhoTam : Tam → Target)
    (rhoTors : Tors → Target)
    (rhoShaCT : ShaCT → Target)
    (tensor3 : Target → Target → Target → Target) :
    Tam × Tors × ShaCT → Target
  | (tam, tors, shaCTPairing) => tensor3 (rhoTam tam) (rhoTors tors) (rhoShaCT shaCTPairing)

def matMul {n : Nat} (A B : Fin n → Fin n → Int) : Fin n → Fin n → Int :=
  fun i j => sumFin (fun k => A i k * B k j)

def matSub {n : Nat} (A B : Fin n → Fin n → Int) : Fin n → Fin n → Int :=
  fun i j => A i j - B i j

def zeroMatrix {n : Nat} : Fin n → Fin n → Int :=
  fun _ _ => 0

def trace {n : Nat} (M : Fin n → Fin n → Int) : Int :=
  sumFin (fun i => M i i)

/-- The explicit matrix computation `I * I = I`. -/
theorem heightKLLMatMul {n : Nat} :
    matMul (n := n) (heightKLL : Fin n → Fin n → Int) heightKLL = heightKLL := by
  funext i j
  exact sumFinKronecker i (fun k => heightKLL k j)

/-- Pairing-aware finite source admits the full identity projection. -/
theorem finiteSourceSchurCollapse :
    let I4 : Fin 4 → Fin 4 → Int := heightKLL
    let I4dagger : Fin 4 → Fin 4 → Int := I4
    let projection := matMul (matMul I4 I4dagger) I4
    let Xi_C := matSub I4 projection
    projection = I4 ∧ Xi_C = zeroMatrix := by
  dsimp only
  have hmul : matMul heightKLL heightKLL = (heightKLL : Fin 4 → Fin 4 → Int) :=
    heightKLLMatMul
  constructor
  · rw [hmul, hmul]
  · rw [hmul, hmul]
    funext i j
    simp [matSub, zeroMatrix]

def scalarFiniteRow : Fin 4 → Int := fun i =>
  if i = 0 then 1 else if i = 1 then -2 else if i = 2 then 1 else 0

def sumFinRat : {n : Nat} → (Fin n → Rat) → Rat
  | 0, _ => 0
  | Nat.succ n, f => sumFinRat (fun i : Fin n => f i.castSucc) + f (Fin.last n)

def traceRat {n : Nat} (M : Fin n → Fin n → Rat) : Rat :=
  sumFinRat (fun i => M i i)

def scalarFiniteRowRat : Fin 4 → Rat := fun i =>
  if i = 0 then 1 else if i = 1 then -2 else if i = 2 then 1 else 0

def scalarFiniteSsT : Rat :=
  sumFinRat (fun i => scalarFiniteRowRat i * scalarFiniteRowRat i)

def scalarFiniteProjector : Fin 4 → Fin 4 → Rat :=
  fun i j => (scalarFiniteRowRat i * scalarFiniteRowRat j) / scalarFiniteSsT

theorem ratNegTwoMulNegTwo : ((-2 : Rat) * (-2)) = 4 := by
  rw [Rat.mul_def, Rat.normalize_eq_mkRat]
  unfold mkRat
  simp [Rat.normalize_eq_mk']

theorem ratOneAddFour : ((1 : Rat) + 4) = 5 := by
  rw [Rat.add_def, Rat.normalize_eq_mkRat]
  unfold mkRat
  simp [Rat.normalize_eq_mk']

theorem ratFiveAddOne : ((5 : Rat) + 1) = 6 := by
  rw [Rat.add_def, Rat.normalize_eq_mkRat]
  unfold mkRat
  simp [Rat.normalize_eq_mk']

theorem ratFourSubOne : ((4 : Rat) - 1) = 3 := by
  rw [Rat.sub_def, Rat.normalize_eq_mkRat]
  unfold mkRat
  simp [Rat.normalize_eq_mk']

theorem scalarFiniteSsTEqSix : scalarFiniteSsT = 6 := by
  simp [scalarFiniteSsT, sumFinRat, scalarFiniteRowRat]
  rw [ratNegTwoMulNegTwo]
  rw [show ((0 : Rat) + 1) = 1 by exact Rat.zero_add 1]
  rw [ratOneAddFour]
  rw [ratFiveAddOne]
  exact Rat.add_zero 6

theorem scalarFiniteProjectorTraceEqOne : traceRat scalarFiniteProjector = 1 := by
  simp [traceRat, scalarFiniteProjector, sumFinRat, scalarFiniteRowRat,
    scalarFiniteSsTEqSix]
  rw [ratNegTwoMulNegTwo]
  rw [show ((0 : Rat) / 6) = 0 by
    rw [Rat.div_def]
    simp]
  rw [show ((0 : Rat) + 1 / 6) = 1 / 6 by exact Rat.zero_add _]
  rw [show ((1 : Rat) / 6) = Rat.divInt 1 6 by
    exact (Rat.divInt_eq_div 1 6).symm]
  rw [show ((4 : Rat) / 6) = Rat.divInt 4 6 by
    exact (Rat.divInt_eq_div 4 6).symm]
  simp
  rw [Rat.add_zero]
  exact Rat.divInt_self' (by decide : (216 : Int) ≠ 0)

/-- The rank-one scalar projector has trace one, computed from `s*s^T = 6`. -/
theorem scalarProjectorTrace :
    scalarFiniteSsT = 6 ∧ scalarFiniteSsT ≠ 0 ∧
      traceRat scalarFiniteProjector = scalarFiniteSsT / scalarFiniteSsT ∧
      traceRat scalarFiniteProjector = 1 := by
  have hSsT : scalarFiniteSsT = 6 := scalarFiniteSsTEqSix
  have htrace : traceRat scalarFiniteProjector = 1 := scalarFiniteProjectorTraceEqOne
  have hdiv : scalarFiniteSsT / scalarFiniteSsT = 1 := by
    rw [hSsT, Rat.div_def]
    exact Rat.mul_inv_cancel (6 : Rat) (by decide)
  constructor
  · exact hSsT
  · constructor
    · rw [hSsT]
      decide
    · constructor
      · rw [htrace, hdiv]
      · exact htrace

def scalarShaCTWitness : Fin 4 → Int := fun i =>
  if i = 0 then 0 else if i = 1 then 0 else if i = 2 then 2 else 1

def scalarTamagawaWitness : Fin 4 → Int := fun i =>
  if i = 0 then 2 else if i = 1 then 0 else if i = 2 then 0 else 0

/-- The scalar finite row has positive residual trace and is non-injective. -/
theorem scalarFiniteShadow :
    let ssT := scalarFiniteSsT
    let ambientTrace : Rat := 4
    let projectorTrace := traceRat scalarFiniteProjector
    let XiScalarTrace := ambientTrace - projectorTrace
    ssT = 6 ∧ projectorTrace = ssT / ssT ∧ projectorTrace = 1 ∧
      XiScalarTrace = 3 ∧ XiScalarTrace > 0 ∧
      dot scalarFiniteRow scalarShaCTWitness = 2 ∧
      dot scalarFiniteRow scalarTamagawaWitness = 2 ∧
      scalarShaCTWitness ≠ scalarTamagawaWitness := by
  have htrace := scalarProjectorTrace
  dsimp only
  constructor
  · exact htrace.1
  · constructor
    · exact htrace.2.2.1
    · constructor
      · exact htrace.2.2.2
      · constructor
        · rw [htrace.2.2.2]
          exact ratFourSubOne
        · constructor
          · rw [htrace.2.2.2]
            rw [ratFourSubOne]
            decide
          · constructor
            · decide
            · constructor
              · decide
              · intro h
                have h0 : scalarShaCTWitness 0 = scalarTamagawaWitness 0 := congrFun h 0
                exact (by decide : ¬ scalarShaCTWitness 0 = scalarTamagawaWitness 0) h0

def dimShaProjector : Fin 2 → Fin 2 → Int :=
  fun i j => (if i = 0 then 1 else 0) * (if j = 0 then 1 else 0)

def dimShaXi : Fin 2 → Fin 2 → Int :=
  matSub heightKLL dimShaProjector

def dimShaU1 : Int × Nat := (2, 2)

def dimShaU2 : Int × Nat := (2, 4)

/-- Dimension-only Sha data leaves the Cassels--Tate coordinate as residual. -/
theorem dimShaShadow :
    dimShaXi 0 0 = 0 ∧ dimShaXi 0 1 = 0 ∧
      dimShaXi 1 0 = 0 ∧ dimShaXi 1 1 = 1 ∧
      trace dimShaXi = 1 ∧ (1 : Int) > 0 ∧
      dimShaU1.1 = dimShaU2.1 ∧ dimShaU1.2 ≠ dimShaU2.2 := by
  constructor
  · decide
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
            · constructor
              · decide
              · decide

end SixBirdsBSD.Apparatus.FiniteSource
