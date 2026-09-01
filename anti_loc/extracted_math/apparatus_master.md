# Apparatus axis (Paper A) — consolidated math (Phase A.3)

Consolidated, dependency-ordered, labeled statements-of-record for the
**typed five-column Bloch–Kato decomposition + adequacy diagnostics +
no-go suite**. This is the binding source for the apparatus-axis Lean
mechanization (it drives `apparatus_paper_inventory.toml` →
`queue_apparatus.csv` → `SixBirdsBSD.Apparatus.*`).

Historical source-step identifiers are retained as concise provenance tags.
Labels are stable: `<kind>:apparatus:<short-name>`.
Notation is harmonized across steps; the Schur adequacy residual is
written `Ξ_C(D∣L) = K_DD − K_DL K_LL^† K_LD` throughout.

Standing conventions: `E/Q` an elliptic curve, `M_E = h¹(E)(1)`,
`r = rank E(Q)`, `r_an = ord_{s=1} L(E,s)`. Adequacy orientation: a
column readout is **adequate** when its Schur residual vanishes,
`Ξ_C(D∣L) = 0`. The five refined external transports
(`ρ_*_integral_BK_transport`) are out-of-scope-for-Lean recognition
obligations carried by the columns, recorded but not mechanized.

---

## §1. Decomposition — the typed five columns
Module: `SixBirdsBSD.Apparatus.Decomposition`. Source: bsd_b52a.

### def:apparatus:bk-component-map
The Bloch–Kato component-assembly map for `M_E = h¹(E)(1)` is
`ρ_BK = ρ_an ⊕ ρ_ht ⊕ ρ_fin ⊕ (⊕_p ρ_p) ⊕ ρ_det`, from the integrated
typed BSD carrier `C_BSD = (C_an, {C_p}_p, C_ht, C_fin, C_BK, C_stat)`
to the determinant-line target
`C_BK(E) = (M_E, Δ_f(M_E), z_BK(M_E), τ_BK(M_E))`, with typed components
(i) `ρ_an : C_an → C_BK` (central leading-term + period → analytic
zeta/trivialization side); (ii) `ρ_ht : C_ht → C_BK` (Mordell–Weil
height/regulator → global cohomological determinant); (iii)
`ρ_fin : C_fin → C_BK` (Tamagawa, torsion, `Sha[p^∞]`, Cassels–Tate →
finite arithmetic determinant); (iv) `ρ_p : C_p → C_BK` (p-adic
analytic/Selmer + control + local normalization → p-primary
determinant); (v) `ρ_det` (orientation/sign/unit compatibility — same
determinant line).

### def:apparatus:bridge-defect-equation
After choosing a comparison trivialization, the strong-duality defect
decomposes additively:
`Δ_BSD^BK = E_an/period + E_ht/reg + E_finite + Σ_p E_p + E_det`
(multiplicatively, the corresponding product of component ratios).

### thm:apparatus:component-killing
If every component defect vanishes in the declared determinant-line
comparison (`E_an/period = E_ht/reg = E_finite = E_p (∀p) = E_det = 0`)
then `Δ_BSD^BK = 0`. Contrapositive: if `Δ_BSD^BK ≠ 0` then at least one
component defect is nonzero or not legally comparable. *(Proof: immediate
from def:apparatus:bridge-defect-equation.)*

### thm:apparatus:finite-scalar-public-shadow (NG-1, decomposition form)
The finite scalar BSD factor
`φ_fin(C_fin) = |Sha|·∏_ℓ c_ℓ / |E(Q)_tors|²`, with prime-local
valuation `q_p = v_p|Sha| + v_p(∏_ℓ c_ℓ) − 2 v_p|E(Q)_tors|`, is **not
injective** on the typed finite-source tower
`C_fin = C_Tamagawa ⊕ C_torsion ⊕ C_{Sha[p^∞]} ⊕ C_CT`. Witness: at a
fixed `p`, the triples `(v_p|Sha|, v_p c, v_p|E_tors|) = (1,0,0)` and
`(0,1,0)` both give `q_p = 1` but place the valuation in the
`Sha`-block vs the Tamagawa block; the Cassels–Tate datum is entirely
forgotten by `q_p`. Hence a scalar finite-factor row cannot be promoted
to a finite-source carrier row without additional source data.

### nonclaim:apparatus:decomposition-scope
b52a does not prove BSD, Bloch–Kato, or ETNC. It proves the
component-map and the public-shadow no-go for the typed bridge, and
classifies framework-derived content vs the five external transports.[^b52a]

[^b52a]: bsd_b52a (`bsd_b52a_bk_component_map.tex`, `bsd_b52a_public_shadow_no_go.csv`, `bsd_b52a_defect_equation.csv`).

---

## §2. HeightRegulator — `ρ_ht/reg^R`
Module: `SixBirdsBSD.Apparatus.HeightRegulator`. Source: bsd_b53.

Carrier: `Λ_E = E(Q)/E(Q)_tors`, `V_E = Λ_E ⊗_Z R`, `r = rank_Z Λ_E`.
Néron–Tate pairing `⟨P,Q⟩_NT = (ĥ(P+Q) − ĥ(P) − ĥ(Q))/2`; for a basis
`(P_1,…,P_r)`, `H_E = (⟨P_i,P_j⟩_NT)`, `Reg(E/Q) = det H_E` (empty
determinant `= 1` for `r = 0`).

### def:apparatus:height-regulator-map
`ρ_ht/reg^R : (V_E, Λ_E, ⟨·,·⟩_NT) ↦ det(h_NT) ∈ det(V_E^*) ⊗ det(V_E)^*`,
where `h_NT : V_E → V_E^*`, `P ↦ ⟨P,·⟩_NT`. In a basis the element has
scalar coefficient `det H_E = Reg(E/Q)`. Basis-independent: under
`A ∈ GL_r(Z)`, `H_E ↦ AᵀH_E A` and `det(AᵀH_E A) = det(A)² det H_E =
det H_E` since `det A = ±1`. (Full BK component
`ρ_ht/reg = β_BK,ht ∘ ρ_ht/reg^R`; `β_BK,ht` is the external transport,
obl:apparatus:rho-ht-reg-transport.)

### thm:apparatus:height-schur-collapse
On the tangent height carrier `S_r = Sym_r(R)`, coordinate
`x = vech(δH)`, audit energy `C = I`: with native family
`L_full(x) = x` and dissolving readout
`D_H(δH) = d(log det)_H(δH) = tr(H^{-1} δH) = d_H x`, one has
`Ξ_C(D∣L_full) = K_DD − K_DL K_LL^† K_LD = d_H d_Hᵀ − d_H I d_Hᵀ = 0`.
The pre-source residual is `K_DD = d_H d_Hᵀ = ‖d_H‖²` (e.g. 37a1 rank 1:
`K_DD = 382.79…`); admitting the full height pairing collapses it to 0.
*(Instances: 37a1 rank 1; symbolic rank-2 template `H_2`; 11a1/571a1
rank-0 vacuous — `K_DD = 0`.)*

### obl:apparatus:rho-ht-reg-transport (out_of_scope_recognition_source)
Construct an accepted bridge
`β_BK,ht : det(V_E^*) ⊗ det(V_E)^* → Δ_f(M_E)_ht/reg` identifying the
Néron–Tate determinant with the Beilinson/Deligne regulator
normalization (coefficient convention; archimedean Deligne-cohomology
normalization; determinant orientation/trivialization; compatibility
with finite/det components without absorbing them). External:
Beilinson regulators; Néron–Tate; Nekovář heights.

### warn:apparatus:571a1-carrier
571a1 is Mordell–Weil rank 0 with nontrivial `Sha[2]`/Cassels–Tate
data; its lawful height-regulator row is rank-0/vacuous. Rank-2
instances use 389a1.[^b53]

[^b53]: bsd_b53 (`bsd_b53_height_regulator_component_map.tex`, `bsd_b53_schur_residual_computations.csv`).

---

## §3. AnalyticPeriod — `ρ_an/period^R`
Module: `SixBirdsBSD.Apparatus.AnalyticPeriod`. Source: bsd_b54.

By modularity, `f_E ∈ S_2(Γ_0(N))`, `L(E,s) = L(f_E,s)`,
`A_E = L^{(r_an)}(E,1)/r_an!` (the standard BSD leading coefficient —
equivalently the leading Taylor coefficient `L^*(E,1) = lim_{s→1}
L(E,s)/(s−1)^{r_an}`, with no further division), real period
`Ω_E^+ = ∫_{γ_∞} ω_E`.

### def:apparatus:analytic-period-map
Native family `L_an/per(E) = (A_E, Ω_E^+)`; isolated scalar
`q_an/per(E) = A_E/Ω_E^+`. The real map is
`ρ_an/period^R : (A_E, Ω_E^+) ↦ (A_E/Ω_E^+)·e_an/per ∈ L_an/per(E)_R`.
Excludes the height regulator, torsion, Tamagawa, and `Sha` data.
(Full BK component `ρ_an/period = ι_BK,an ∘ β_Del ∘ ρ_an/period^R`.)

### thm:apparatus:analytic-period-schur-collapse
With `x = (log A_E, log Ω_E^+) ∈ R²`, `C = I_2`, native `L_full(x) = x`,
dissolving readout `D(x) = x_A − x_Ω` (row `d = (1,−1)`): block
currencies `K_LL = I_2`, `K_DL = d`, `K_DD = d dᵀ = 2`, so
`Ξ_C(D∣L) = 2 − d I_2 dᵀ = 0`. (No source admitted → residual 2; only
`x_A` → residual 1; both → 0.) *(Instances 11a1/37a1/389a1: same linear
signature `K_DD = 2`, `Ξ_full = 0`, differing only in base point.)*

BSD-prediction match (numerical, evidence only): 11a1 `L/Ω = 0.2 =
∏c_v·#Sha/|E_tors|² = 5/25`; 37a1 `L'/Ω = 0.05111… = Reg(37a1)`; 389a1
`L''/2!/Ω = 0.15246… = Reg(389a1)`.

### obl:apparatus:rho-an-period-transport (out_of_scope_recognition_source)
Construct `β_BK,an : L_an/per(E)_R → Δ_f(M_E)_an/per` identifying
`L^{(r_an)}(E,1)/(r_an!·Ω_E^+)` with the analytic zeta-element factor
(rational vs integral; Betti–de Rham comparison + real orientation;
positive-rank leading-term normalization; separation from the other
columns). Rank-0 classical; rank ≥ 1 conjectural (BSD-equivalent).[^b54]

[^b54]: bsd_b54 (`bsd_b54_analytic_period_component_map.tex`, `bsd_b54_schur_residual_computations.csv`). **Intentional source correction:** b54 writes `A_E = L^*(E,1)/r_an!` with `L^*(E,1) = lim_{s→1} L(E,s)/(s−1)^{r_an}`, a double division; the master corrects this to `A_E = L^{(r_an)}(E,1)/r_an!`, which matches b54's own evidence rows (37a1 `L'/Ω = Reg`, 389a1 `L''/2!/Ω = Reg`). The cascade artifact is left unedited as provenance-of-record; this footnote records the correction.

---

## §4. FiniteSource — `ρ_finite^R` and the finite no-gos
Module: `SixBirdsBSD.Apparatus.FiniteSource`. Source: bsd_b55.

Carrier tower `C_fin(E) = C_Tamagawa ⊕ C_torsion ⊕ C_{Sha[p^∞]} ⊕ C_CT`.

### def:apparatus:finite-source-map
Native family `L_finite(E) = ((c_v(E))_{v|N}, E(Q)_tors,
(Sha(E/Q)[p^∞])_p, ⟨·,·⟩_CT)`. The real map is the tensor
`ρ_finite^R = ρ_Tam^R ⊗ ρ_tors^R ⊗ ⊗_p ρ_{Sha-CT,p}^R` with:
- `ρ_Tam^R : (c_v)_{v|N} ↦ ⊗_{v|N} c_v·e_v^loc`, `c_v = |Φ_v(E)|`,
  `Φ_v = E(Q_v)/E^0(Q_v)`;
- `ρ_tors^R : T(E) ↦ ⊗_p |T_p(E)|^{-2}·e_p^tors`;
- `ρ_{Sha-CT,p}^R : (S_p, ⟨·,·⟩_CT,p) ↦ Pf(⟨·,·⟩_CT,p)·e_p^{Sha-CT}`,
  where `S_p = Sha[p^∞]/Sha_div[p^∞]` carries the perfect alternating
  Cassels–Tate pairing; the Pfaffian records the determinant-line
  trivialization (unit for trivial `S_p`).

The source datum is the **pairing** `(S_p, ⟨·,·⟩_CT,p)`, not `|S_p|`
and not `dim_{F_p} S_p[p]`. (Full BK component
`ρ_finite = β_BK,finite ∘ ρ_finite^R`.)

### thm:apparatus:finite-source-schur-collapse
At a support prime `p`, `x = (x_T, x_tors, x_Sha, x_CT) ∈ R⁴` with
`x_T = v_p(∏_v c_v)`, `x_tors = v_p|E(Q)_tors|`, `x_Sha = v_p|S_p|`,
`x_CT =` CT-pairing coordinate. With pairing-aware `D_full(x) = x`,
`L_full(x) = x`, `C = I_4`:
`Ξ_C(D_full∣L_full) = I_4 − I_4 I_4^† I_4 = 0`.

*Mechanization note (rfl-risk):* because `D_full = L_full = id`, the
Lean theorem must derive `Ξ = 0` by computing the Moore–Penrose
pseudoinverse `I_4^† = I_4` and the projection `K_DL I_4^† K_LD = I_4`
explicitly (a genuine `≥1` non-`rfl` step), not assert it by definitional
choice. The substantive finite-source content is the paired no-gos
`thm:apparatus:scalar-finite-shadow` and `thm:apparatus:dim-sha-shadow`
(positive residuals), which must be mechanized together with this
collapse.

### thm:apparatus:scalar-finite-shadow (NG-1, Schur form)
The scalar projection `q = s·x`, `s = (1,−2,1,0)`, has Schur projector
`P_s = sᵀ(s sᵀ)^{-1} s` and leaves `Ξ_scalar = I_4 − P_s` with
`tr(Ξ_scalar) = 3 > 0` against `D_full`. Explicit noninjectivity:
`(0,0,2,H)` and `(2,0,0,0)` both give scalar `q = 2` but live in the
`Sha`-CT vs Tamagawa blocks. Hence the scalar finite factor is provably
inadequate as a finite-source column.

### thm:apparatus:dim-sha-shadow (NG-2, Schur form)
On the `Sha`-CT subcarrier `y = (m, θ) ∈ R²` (`m` = p-power
elementary-divisor length, `θ` = CT coordinate), the dimension-only
projection `L_dim(y) = (1,0)y` leaves
`Ξ_dim = I_2 − (1,0)ᵀ(1,0) = diag(0,1)`, `tr(Ξ_dim) = 1 > 0`. Witness:
`U_1 = (Z/2Z)²` with `⟨e,f⟩ = ½ mod Z` and `U_2 = (Z/4Z)²` with
`⟨e,f⟩ = ¼ mod Z` both have `dim_{F_2} U_i[2] = 2` but differ in CT
determinant-line factor. The Pfaffian of the CT pairing is the natural
datum; the dimension is the noninjective shadow.

### obl:apparatus:rho-finite-transport (out_of_scope_recognition_source)
Construct `β_BK,finite : L_finite(E)_R → Δ_f(M_E)_finite` (integral
local-condition conventions at bad primes; squared-torsion
normalization; Cassels–Tate Pfaffian/orientation; compatibility with
`ρ_det`). External: Flach; Poonen–Stoll; Bloch–Kato local finite.[^b55]

[^b55]: bsd_b55 (`bsd_b55_finite_source_component_map.tex`, `bsd_b55_no_go_demonstrations.csv`, `bsd_b55_schur_residual_computations.csv`). NG-1 originating discipline: bsd_b30.

---

## §5. PAdic — `ρ_p^R`
Module: `SixBirdsBSD.Apparatus.PAdic`. Source: bsd_b56.

`T = T_p E`, `V = V_p(E) = T ⊗ Q_p` over `G_{Q_p}`; local condition
`H^1_f(Q_p,V) = ker(H^1(Q_p,V) → H^1(Q_p, V ⊗ B_cris))`; dual
exponential `exp^* : H^1_f(Q_p,V) → D_dR(V)/Fil⁰ D_dR(V)`.

### def:apparatus:p-adic-map
**Good ordinary** (`a_p` a `p`-unit; `α_p + β_p = a_p`, `α_p β_p = p`,
`v_p(α_p) = 0`; ordinary filtration `0 → T^+ → T → T^- → 0`): native
`L_p^ord(E) = (T^+, H^1_f(Q_p,V), exp^*)`,
`ρ_{p,ord}^R : (T^+, H^1_f, exp^*) ↦ e_{T^+} ⊗ det(exp^*)·e_loc,p ∈
Δ_f(V,T)_{p,R}^ord`.
**Good supersingular** (`a_p ≡ 0 mod p`): signed
`L_p^±(E) = (H^1_+, H^1_-, exp^*)` per Pollack–Kobayashi,
`ρ_{p,±}^R : (H^1_+, H^1_-, exp^*) ↦ e_+ ⊗ e_- ⊗ det(exp^*)·e_loc,p^±`.
(Full component `ρ_p = ι_BK-local ∘ ρ_p^R`.)

### thm:apparatus:ordinary-schur-collapse
Good-ordinary tangent `x = (x_ord, x_f, x_exp) ∈ R³`, `D_ord(x) = x`,
`L_ord,full(x) = x`, `C = I_3`: `Ξ_C(D_ord∣L_ord,full) = 0`. Omitting
the ordinary-control coordinate `x_ord` leaves trace residual 1 — the
unit-root control is necessary; unsigned local L alone is inadequate.
*(Rows 11a1@5 `a_5=1`, 37a1@5 `a_5=−2`.)*
*Mechanization note (rfl-risk):* the full collapse has `D = L = id`;
mechanize `I_3^† = I_3` and the projection explicitly, not `Ξ = 0` by
definition. The substantive content is the **residual-1 shadow**
(omit-`x_ord`), which must be mechanized as the non-trivial sibling.

### thm:apparatus:signed-schur-collapse
Good-supersingular signed tangent `y = (y_+, y_-, y_exp) ∈ R³`,
`D_±(y) = y`, `L_±,full(y) = y`, `C = I_3`:
`Ξ_C(D_±∣L_±,full) = 0`. The unsigned projection
`L_uns(y) = (y_+ + y_-, y_exp)` has rank 2 and leaves the difference
direction `y_+ − y_-` invisible → trace residual 1. The signed
Pollack–Kobayashi decomposition is structural; unsigned aggregation is
a public shadow. *(Row 37a1@3 `a_3 = −3`.)*
*Mechanization note (rfl-risk):* the full signed collapse has
`D = L = id`; mechanize `I_3^† = I_3` and the projection explicitly. The
substantive content is the **unsigned-collapse residual-1** (the rank-2
projection killing `y_+ − y_-`), which carries the non-`rfl` step.

### obl:apparatus:rho-p-transport (out_of_scope_recognition_source)
Construct `β_BK,p : Δ_f(V,T)_{p,R} → Δ_f(M_E)_p` (integral
Fontaine–Laffaille/Wach data; local Tate-pairing + dual-exp orientation;
Nekovář Selmer-complex local-global compatibility; signed normalization;
compatibility with `ρ_det`). External: BK local; Greenberg;
Pollack–Kobayashi; Nekovář.[^b56]

[^b56]: bsd_b56 (`bsd_b56_p_adic_component_map.tex`, `bsd_b56_reduction_type_table.csv`, `bsd_b56_schur_residual_computations.csv`).

---

## §6. DetAssembly — `ρ_det^R` and cascade completion
Module: `SixBirdsBSD.Apparatus.DetAssembly`. Source: bsd_b57.

### def:apparatus:det-assembly-map
Assembly native family is the tensor of the four constructed
components, `L_assembly(E) = ρ_ht/reg^R ⊗ ρ_an/period^R ⊗ ρ_finite^R ⊗
⊗_{p∈S(E)} ρ_p^R`. With orientation/trivialization coordinate `o_det`,
the real map is
`ρ_det^R : λ_loc(E) ⊗ o_det ↦ λ_loc(E)·o_det ∈ Δ_f(M_E)_R`, where
`λ_loc(E)` is that local tensor. (Full map
`ρ_det = β_det-assembly ∘ ρ_det^R`.)

### thm:apparatus:cascade-completion-signature
Cascade-level tangent `x = (x_ht, x_an, x_fin, x_p, x_det) ∈ R⁵`. Native
assembly source row `ℓ = (1,1,1,1,0)`, global determinant target
`d = (1,1,1,1,1)`. With `C = I_5`: `K_DD = d dᵀ = 5`,
`K_LL = ℓ ℓᵀ = 4`, `K_DL = d ℓᵀ = 4`, so
`Ξ_C(D∣L) = 5 − 4·4^{-1}·4 = 1`. The residual is **exactly** the
one-dimensional determinant-orientation coordinate `x_det`: the four
constructed components explain everything except the global determinant
orientation. *(Instances 11a1/37a1/389a1: structural residual 1,
base-point-independent.)*

### obl:apparatus:rho-det-assembly (out_of_scope_recognition_source)
Construct `β_det-assembly : (Δ_ht/reg ⊗ Δ_an/period ⊗ Δ_finite ⊗ ⊗_p Δ_p)
→ Δ_f(M_E)` (Knudsen–Mumford determinant signs; Selmer-complex
local-global compatibility; zeta-element vs motivic trivialization;
compatibility with the four refined transports). External:
Fontaine–Perrin-Riou; Knudsen–Mumford; ETNC.[^b57]

[^b57]: bsd_b57 (`bsd_b57_det_assembly_component_map.tex`, `bsd_b57_cascade_completion_summary.csv`, `bsd_b57_schur_residual_computations.csv`).

---

## §7. Comparison — literature gap + `Φ_5col↔BK`
Module: `SixBirdsBSD.Apparatus.Comparison`. Sources: bsd_b58, bsd_b59.

### rmk:apparatus:five-column-literature-gap (support_only — audit observation, NOT a Lean theorem)
Paper-grounded literature audit (Schneider 1988; Bloch–Kato 1990 §5
pp. 371–383; Nekovář 1994; b58 overall verdict: `mixed`) records that
the audited literature presents `Δ_f(M_E)` as a single **global
Tamagawa-number package**, with no typed-column decomposition separating
the height-regulator / analytic-period / finite / p-adic / det slots.
Relative to that audited corpus, the b52a five-column decomposition
`Δ_BSD^BK = E_an/period + E_ht/reg + E_finite + Σ_p E_p + E_det` is a
structural contribution not found in the literature. This is a
**paper-grounded audit observation (`support_only`)**, not a
Lean-derivable theorem; it is not mechanized.[^b58]

### def:apparatus:five-column-tensor
`T_5col(E) = ρ_an/period^R(E) ⊗ ρ_ht/reg^R(E) ⊗ ρ_finite^R(E) ⊗
⊗_{p∈S} ρ_p^R(E) ⊗ ρ_det^R(E)`; source family `L` = its five separated
log-tangent coordinates, target `D` = the single BK Tamagawa-package
coordinate.

### thm:apparatus:five-col-bk-comparison (Φ_5col↔BK)
At the log-tangent level `x = (x_an, x_ht, x_fin, x_p, x_det) ∈ R⁵`,
define `Φ_5col↔BK(x) = d·x` with `d = (1,1,1,1,0)`. With `K_LL = I_5`,
`K_DL = d`, `K_DD = ‖d‖² = 4`:
`Ξ_{5col↔BK} = 4 − d I_5 dᵀ = 4 − 4 = 0`. So the typed source is
**adequate** for the BK scalar projection, and `x_det ∈ ker Φ` — the BK
global-Tamagawa scalar is a strict 1-dimensional shadow of the typed
atlas. The integral arithmetic interpretation is conditional on the
five refined transports. *(Instance 11a1: `Φ = (A/Ω)·Reg·(∏c/|tors|²)·1
= 0.2·1·0.2·1 = 0.04`, `log Φ = 2 log 0.2`.)*[^b59]

[^b58]: bsd_b58 (`bsd_b58_paper_grounded_extract.md`, `bsd_b58_paper_audit_table.csv`).
[^b59]: bsd_b59 (`bsd_b59_five_column_vs_BK_comparison.tex`, `bsd_b59_comparison_map_construction.csv`).

---

## §8. HigherRankNoGo — NG-3 and the rank-2 Kummer source
Module: `SixBirdsBSD.Apparatus.HigherRankNoGo`. Source: bsd_b60.

### def:apparatus:rank-two-kummer-source
For `Λ_E = E(Q)/E(Q)_tors` and prime `p`, the Kummer map
`κ_p : Λ_E ⊗ Q_p → H^1_f(Q, V_p(E))` gives, on a MW basis `(P_1,P_2)` of
389a1, the rank-2 candidate `c_2^MW(P_i) = κ_p(P_i)` — a rank-2 Selmer
source after `⊗ Q_p`. Classical once the basis is known; not a
generalized Heegner-cycle construction and not a motivic-cycle source.

### thm:apparatus:rank-two-height-schur-collapse
For the 389a1 Gram representative `H_E` with
`d(log det)_H = ℓ = (3.12679…, −0.76771…, 2.14483…)` on
`(δh_11, δh_12, δh_22)`, `K_LL = I_3`, `K_DD = ‖ℓ‖² = 14.9665…`:
`Ξ_{NT→Reg} = ‖ℓ‖² − ℓ I_3 ℓᵀ = 0`. The full symmetric height-matrix
carrier is adequate for its regulator determinant at rank 2; the scalar
determinant alone leaves residual `3 − 1 = 2`.

### thm:apparatus:gram-matrix-shadow (NG-3)
For `r ≥ 2`, the Néron–Tate Gram matrix is a **noninjective public
shadow** of the rank-`r` motivic-cycle source: the Gram functor factors
through height-orthogonal changes of representatives, so distinct
motivic-cycle data (orientation, motivic labels, Abel–Jacobi
provenance) share the same Gram matrix. It supplies `Reg` once the MW
basis is known but does not construct the rank-`r` cycle source.
*Nonclaim:* NG-3 does not foreclose BDP / Beilinson–Kato / K_2(E) /
higher-Chow constructions (status `imported_under_hypotheses`); it only
forecloses treating the MW height matrix alone as a rank-`r` cycle
source.[^b60]

[^b60]: bsd_b60 (`bsd_b60_higher_rank_cycle_map.tex`, `bsd_b60_cycle_source_candidates.csv`, `bsd_b60_schur_residual_computation.csv`).

---

## §9. GlobalAuditNoGo — NG-4
Module: `SixBirdsBSD.Apparatus.GlobalAuditNoGo`. Source: bsd_b62.

### thm:apparatus:finite-window-no-go (NG-4)
For the conductor-colimit carrier
`C_BSD^{typed,+} = colim_{N_0→∞} {E/Q : cond(E) ≤ N_0}`, no
theorem-grade promotion from the b50 five-curve window
`W_50 = {11a1,37a1,121b1,960d1,571a1}` to the global typed predicate
`∀E/Q, BSD(E)` can depend only on the `W_50` rows. Schur form: at
conductor bound `B` with `M(B) = #C_BSD(B)`, `K_LL = I_5`,
`K_DD = I_{M(B)}`, `tr Ξ_B = M(B) − 5 → ∞` as `B → ∞`. Proof: two global
completions agreeing on `W_50` but differing at any `E_* ∉ W_50` are
indistinguishable to a `W_50`-only operator. Window evidence is
`moving_window_support_only`; closure needs a tail/exhaustivity
certificate or an audited density-to-pointwise bridge.[^b62]

[^b62]: bsd_b62 (`bsd_b62_global_audit_promotion.tex`, `bsd_b62_schur_residual_computation.csv`).

---

## §10. SupportPrimeNoGo — NG-5 + the support-prime atlas
Module: `SixBirdsBSD.Apparatus.SupportPrimeNoGo`. Source: bsd_b63.

Reduction classes: good ordinary (`a_p ≢ 0`) → R4a/ordinary-hyp; good
supersingular (`a_p ≡ 0`) → R4a/signed-hyp; multiplicative (`p|N`,
`v_p(c_4)=0`) → R4b unless L-invariant-covered; additive (`p|N`,
`v_p(c_4)>0`) → R4b case-by-case.

### thm:apparatus:finite-prime-cover-no-go (NG-5)
No fixed finite prime set certifies the all-prime support-prime carrier
`⊗_p Δ_f(M_E)_p`. Proof: for any finite `P_0`, choose `q ∉ P_0`; two
cover completions that agree on every prime of `P_0` but assign `q` a
covered vs an uncovered local row are indistinguishable to any
`P_0`-only operator, so it cannot determine the all-prime target. Hence
finite-prime evidence is non-exhaustive for Frontier 4, which requires
typed completed-coverage for the R4b residual class, not finite
enumeration.

### def:apparatus:support-prime-truncation-residual (finite diagnostic)
For a finite truncation `S_B = {p ≤ B}`, with an R4a row contributing no
residual and each R4b row one unit of unexplained local data, the
finite-truncation Schur residual is `Ξ_B(E) = u_B(E)` (the number of
R4b rows in `S_B`). This is a finite diagnostic and is **distinct from**
`thm:apparatus:finite-prime-cover-no-go`: by itself it does not prove
all-prime non-exhaustivity. b50 values below 50:
`Ξ(11a1) = Ξ(37a1) = Ξ(121b1) = 1`, `Ξ(960d1) = 3`, `Ξ(571a1) = 0`
(`571a1` becomes 1 with its bad prime 571 included).

### rmk:apparatus:support-prime-atlas (support_only)
The b63 76-row atlas of `(E,p)` classifications for the b50 curves
(reduction type; `a_p` by point counting; ordinarity;
IMC-applicability; R4a/R4b assignment). R4b rows below 50:
`11a1:{11}` (mult), `37a1:{37}` (mult), `121b1:{11}` (add),
`960d1:{2,3,5}` (add/mult), `571a1:∅` (bad prime 571 outside the `<50`
sample; b50 bad-prime R4b count 7). Support table, not a mechanized
theorem.[^b63]

[^b63]: bsd_b63 (`bsd_b63_support_prime_atlas.tex`, `bsd_b63_schur_residual_computation.csv`).

---

## §11. Vsrc — Non-Descending Translation calibration
Module: `SixBirdsBSD.Apparatus.Vsrc`. Sources: bsd_b67, bsd_b68, bsd_b69.

### def:apparatus:vsrc-algebra
For `E/Q` of rank `r`, `V_r = Q J_1 ⊕ … ⊕ Q J_r`,
`vsrc_r(E) = Λ_Q(V_r)` with `J_i² = 0`, `J_i J_j = −J_j J_i (i≠j)`,
unit 1. Each `J_i` is a non-descending symbol for the `i`-th virtual
independent motivic-cycle source class. (Exterior, not Clifford: the
rank-`r` source problem is determinant-shaped; `J_i² = 0` keeps
`J_1⋯J_r` as the independence witness. Cross-orientation: P-vs-NP's
`vobs` uses `J² = −I` for obstruction; `vsrc` uses the wedge for
adequacy.)

### thm:apparatus:vsrc-stage-i-consistency
Every element of `vsrc_r(E)` has a unique normal form
`a_∅·1 + Σ_{∅≠I⊆{1..r}} a_I J_I` (`J_I = J_{i_1}⋯J_{i_k}`, ordered),
so `dim_Q vsrc_r(E) = 2^r`; it is a consistent finite-dimensional
associative unital graded-commutative `Q`-algebra. Low-rank preserved:
`r=0 → vsrc_0 = Q`; `r=1 → Q ⊕ Q J_1`, `J_1² = 0`, with Stage-II
descent `J_1 ↦ P_K` (Heegner) under Gross–Zagier hypotheses.

### rmk:apparatus:vsrc-no-licensed-descent (support_only — typed-record predicate)
For `r ≥ 2`, the BSD-track records do not license a framework-internal
descent `vsrc_r(E) → CH^*(X)_Q` (or to any Selmer/MW carrier) realizing
all `J_i` as independent motivic classes. This is a **typed-record
predicate over the inherited ledger, not a mathematical non-existence
claim** and not a Lean-derivable theorem: such a descent would be new
external content relative to the recorded audits — bsd_b60 (Gram-shadow
no-go), bsd_b61 (Kato audit: no rank-`r` independent source classes),
bsd_b66 (BDP audit: motivic provenance but no two-class closure for
389a1). Mechanizable only as a finite record predicate
(`support_only`).[^b60][^b6166]

### thm:apparatus:vsrc-stage-ii-gz-partial
The `vsrc_1` calculus recovers the Gross–Zagier source/regulator side as
routine descent (`r_GZ(J_1) = P_K`, `h_vsrc(J_1,J_1) ↦ ⟨P_K,P_K⟩_NT`,
so `Reg = ⟨P_K,P_K⟩_NT`) but does **not** recover the full GZ identity
`L'(E/K,1)/Ω_{E,K} = c(E,K)⟨P_K,P_K⟩_NT` without importing the
analytic-height theorem. Residual
`Ξ_GZ = E_analytic_height_identity_import_GZ ≠ 0` for strict descent.

### thm:apparatus:vsrc-stage-iii-translation
For 389a1 (`r = 2`, `vsrc_2 = Q ⊕ Q J_1 ⊕ Q J_2 ⊕ Q J_{12}`,
`J_1 J_2 = J_{12}`): with the scalar residual `Ξ_Sc = 0 ⟺ A_lead =
Ω_E^+ Reg(E/Q)` (using `∏c_v = #Sha = |E_tors| = 1`) and the motivic
residual `Ξ_Mot = 0 ⟺ ∃` a realization `(r_2, z_{12}, B_an-ht^{(2)})`
with `z_{12} = r_2(J_{12}) ≠ 0` a rank-2 motivic wedge source: the
forward implication **`Ξ_Mot = 0 ⟹ Ξ_Sc = 0`** holds under the rank-2
analytic-height bridge `B_an-ht^{(2)}`. The **reverse implication is not
established** by the inherited records: the scalar formula does not
construct `z_{12}` nor certify its independence (the NG-3 obstruction),
so the converse requires the named external content `R_BSD→mot^{(2)}`
(not supplied by bsd_b60/b61/b66 or Stage II). This is a one-way
translation for the fixed 389a1 carrier, not a proven converse failure.
Named open content: `R_BSD→mot^{(2)}`, `B_an-ht^{(2)}`, and a `J_{12}`
independence certificate.[^b67][^b68][^b69]

### rmk:apparatus:vsrc-rank-r-stronger (support_only — framework interpretation)
The one-way Stage-III translation exposes that the scalar
leading-coefficient formula hides the rank-`r` motivic-cycle-existence
content carried by `J_1 ∧ … ∧ J_r`. The cascade reads this as
"rank-`r` BSD is logically stronger than its scalar statement";
recorded here as the framework interpretation of the Stage-III
asymmetry, **not** as an independently proven strict-stronger
meta-theorem, and not mechanized as one.

[^b67]: bsd_b67 (`bsd_b67_vsrc_stage_i.tex`).
[^b68]: bsd_b68 (`bsd_b68_vsrc_stage_ii_GZ.tex`).
[^b69]: bsd_b69 (`bsd_b69_vsrc_stage_iii_translation.tex`).
[^b6166]: bsd_b61 (Kato Euler-system audit) and bsd_b66 (BDP generalized-Heegner audit).

---

## §12. KappaNormalization — cascade form ≡ Strong BSD
Module: `SixBirdsBSD.Apparatus.KappaNormalization`. Source: bsd_b392.

### thm:apparatus:kappa-r-normalization-equivalence
Fixing the cascade convention `c_E := Tam(E) = ∏_ℓ c_ℓ(E)`, the
cascade conjecture form
`L^{(r)}(E,1)/r! = κ_r(E)·Ω_E·Reg_r(E)·c_E`
equals the standard BSD leading-coefficient formula
`L^{(r)}(E,1)/r! = Ω_E·Reg_r(E)·#Sha(E/Q)·Tam(E)/#E(Q)_tors²`
**iff** `κ_r(E) = #Sha(E/Q) / #E(Q)_tors²`. Under this canonical
normalization the cascade form is **provably equivalent** to the
standard Strong BSD identity — an equivalence of forms (after fixing
`c_E = Tam(E)`) restating the standard BSD identity in the cascade's
target coordinates; it does not derive the identity. *(Falsifiability anchors:
389a1 `κ_2 = 1` (`#Sha=1`, trivial torsion); 17127b1 `κ = 9`
(`#Sha=9`). Nonclaim: this does not prove the identity, only the
equivalence of the two forms.)*[^b392]

[^b392]: bsd_b392 (`bsd_b392_canonical_kappa_r_normalization.tex`); raw cascade conjecture form (`L^{(r)}/r! = κ_r·Ω·Reg·c_E`) from bsd_b346.

---

## Axis-level nonclaims

- The apparatus axis does **not** prove BSD (scalar or strong),
  Bloch–Kato, or ETNC.
- The five refined transports (`obl:apparatus:rho-*`) are
  out-of-scope-for-Lean recognition obligations; in Lean they are typed
  carriers / hypothesis parameters, never `axiom`s.
- Numerical BSD-prediction matches (11a1/37a1/389a1/…) are paper-side
  evidence, not Lean content.
- 571a1 is never used as a rank-2 height carrier (rank 0, nontrivial
  `Sha[2]`); rank-2 instances use 389a1.

---

## Revision history

- **rev1 (Phase B, post-external review).** Applied five prioritized fixes:
  (E1) corrected the analytic leading-term convention globally to
  `A_E = L^{(r_an)}(E,1)/r_an!` (removed the `L^*/r!` double-divide);
  (E2) split NG-5 (`thm:apparatus:finite-prime-cover-no-go`,
  all-prime two-completion) from the finite-truncation diagnostic
  (`def:apparatus:support-prime-truncation-residual`) and added
  `rmk:apparatus:support-prime-atlas`; (E3) downgraded the b58
  literature-gap to `rmk:apparatus:five-column-literature-gap`
  (`support_only`, b58 verdict mixed); (E4) renamed vsrc Stage III to
  `thm:apparatus:vsrc-stage-iii-translation`, replaced "converse fails"
  with "reverse implication not established," and split the
  "stronger-than-scalar" reading into
  `rmk:apparatus:vsrc-rank-r-stronger` (`support_only`); plus added
  b60/b61/b66 provenance to `vsrc-no-licensed-descent` (now `support_only`
  typed-record predicate), b346 lineage to κ, softened the κ "re-derives"
  wording, and added rfl-risk mechanization notes to the three
  identity-projection collapses (finite-source / ordinary / signed).

### intended_status summary (drives Phase C inventory)

- `mechanize_now`: all `def:apparatus:*` component maps + carriers; the
  Schur-collapse theorems (height, analytic, finite-source, ordinary,
  signed, rank-2-height, cascade-completion, comparison); the no-gos
  (component-killing, finite-scalar/scalar-finite shadow, dim-sha,
  gram-matrix NG-3, finite-window NG-4, finite-prime-cover NG-5); the
  vsrc algebra + stage-i/ii/iii theorems; the κ_r equivalence; the
  truncation-residual diagnostic.
- `support_only`: `rmk:apparatus:five-column-literature-gap`,
  `rmk:apparatus:support-prime-atlas`,
  `rmk:apparatus:vsrc-no-licensed-descent` (typed-record predicate),
  `rmk:apparatus:vsrc-rank-r-stronger`.
- `out_of_scope_recognition_source`: the five `obl:apparatus:rho-*`
  transports (typed carriers / hypothesis fields; never Lean `axiom`s).
