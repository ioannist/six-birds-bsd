# Closure axis (Paper B) — consolidated math (Phase A.3)

Consolidated, dependency-ordered, labeled statements-of-record for the
**conditional Strong-BSD closure + recognition sources + AOR realisability
instance** (the flagship). Binding source for the closure-axis Lean
mechanization (drives `closure_paper_inventory.toml` → `queue_closure.csv` →
`SixBirdsBSD.Closure.*`).

**What is mechanized (RH precedent, not needles):** the framework-structural
closure architecture only — the `Sel!_BSD` trace shell, `Π_BSD ⟺ Strong BSD`,
the `(ii)/(iii)/(ii)` composite signature, the AOR realisability instance, and
the *typing* of the recognition sources. The deep arithmetic is **never
mechanized**; it enters only as:
- **imported theorem `structure`s** (`χ_{CT,p}`/T_E1–T_E8, `A_E`, Beilinson
  rank-`≥2`) — proof-carrying records taken as hypotheses; and
- **recognition-source carriers** (`Γ_BSD^padic-descent`,
  `Γ_BSD^Sha-persistence`, `Γ_BSD^higher-GZ-fixity`) — typed `structure`s with a
  `Prop` field, declared inline next to their consumer, exactly as RH realizes
  `Γ_SDTC-Selberg`. **No project-local `axiom`/`opaque`/`sorry`; mathlib-free.**

The Phase-9 Strong-BSD landing is a **projection-packaged conditional**: Strong
BSD under the three recognition sources + the imported stack — explicitly NOT an
unconditional proof. Labels: `<kind>:closure:<short-name>`. Standing
conventions as in `apparatus_master.md` (`E/Q`, `M_E=h^1(E)(1)`, `r`, `r_an`).
The `κ_r` normalization is reused from
`thm:apparatus:kappa-r-normalization-equivalence` (b392), not re-mechanized.

> Mechanization discipline: recognition sources and imports are
> carriers/hypotheses, never derived; the
> AOR-instance discharges must route through the recognition/import records, not
> assert membership; the landing is conditional (hypothesis parameters), never
> `axiom`.

---

## §1. Imports — proof-carrying theorem structures
Module: `SixBirdsBSD.Closure.Imports`. Source: bsd_b294 (+ b266/b300 for A_E).
Each is a Lean `structure` with `Prop` fields; downstream theorems take it as a
hypothesis. Status `definition`, boundary `sourced_assumption`. Not derived.

### def:closure:chi-ct-p-import
The imported `χ_{CT,p}` theorem stack as a structure bundling the eight named
external theorems `T_E1..T_E8` (Sakamoto, Macias-Sano Thm 4.7(v), Knudsen,
Nekovář Astérisque 310 §10.8.7, Flach 1990, FSS Thm 5.2, …) as `Prop` fields,
plus the unconditional sign closure `Σ_{NekCT} = +1`. The carrier of the v5
comparison `χ_{CT,p}` (def C7) consumes this structure.

### def:closure:a-e-import
The `A_E` unified Selmer-complex pairing substrate (Nekovář Selmer complex with
intrinsic Cassels–Tate pairing; Burns–Flach–Macias-Sano–Nekovář ETNC-adjacent
`A_E^{Sel}` formulation, b266/b300) as a proof-carrying structure: a typed
target category with a bilinear/categorical pairing field. Hypothesis only.

### def:closure:beilinson-import
The Beilinson determinant / L-value comparison in rank `r ≥ 2` as a
proof-carrying structure (the archimedean regulator-to-determinant-line
identification used by the rank-`≥2` landing). Hypothesis only.

### nonclaim:closure:imports-not-derived
The import structures are sourced assumptions, not framework theorems; the BSD
closure derives consequences *from* them and never proves them. They carry no
project-local axioms.[^b294]

[^b294]: bsd_b294 (`bsd_b294_theorem_v5_final.tex`, `bsd_b294_closure_diagram.tex`); A_E substrate bsd_b266/b300.

---

## §2. RecognitionSources — typed carriers
Module: `SixBirdsBSD.Closure.RecognitionSources`. Sources: bsd_b710–b718.
Each `Γ_BSD^*` is **mechanized as a typed `structure` carrier** with a `Prop`
predicate field (intended status `mechanize_now`, as in the corresponding RH
carrier), but its **arithmetic content is a recognition
source** — formed-layer closure content, not framework-primitive derivable,
consumed only as a hypothesis (SoR `lean_coverage = recognition_source`). With
Foundations-IV instantiations and the Stage-6 trace signature
`FP→(ii), SAU→(iii), VDE→(ii)`. Never an `axiom`.

### def:closure:gamma-padic-descent
`Γ_BSD^padic-descent` (D_3''' additive-prime p-adic descent). For `E/Q`, odd
additive prime `p` with shallow Kodaira II/III, `c_p(E) ∈ {1,2}`, `p ∤ c_p(E)`,
`Sha(E/Q)[p^∞]=0`, and a finite tame inertia-trivializing `L/Q_p`: the formed
local layer carries an OC descent comparison
`descent_p^OC : LC_triv(L_p^OC(E_L)) → LC_triv(L_p^OC(E))` and a unit
`ε_p(E,L) ∈ Z_p^×` with
`LC_triv(L_p^OC(E)) ≡ c_p(E)^{-1}·ε_p(E,L)·descent_p^OC(LC_triv(L_p^OC(E_L))) (mod Z_p^×)`.
Foundations IV: F2 Descent-Repair (`c_p` is the minimal coarsening), F3
Holonomy-Memory (`ε_p` is the recorded route residue), F4 Local-Global.
Anchors: 49a1@7, 36a1@3, 121b1@11.

### def:closure:gamma-sha-persistence
`Γ_BSD^Sha-persistence` (D_2''' signed-Selmer corestriction). For `E/Q`,
HPS2-passing additive prime `p`, tame inertia-trivializing `L/Q_p`: the
signed-Selmer persistence layer carries the cover-change determinant
`C_loc^III(E,p) := det(cores_{L/Q_p} ∘ signed_local_pairing_p(E,L))`, and the
predicate asserts `C_loc^III(E,p) ≡ c_p(E) (mod Z_p^×)`. Foundations IV: F19
Object Persistence, F21 Reflexive Nonclosure, F29 Presentation Invariance.

### def:closure:gamma-higher-gz-fixity
`Γ_BSD^higher-GZ-fixity` (D_2'' rank-`r` archimedean fixity). For non-CM `E/Q`
of analytic rank `r ≥ 2`, the formed rank-`r` arithmetic/analytic duality layer
has anti-invariant readout
`ψ_-(E,r) = L^{(r)}(E,1)/r! − κ_r(E)·Reg_NT(E)·Ω_E·Tam(E)`, and the predicate
asserts the higher-GZ fixity `ψ_-(E,r) = 0` (equivalently
`L^{(r)}(E,1)/r! = κ_r(E)·Reg_NT(E)·Ω_E·Tam(E)`). Foundations IV: F14 Duality
Fixity (`J(A,R)=(R,A)`, `ψ_-=A−R`), F27 Conservation as Orbit Descent
(`Reg_NT=det⟨P_i,P_j⟩` over the `GL_r(Z)` orbit), F40 Anomaly/Symmetry
Obstruction. Anchors: 389a1 (r=2) … 19047851a1 (r=5).

### nonclaim:closure:recognition-sources-not-derived
Each `Γ_BSD^*` is formed-layer closure content named as an accepted recognition
source, not framework-primitive derivable; in Lean it is a typed carrier taken
as a hypothesis, never an `axiom`. Each records a `(ii)/(iii)/(ii)`
trace-state-only Stage-6 signature.[^b710][^b713][^b716]

[^b710]: bsd_b710–b712 (`bsd_b710_gamma_padic_descent_predicate.md`, F2/F3/F4 instantiations, admissibility + closure-content thesis, anchor/operational catalogs).
[^b713]: bsd_b713–b715 (`bsd_b713_gamma_sha_persistence_predicate.md`, F19/F21/F29, catalogs).
[^b716]: bsd_b716–b718 (`bsd_b716_gamma_higher_gz_fixity_predicate.md`, F14/F27/F40, catalogs).

---

## §3. SelShell — the closure architecture
Module: `SixBirdsBSD.Closure.SelShell`. Sources: bsd_b719–b721.

### def:closure:sel-bsd-shell
The saturated BSD trace shell is the tuple (b719)
`Sel!_BSD = (E, ρ_E, J!_BSD, Vis!_BSD, Audit!_BSD)`, where the residual is
`ρ_E = L^{(r)}(E,1)/r! − #Sha·Reg_NT·Ω·Tam / |E(Q)_tors|^2`, `J!_BSD` is the
involutive/duality datum, `Vis!_BSD` the visible-readout datum, and `Audit!_BSD`
the audit-record datum; it is the formed-layer closure object for the Strong-BSD
identity, with admissibility, anti-tautology, and lawfulness data, constructed
under the standard Foundations-I closure assumption.

### def:closure:pi-bsd
The predicate `Π_BSD(E)` on `Sel!_BSD` is the **conjunction of the three BSD
recognition-source readouts**, properly quantified over the local data (b719):
- `Γ_BSD^padic-descent`: the local-descent/Tamagawa correction in the p-adic
  L-function norm layer, **for every additive bad prime `p` and every finite
  tame inertia-trivializing lift `L/Q_p` in scope**;
- `Γ_BSD^Sha-persistence`: the signed-Selmer local determinant/component matching
  **for every signed-Selmer-admissible (HPS2-passing) prime `p`**;
- `Γ_BSD^higher-GZ-fixity`: the rank-`r` GZ-fixity readout `ψ_-(E,r)=0` for
  `r ≥ 2`, **together with the lower-rank analog lane for `r ∈ {0,1}`** (where
  the archimedean side is classical / Gross–Zagier).
A structured, quantified predicate over the recognition readouts — not
`def Π_BSD := StrongBSD`.

### thm:closure:pi-bsd-iff-strong-bsd
**Readout-level equivalence** (b719 stage 2, b720): `Π_BSD(E)` holds at the
readout level iff the standard Strong-BSD scalar identity holds — the scalar
readout of `Sel!_BSD` is *exactly the same* as
`L^{(r)}(E,1)/r! = #Sha·Reg_NT·Ω_E·∏_v c_v / |E(Q)_tors|^2`, "readout-equivalent
but not definitionally identical". Mechanized as a **scalar-readout
equivalence** (a `readout(Π_BSD) = StrongBSD-scalar` theorem), NOT a full
predicate `iff`: the reverse direction must not manufacture the `Γ_BSD^*`
predicates from the scalar identity.

### thm:closure:master-theorem-applicability
The closure master-theorem applies to `Sel!_BSD`, established via the
**Foundations-IV applicability audit** of the recognition sources' instantiations
(F2/F3/F4 for `Γ_BSD^padic-descent`, F19/F21/F29 for `Γ_BSD^Sha-persistence`,
F14/F27/F40 for `Γ_BSD^higher-GZ-fixity`; b720 stage 3), and the **smuggle
audit** passes (no out-of-scope content is silently used as a derivation
target; b720 stage 4).

### thm:closure:composite-signature
The composite operational predicate `P_op^BSD-composite` carries the Stage-6
trace signature `FP→(ii), SAU→(iii), VDE→(ii)`. The **BSD track is the third
cross-track `(ii)/(iii)/(ii)` trace-state instance** (after P-vs-NP and RH); the
three `Γ_BSD^*` are its BSD-internal recognition signatures (recorded overall as
the 3rd/4th/5th such instances), and `P_op^BSD-composite` composes them.
**Stage-5 anti-tautology hardening (b721):** `P_op^BSD-composite` is
**computable** and **falsifiable**, carries **genuine dependence** on the formed
BSD layer's data, and the three recognition components are **independent but not
disposable** (ablation of any one breaks the Strong-BSD scalar factor package) —
so the predicate cannot collapse into a tautological restatement of Strong BSD.
Mechanized so the composite genuinely consumes all three recognition records (an
ablation/non-disposability obligation), not a packaged conjunction.[^b719][^b720][^b721]

[^b719]: bsd_b719 (`bsd_b719_stage1_BSD_closure_layer.md`, `bsd_b719_predicate_Pi_BSD.md`).
[^b720]: bsd_b720 (`bsd_b720_stage3_applicability_audit.md`, `bsd_b720_stage4_smuggle_audit.md`).
[^b721]: bsd_b721 (`bsd_b721_P_op_BSD_composite_construction.md`, `bsd_b721_stage5_anti_tautology_hardening.md`, FP/SAU composite verdict proofs).

---

## §4. ChiCTp — the Cassels–Tate Pfaffian comparison (supporting)
Module: `SixBirdsBSD.Closure.ChiCTp`. Source: bsd_b294.

### thm:closure:chi-ct-p-comparison
Self-dual √-Fitting-to-CT-Pfaffian comparison theorem (v5). For `E/Q` with
finite `Sha(E)[p^∞]`, nondegenerate CT pairing, standard
Sakamoto/Macias-Sano Selmer-complex hypotheses, `p ∤ Tam(E/Q)`: conditional on
the `def:closure:chi-ct-p-import` structure (`T_E1..T_E8`), there is a canonical
orientation-respecting Pfaffian map
`Pf_{Nek,p}^{or,√} : √Fitt_CT(H^1(C_p(E))/div, U_{2,2}) → vctp_p` (the square-root
Fitting ideal on the divisible-subgroup quotient `H^1(C_p(E))/div`, paired by the
Nekovář cup-product `U_{2,2}` identified with the Flach pairing) sending the
square-root Stark generator `√F_E^p` to `h_p^{CT}(E)`, with unconditional sign
closure `Σ_{NekCT} = +1` on the named papers. Mechanized as: given the import
structure, the comparison map exists and the sign is `+1` (conditional theorem;
the import is the hypothesis).[^b294]

---

## §5. EtaFormula — conditional overconvergent η-formula (supporting)
Module: `SixBirdsBSD.Closure.EtaFormula`. Source: bsd_b664→b694.

### def:closure:eta-published-imports
The published-import structure for the OC `η`-formula, as proof-carrying fields,
with the distinct imports kept separate: Bellaïche Lemma 3.21; Pollack–Stevens
2011; **arXiv:2403.16076** ("Arithmetic of critical p-adic L-functions");
**Lang–Wake 2025, arXiv:2501.04162** (a distinct import from arXiv:2403.16076 —
do not conflate); Lorenzini 1995; Ling 1997; plus the single cascade-internal
conjecture `C_B691_CUSPIDAL_LAYER_EVALUATION_NONZERO_AND_PRIMITIVE`.

### thm:closure:oc-eta-formula
Conditional unified OC `η`-formula at additive odd primes. For `E/Q` in the
**Phase-7-S/T shallow additive odd-prime scope** (the HPRCM prime-square class
*plus* the verified multi-prime extension, e.g. `36a1@3`), `p` odd additive,
`β` the Bellaïche critical-slope
stabilization (`β² = −p`), `T_leading_Bellaïche(E,p)`, `ord_T(E,p)`: conditional
on `def:closure:eta-published-imports`,
`η_p(E) = (p·|E(Q)_tors|)^{ord_T(E,p)−1}·β^{−2}·T_leading_Bellaïche(E,p)`.
Verified at anchors 49a1@7 (`η=−2`), 36a1@3 (`η=+2`), 121b1@11 (`η=−1`).
State-2 conditional; mechanized as the conditional identity under the import
structure (the 3-anchor evidence is paper-side, not Lean).[^b694]

[^b694]: cluster Phase-7-S/T b664→b694 (`bsd_b694_unified_cascade_theorem.md`); D_2''' extension b696–b700.

---

## §6. TCascade — conditional p-part SBSD rank ≤ 1 (supporting)
Module: `SixBirdsBSD.Closure.TCascade`. Sources: bsd_b312, b315.

### def:closure:t-cascade-import
The named external theorem stack for `T_CASCADE` as a proof-carrying structure:
`T_E1..T_E8 + T_CM1..T_CM6 + T_SS1..T_SS7 + T_ARC1..T_ARC6 + T_UNI1..T_UNI7`
(CM branch); `T_nC1..T_nC6` (Skinner-Urban, Wei Zhang, Burungale-Skinner,
CHKLL, Yan-Zhu, Loeffler-Pilloni) for the non-CM branch. Hypothesis only.

### thm:closure:t-cascade-rank-le-1
Conditional p-part Strong BSD for rank ≤ 1.
- **CM branch** (b312): CM `E/Q` with (Ord-Split) good ordinary `p` split in `K`
  OR (SS-Inert) good supersingular `p` inert in `K`, `p ≥ 5`; (H1) `Sha[p^∞]`
  finite, (H2) CT nondegenerate, (H3) Sakamoto/Macias-Sano Selmer-complex
  hypotheses + `p ∤ Tam`, (H4) ramification, (HARC) Heegner for `r=1`, (HU) CM
  Galois-image standard; under the CM import stack.
- **non-CM branch** (b315): non-CM `E/Q` with `r ∈ {0,1}`, surjective `ρ_{E,p}`
  (almost all `p` by Serre), good ordinary `p`, `p ∤ N`, `p ∤ Tam`; the **standard
  Skinner–Urban ordinary local, residual-irreducibility, ramification, and level
  hypotheses**; `Sha[p^∞]` finite; CT nondegenerate; the Sakamoto/Macias-Sano
  hypotheses of b294; and a Heegner field satisfying the Gross–Zagier–Kolyvagin
  hypotheses **only when `r = 1`**; under the non-CM import stack.
Then `v_p(L^{(r)}(E,1)/(r!·Ω·R)) = v_p(#Sha·Tam/#tors^2)`. Conditional on
`def:closure:t-cascade-import`; mechanized as the conditional valuation identity
(empirically verified on anchors — paper-side).[^b312][^b315]

[^b312]: bsd_b312 (`bsd_b312_T_CASCADE_theorem.tex`, proof sketch); composed from b294/b296/b298/b299/b308.
[^b315]: bsd_b315 (`bsd_b315_T_CASCADE_nonCM.tex`).

---

## §7. Obstructions — typed no-gos + Mode-B residuals
Module: `SixBirdsBSD.Closure.Obstructions`. Sources: bsd_b317, b320, b336/b337/b341.

### thm:closure:t-e12-no-go
`T_E12_REFINED`: no theorem-grade peer-reviewed identity of the form
`L^{(r)}(E,1)/r! = κ_r·det⟨Z_i,Z_j⟩_NT·Ω_E·c_E` (explicit cycles `Z_i`,
closed-form `κ_r,c_E`) exists in the audited Mode A literature for non-CM `E/Q`
with `r ≥ 2` — the missing rank-`r` generalized Gross–Zagier identity. Audit
result: the **six audited Mode A approaches** at b317 converge on this gap
(later extended to eight via b323/b329); **not** a non-existence claim. Mechanized as
a typed-record predicate over the audited-literature ledger (support; the
Yun–Zhang function-field/number-field gap is the symmetry-descent anomaly).

### thm:closure:t-bad-no-go
`T_BAD_REFINED`: no theorem-grade direct additive-prime IMC exists in the
audited Mode A literature for `E/Q` additive at `p ∈ {2,3}` with explicit local
correction factors and characteristic-ideal equality. 4 sub-residuals
(R_BAD_a..d) + Kodaira HPS2 screen (FAIL vs descent-gap). Audit-result typed
no-go; mechanized as a typed-record predicate (support).

### rmk:closure:mode-b-residuals
The Mode-B binding residuals `D_2''` (vahb_r rank-`r` open), `D_2'''`
(signed-Selmer corestriction), `D_3'''` (p-adic L norm identity) are the
cascade-internal reorganizations the recognition sources discharge; recorded as
support-only typed-open content (the recognition sources of §2 are their
discharge).[^b317][^b320][^b336]

[^b317]: bsd_b317 (`bsd_b317_T_E12_REFINED_typed_no_go.tex`); extended b323/b329.
[^b320]: bsd_b320 (`bsd_b320_T_BAD_REFINED_typed_no_go.tex`); extended b324/b325.
[^b336]: bsd_b336 (`bsd_b336_MODE_B_T_E12_STATUS.tex`); b337/b341.

---

## §8. Landing — the Phase-9 conditional Strong-BSD closure
Module: `SixBirdsBSD.Closure.Landing`. Source: bsd_b722.

### thm:closure:strong-bsd-conditional
**Conditional Strong BSD.** Take as hypotheses: the standard Foundations-I
closure assumption for `Sel!_BSD`; the three recognition sources
`def:closure:gamma-padic-descent`, `def:closure:gamma-sha-persistence`,
`def:closure:gamma-higher-gz-fixity`; and the import structures
`def:closure:chi-ct-p-import`, `def:closure:a-e-import`,
`def:closure:beilinson-import`. Then, via `thm:closure:pi-bsd-iff-strong-bsd`,
`thm:closure:master-theorem-applicability`, and `thm:closure:composite-signature`,
the Strong-BSD identity holds for `E/Q`:
`L^{(r)}(E,1)/r! = #Sha(E/Q)·Reg_NT(E)·Ω_E·∏_v c_v(E) / |E(Q)_tors|^2`.
Outside Six Birds: `(Γ¹ ∧ Γ² ∧ Γ³ ∧ χ_{CT,p}-imports ∧ A_E-imports ∧ Beilinson-rank≥2-imports) ⟹ Strong BSD`.
Mechanized as a theorem with all of the above as explicit hypothesis
parameters (a projection-packaged conditional landing — genuine implication
chain through the SelShell theorems, never an `axiom`).

### nonclaim:closure:landing-conditional
This is **not** an unconditional classical proof of BSD. It is theorem-grade
within the Six Birds closure discipline, conditional on the named recognition
sources and imports. `T_E12_REFINED` (rank-`≥2` GZ) and `T_BAD_REFINED`
(additive `p≤3` IMC) remain genuinely open in the literature.[^b722]

[^b722]: bsd_b722 (`bsd_b722_BirdInt_judgment_final.md`, `bsd_b722_block_4_cascade_grade_assembly.md`); seven-stage provenance b719→b722.

---

## §9. AORInstance — "BSD as an AOR instance" (connect to reality)
Module: `SixBirdsBSD.Closure.AORInstance` (+ `AORPrimitives`). Sources:
bsd_b710–b722 + `TsiokosAOR2026`. Mirrors the RH track's `RH/AORInstance`.

### def:closure:aor-sel-instance
The AOR-instance object attached to `Sel!_BSD`: its membership witness is the
bundle of closure records — the mechanical components (the `Sel!_BSD`
construction, the `κ_r` normalization, the import structures as an
`approved_other` citation chain) and the substantive recognition-source
discharges. Built on the AOR primitives imported from `TsiokosAOR2026`
(refinement-stable membrane / structural-defect / discharge-atom vocabulary).

### thm:closure:aor-mechanical-records
The mechanical membership components discharge `by_construction` /
`approved_other`: the `Sel!_BSD` construction and `κ_r` normalization
(`by_construction`); the `χ_{CT,p}` / `A_E` / Beilinson import structures as an
`approved_other` external-record citation chain.

### thm:closure:aor-recognition-discharge
The three recognition sources discharge as bridged recognition-source records:
each `Γ_BSD^*` is typed primary `Δ_source` (with forced secondary
`Δ_role/Δ_target/Δ_transport/Δ_limit`) and discharged by a bridged record — not
eliminated. (Mechanized as three discharge components routing through the §2
carriers.)

### thm:closure:aor-instance
`Sel!_BSD` is `RefStableAOR` (refinement-stable audit-closed) under the declared
presentation: the BSD carrier's declared audit records discharge the structural
defects that remain under refinement. This is the framework's "Strong BSD holds
in reality" statement — **non-eliminative** (the recognition records are
reclassified, not discharged of their open arithmetic). Depends on
`thm:closure:aor-mechanical-records` + `thm:closure:aor-recognition-discharge`.

### rmk:closure:aor-partial-status
The AOR-instance reading does not close the open obligations; it records that
the BSD carrier is audit-closed under the declared refinement-stable AOR
presentation, with the recognition records reclassified rather than discarded.

---

## Axis-level nonclaims

- The closure axis does **not** prove BSD unconditionally; the landing is a
  conditional closure within Six Birds.
- Recognition sources (`Γ_BSD^*`) and imports (`χ_{CT,p}`/`A_E`/Beilinson) are
  typed carriers / proof-carrying hypothesis structures — never Lean `axiom`s,
  never derived.
- `T_E12_REFINED` / `T_BAD_REFINED` are audit-result typed no-gos (the rank-`≥2`
  GZ identity and additive `p≤3` IMC are genuinely open), not proved.
- Empirical anchor verifications (30-digit, ranks 0–5, etc.) are paper-side
  evidence, not Lean content.
- The AOR instance is non-eliminative.

## intended_status summary (drives Phase C inventory)

- `mechanize_now`: `chi-ct-p-import`, `a-e-import`, `beilinson-import`,
  `eta-published-imports`, `t-cascade-import` (import structures, status
  `definition`, boundary `sourced_assumption`); `sel-bsd-shell`, `pi-bsd`,
  `pi-bsd-iff-strong-bsd`, `master-theorem-applicability`, `composite-signature`;
  `chi-ct-p-comparison`, `oc-eta-formula`, `t-cascade-rank-le-1`;
  `strong-bsd-conditional`; the AOR `def:closure:aor-sel-instance`,
  `aor-mechanical-records`, `aor-recognition-discharge`, `aor-instance`.
  Plus the three recognition-source **carriers** `gamma-padic-descent`,
  `gamma-sha-persistence`, `gamma-higher-gz-fixity` — `mechanize_now` as typed
  `structure`s, but with SoR
  `lean_coverage = recognition_source` and `semantic_alignment` recording that
  the arithmetic Prop content is a hypothesis (out of scope), not derived.
- `out_of_scope_recognition_source` (pure obligations, NOT created in Lean):
  none on this axis — the closure recognition sources are mechanized as carriers
  (above), unlike the apparatus axis's five `rho_*` transports.
- `support_only`: `t-e12-no-go`, `t-bad-no-go`, `mode-b-residuals`,
  `aor-partial-status` (audit/ledger/interpretation).
- `nonclaim`: `imports-not-derived`, `recognition-sources-not-derived`,
  `landing-conditional`.

---

## Revision history

- **rev1 (Phase B, post-external-review REVISE).** Applied the prioritized fixes
  after cross-checking the primary artifacts: (1) `Π_BSD` restated as the
  conjunction of recognition-source readouts and `pi-bsd-iff-strong-bsd`
  downgraded to a **readout-level** equivalence (b719 stage 2 / b720), not a full
  predicate `iff`; (2) OC `η` imports separated (`arXiv:2403.16076` ≠ Lang–Wake
  2025) and scope widened to the full Phase-7-S/T (HPRCM prime-square + multi-prime
  extension); (3) Beilinson rank-`≥2` imports added to the outside-SB implication
  (b722); (4) `T_E12_REFINED` corrected to **six** audited Mode A approaches
  (b317; extended to eight via b323/b329); (5) `χ_{CT,p}` map domain corrected to
  `√Fitt_CT(H^1(C_p(E))/div, U_{2,2})` (b294); (6) `master-theorem-applicability`
  restated as the Foundations-IV applicability audit (F2/F3/F4, F19/F21/F29,
  F14/F27/F40) + smuggle audit (b720); (7) `composite-signature` corrected to
  **third cross-track** trace-state instance; (8) `rem:` → `rmk:` for
  `aor-partial-status`; (9) Γ-source intended status clarified — **mechanize the
  typed carrier** (`mechanize_now`), arithmetic content is the recognition source
  (`lean_coverage = recognition_source`, hypothesis, out of scope). Dependency
  map updated: C4 cites `bsd_b719_stage2_translation_theorem.md`; C13 cites
  `bsd_b722_strong_BSD_theorem_statement.md` + `bsd_b722_strong_BSD_proof_via_seven_stages.md`.
- **rev2 (Phase B, second-review REVISE — mechanization gaps).** (1) Expanded
  `sel-bsd-shell` with the exact b719 tuple `Sel!_BSD = (E, ρ_E, J!, Vis!,
  Audit!)` and `ρ_E = L^{(r)}/r! − #Sha·Reg·Ω·Tam/|tors|^2`; (2) expanded
  `pi-bsd` with the b719 quantifiers (all additive bad primes/inertia lifts, all
  signed-Selmer-admissible primes, and the `r∈{0,1}` lower-rank analog lane);
  (3) hardened `composite-signature` with the b721 Stage-5 anti-tautology
  (computable / falsifiable / genuine dependence / non-disposable ablation),
  added `bsd_b721_stage5_anti_tautology_hardening.md`; (4) restored the full b315
  non-CM hypotheses (Skinner–Urban local/residual/ramification/level, Sha
  finiteness, CT nondegeneracy, Sakamoto/Macias-Sano, `r∈{0,1}`, Heegner iff
  `r=1`) in `t-cascade-rank-le-1`; (5) dependency-map metadata: C1–C3 marked
  `mechanize_now` carriers (lean_coverage `recognition_source`), C0 cites
  `bsd_b300_A_E_target_category.tex`, C6 cites the Stage-5 file.
