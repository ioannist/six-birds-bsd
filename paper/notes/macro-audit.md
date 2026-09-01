# Macro audit (both papers)

*Phase 1 deliverable. Closed 2026-05-29. Consolidated macro list with
per-paper coverage. The canonical macro definitions live in
`paper/<axis>/includes/paper_macros.tex`, `\input` by each modular
`main.tex` preamble (the `sections/` + `appendices/` scaffold shares the
one macro file). Reserved-symbol policy is binding on Lean naming
(`paper/notation_and_terminology.md`).*

This table mirrors the two `paper/<axis>/includes/paper_macros.tex` files
verbatim — every macro listed here is defined there, and vice versa.

## Shared / framework macros (identical block in both papers)

| macro(s) | renders | meaning |
|---|---|---|
| `\Q \R \Z \Qp \Zp` | `\mathbb{Q}` … `\mathbb{Z}_p` | number sets |
| `\Sha \Reg \Tam \tors` | `\operatorname{Sha}` … | BSD quantities |
| `\tr \Pf` | `\operatorname{tr}`, `\operatorname{Pf}` | trace, Pfaffian |
| `\Fitt \cores` | `\operatorname{Fitt}`, `\operatorname{cores}` | algebraic |
| `\rank \Hf` | `\operatorname{rank}`, `H^1_f` | rank, finite local condition |
| `\kapr` | `\kappa_r` | normalization constant (apparatus-defined; Paper B reuses) |

## Paper A (apparatus) macros

| macro | renders | meaning |
|---|---|---|
| `\XiC` | `\Xi_C(D\mid L)` | adequacy / Schur residual |
| `\KDD \KDL \KLL` | `K_{DD}`, `K_{DL}`, `K_{LL}` | Gram blocks |
| `\Kdagger` | `K_{LL}^{\dagger}` | pseudo-inverse block |
| `\vsrc` | `\mathrm{vsrc}` | exterior-algebra calibrator |
| `\Jone \Jtwo \Jtwelve` | `J_1, J_2, J_{12}` | wedge generators |
| `\MCphi` | `M_C^{\varphi}` | typed column (Lean `M_C_phi`) |

## Paper B (closure) macros

| macro | renders | meaning |
|---|---|---|
| `\Sel` | `\operatorname{Sel}` | Selmer base |
| `\SelBSD` | `\mathrm{Sel}^{!}_{\mathrm{BSD}}` | the trace shell |
| `\rhoE` | `\rho_E` | shell residual |
| `\PiBSD` | `\Pi_{\mathrm{BSD}}` | recognition predicate |
| `\GammaPD \GammaSP \GammaGZ` | `\Gamma_{\mathrm{BSD}}^{\mathrm{padic\text{-}descent}}` etc. | three recognition sources |
| `\chiCTp` | `\chi_{CT,p}` | Cassels–Tate comparison |
| `\AofE` | `A_E` | Selmer-complex pairing substrate (named `\AofE`, **not** `\AE`, which is the reserved Æ ligature) |
| `\etap` | `\eta_p` | OC eta |
| `\RefStable` | `\mathbf{RefStable\,AOR}` | AOR membership |

Paper B also has the full shared block (including `\kapr`, reused from
Paper A's `κ_r` normalization).

## Coverage / policy

- Every macro above is defined in `paper/<axis>/includes/paper_macros.tex`,
  `\input` by the modular `main.tex` preamble; no macro is used before
  definition. The shared block is byte-identical in both files.
- Subscript/superscript names map 1-to-1 to Lean identifiers
  (`M_C^φ → M_C_phi`).
- No macro collides with a built-in LaTeX command or with a reserved
  symbol in `paper/notation_and_terminology.md` (the `A_E` substrate is
  `\AofE`, avoiding the `\AE` ligature clash).
