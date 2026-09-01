# Proof-presentation policy (both papers) — companion form

*Phase 6 deliverable. Closed 2026-05-29; reauthored 2026-05-29 to the
**companion form** (deliberate divergence from the sibling plans, which
produced Lean-heavy "manual" papers). Governs where each statement's
argument lives and how its mechanization is disclosed. Keyed to
`statements-of-record.yml` (`proof_presentation`, `lean_coverage`,
`semantic_alignment`) and the per-label table in
`mechanization-rebinding-policy.md`.*

## The target shape (companion form)

Three layers, each with one job, none doing the others':

1. **Body = a self-contained math paper.** A reader who skips every
   footnote still gets a complete, verifiable mathematical argument.
2. **Footnotes = the mechanization existence claim**, at honest fidelity,
   one per theorem (and per non-trivial definition).
3. **One appendix (App D) = the disclosure mechanics** — the full
   paper-label → Lean-decl → coverage/alignment table, the narrowing
   disclosures, the projection-vs-derivation distinction, the trust base.

The failure modes this rules out: **(A)** stripping the mechanization (the
body no longer answers "how do we know this is correct?" — dishonest);
**(B)** scattering Lean through the body (a manual for the code, not a math
paper — unreadable). Companion form serves both audiences and misleads
neither.

## 1. The body is math first

- Every load-bearing concept gets a formal environment (`definition`,
  `theorem`, `lemma`, `proposition`). A central object that exists only as
  a prose paragraph is a failure — promote it.
- **Every body theorem gets a full proof** — hypotheses unpacked, cases
  enumerated, conclusion derived as standard mathematical prose. No sketch
  that defers to the mechanization ("Lean proves the rest"). The reader of
  the body never needs the Lean code to verify the argument.
- Where the argument leans on a classical result (an imported theorem
  stack), **cite it as a one-line input** — do not reprove it, do not
  sketch it, do not pretend the framework derives it. The body proof is
  complete *given* those cited inputs.
- **No operational vocabulary in body prose**: no Lean module paths, no
  structure/record field names, no tactic talk, no narrowing-disclosure
  sentences ("the Lean realization carries…", "the formalization harness
  tracks…", "App D records this narrowing"). Body prose uses paper-prose
  names ("the saturated trace shell", "the recognition source", "the
  readout equivalence").

## 2. Mechanization disclosure = one footnote per theorem

After a theorem's proof, exactly **one footnote** carrying the existence
claim + the Lean decl + an App-D pointer. The footnote **wording is fixed
by coverage type and is canonical, not editorial** — calling a projection
schema a "Lean proof" misrepresents the work and a careful reviewer will
catch it.

| SoR coverage / alignment | Footnote wording (template) |
|---|---|
| **`lean_substantive`** (theorem, `faithful`) | "Verified in Lean as `[decl]`; see App~D." |
| **`lean_substantive`** (definition, `faithful`, non-trivial realization) | "Realized in Lean as `[decl]`; the typed record exposes [fields]. See App~D." |
| **`narrowed_surrogate`** (theorem/def) | "Verified in Lean as `[decl]` over a narrowed representation (the [X] narrowing — e.g. the `2^r` coordinate space; the local syntactic predicate); the narrowing is recorded in App~D." The narrowing qualifier is **mandatory** — never bare "verified in Lean". |
| **`projection_packaged`** (theorem) | "Tracked in the formalization harness as a conditional schema `[decl]` — a checked projection over an explicit proof-carrying record (conditional on the imported stack / recognition sources), **not** an independent Lean derivation. See App~D." Must **not** say "Lean proves". |
| **`typed_structure_carrier`** (imports) | "Encoded in Lean as a typed structure carrier `[decl]` bundling the imported theorem as a hypothesis field; **not** a Lean axiom. See App~D." |
| **`typed_structure_carrier`** (recognition source) | "Supplied as a recognition source, encoded in Lean as a typed structure carrier `[decl]` (its arithmetic content is a hypothesis field; **not** a Lean axiom). See App~D." |
| **`support_only`** / nonclaim / obligation | **No footnote.** No Lean identifier in body prose. (Obligations, if cited, read "recorded as a manifest obligation"; the item otherwise appears only in App~D / as paper-prose motivation.) |

- A pure typed-mirror definition (faithful, trivial realization) needs **no
  footnote** — the App~D table is enough.
- The footnote's coverage qualifier must match the row's
  `lean_coverage`/`semantic_alignment` in `statements-of-record.yml`
  (source of truth); App~D is generated against that file, so every body
  footnote claim is checkable.

## 3. App D is the canonical disclosure venue

- App~D carries the full mapping table — paper label, paper-prose name,
  Lean decl path, coverage/alignment, footnote-wording rule, body location
  — plus the narrowing-disclosure prose, the projection-vs-derivation
  distinction, the Lean module hierarchy, and the axiom-audit trust base.
  The per-label assignment is `mechanization-rebinding-policy.md`; the
  representation-disclosure notes there move **into App~D**, not into body
  prose.
- Body footnotes point **at** App~D; they do not duplicate it. The footnote
  says "see App~D"; App~D says specifically what is narrowed and how.

## 4. What stays / moves / disappears

- **Stays in body:** all mathematical content — statements, full proofs,
  definitions, mathematical commentary, scope discussion, conceptual
  motivation, comparison to classical results.
- **Moves to footnote:** the mechanization existence claim, the Lean decl,
  the coverage qualifier (one footnote per theorem / non-trivial def).
- **Moves to App~D:** narrowing-disclosure prose, parametric-hypothesis
  disclosure, projection-vs-derivation distinction, module hierarchy,
  trust base, narrowing-detail tables.
- **Disappears from the body entirely:** "The Lean realization carries…",
  "the formalization harness tracks…", "App~D records this narrowing", and
  every other sentence that talks *to the code* rather than to a
  mathematician.

## 5. Hard rules

- Long Lean identifiers (`SixBirdsBSD.…`) appear **only** in footnotes and
  App~D tables, never in running body prose.
- A `projection_packaged` claim is never worded as a Lean proof, in body or
  footnote; its conditionality is stated in the footnote.
- A `narrowed_surrogate` claim always carries its narrowing qualifier in
  the footnote; never bare "verified in Lean".
- No body-prose `axiom`/`opaque`/`constant`/trust-base names; the trust
  base is discussed only in App~D methodology.
- Self-referential framework prose ("our framework", "the present
  construction records") is restrained to the scope/discussion sections.

## 6. The three-layer test (apply at per-paper polish)

1. **Body, footnotes hidden** → reads as a self-contained math paper?
2. **Footnotes alone** → describe what is mechanized, at what fidelity,
   with the correct wording per coverage type?
3. **App~D** → a complete table from paper claim to Lean identifier with
   status?

All three green ⟹ the paper is in companion form.
