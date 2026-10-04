# Mathematical closeout of the conditional BSD translation

This is a mathematical and formalization record, not manuscript text.
It implements the three-item final audit requested on 3 October 2026.
The target remains a conditional translation of BSD into Six Birds closure.
The stronger scalar-source indispensability claim is retired from the
retained argument. No unconditional BSD theorem is claimed or required.
The original constructions, citations and unresolved arithmetic comparisons
are preserved in their source records. The papers have not been edited.

## 1. The exact closure bridge

Fix a field k with 2 nonzero, a formed carrier A, an idempotent C on A,
and a scalar readout q:A -> k x k, all before supplying comparisons.
The already constructed scalar closure is

    c(a,b) = ((a+b)/2, (a+b)/2).

`ArithmeticClosureBridge.ReadoutIntertwines` makes the missing structural
comparison an explicit, uniform conditional hypothesis:

    q(C(x)) = c(q(x)) for every x in A.

It is not a certificate that the original arithmetic state is closed.
Under this comparison, the derived exact return is

    q(C(x)) = q(x)  iff  q(x).1 = q(x).2.

Consequently, if the ORIGINAL state x is C-fixed, its scalar coefficients
agree. `formedClosureForcesStrongBSD` specializes this to the shell's
declared operator, using a separately supplied original state and exact
match q(x)=(L^(r)/r!, BSD right side). It lists comparison, original-state
fixedness and the readout match individually. Merely possessing an
idempotent endomorphism is not this hypothesis.

Conversely, the existing recognition content fixes the observed pair:
`recognitionFixesFormedReadout` proves q(C(x))=q(x) under the comparison
and original readout match. It does not reconstruct the full arithmetic
state or prove that x=C(x). Full fixedness is equivalent to scalar
fixedness if q is injective, as proved separately; injectivity is NOT a
standing assumption on a scalar projection of a large arithmetic carrier.

The comparison has not been constructed for a native Selmer/determinant
layer. The settled conditional formulation includes it explicitly whenever
using the full-carrier route. The scalar recognition route does not need
that additional comparison. Neither route derives a semantic master
application from the legacy `masterFromRecognitionAudits` field.
That field's conclusion-equivalent strength remains exposed in
`master_applicability_audit.md`; an independently established application
cannot be reported from that record projection.

Three constructed rational controls test the missing directions:

* C((a,b),t)=(c(a,b),0), with q forgetting t, intertwines exactly.
  The input ((1,1),1) is scalar-closed but not fully closed.
* The same C intertwines on ((2,1),0), but that ORIGINAL state is not
  closed and 2 does not equal 1. Its transformed output is closed.
* Identity closure fixes (2,1), but cannot intertwine with c through
  the identity readout. Full fixedness without the comparison gives no BSD.

These are operational counterexamples, not arithmetic elliptic curves.
They show why no converse or native identification was silently added.

## 2. The argument after removing necessity

`ScalarBSD.lean` extracts the actual scalar proof into declarations with
no legacy shell or recognition-record prerequisite. The algebra uses only
the subtraction law, denominator movement, the original coefficients,
normalization kappa=Sha/torsionSquared and supplied fixity. The all-rank
theorem consumes the supplied classical scalar lane at ranks zero and one
and normalized fixity at ranks at least two.

`gzFixityForcesStrongBSD` and `piBSDForcesStrongBSD` now invoke this core.
Their mathematical conclusions and the primary landing's premise type
are unchanged. The primary all-rank landing remains a valid conditional
composition. It does not invoke the composite-signature theorem, eta
formula, Pfaffian comparison theorem or master-applicability theorem to
derive its scalar conclusion.

`scripts/check_conditional_core.py` checks compiled project-declaration
dependencies, including types and available definition/proof values,
recursively through project declarations. It checks both scalar core
theorems and both main composition steps, rejecting necessity/ablation,
computability/falsifiability/dependence projections and the excluded
auxiliary theorem calls. The scalar core is also required to have no
dependency on another project record. The gate runs in `make verify-lean`.
It does not inspect arithmetic meanings or pretend that unused fields
are absent from the legacy shell type.

The older shell and generic audit declarations remain compatibility and
provenance records. In particular, the shell still packages extra
opaque audit/ablation receipts. They are not a requirement of the extracted
scalar theorem and are not interpreted here as scalar-source necessity.
`compositeSignature` retains its valid factor-sensitivity algebra and
supplied receipt projections; its docstring now states their exact scope.
It is excluded as an anti-tautology justification for the scalar landing.
Rational native-factor independence and finite information-loss lemmas
remain at their proved interfaces; they do not restore the retired claim.

## 3. Decisions on the auxiliary scope problems

| Item | Retained mathematical statement | Excluded inference / remaining conditional content |
| --- | --- | --- |
| Master applicability | The legacy rule is exactly a supplied implication, conclusion-equivalent with the smuggle proof. The new full-carrier return is conditional on an explicit uniform readout comparison and original-state fixedness. | No derived arithmetic master application from nine arbitrary proved propositions. No inference of original fixedness from idempotence. |
| Eta | `ocEtaFormula` is a projection from a curve/prime-indexed certificate explicitly containing the equation. | The cited-results-plus-one-conjecture derivation is excluded from the retained proof. beta^2=-p has standard slope 1/2, not weight-two critical slope 1; the direct Lang-Wake route excludes the listed level-prime anchors. A different arithmetic route remains research, not a closeout prerequisite. |
| Eta anchors | Historical proposed values remain recorded. | Without complete input tuples or reproducible formula computations they are not verified mathematical evidence for the eta identity. No family coverage follows from these rows. |
| Cassels–Tate/Pfaffian | The comparison is conditional on the fixed native family's selected generator, target, map, canonical property, image identity and normalized sign at the same E,p. Existing finite and fixed odd-primary constructions retain their proved scopes. | T_E1–T_E8 alone do not construct that map or sign. Raw torsion-H2 U_(2,2) equals minus Flach. H1/div, prescribed Stark unit, determinant conventions and final native orientation require supplied comparisons. No prime-two/signed extension from odd-prime/ordinary results. |
| Finite scalar normalization | Integral hyperbolic presentations return half-order n and cardinality n^2, with the arithmetic finite lanes scoped in their source records. | A raw rational lift of a torsion pairing has no canonical numerical Pfaffian. No identification of that raw coefficient with Sha cardinality. |
| Fifth column | An independent orientation/trivialization may be supplied to determinant assembly. The existing double-counting counterexample is retained. | The final assembly cannot itself serve as a fifth multiplicative factor alongside the other four factors. Native tensor transports remain explicit conditional data. |
| Computability | `verifyScalarReadout` checks equality of a supplied pair with a supplied decidable equality. It is executable on the exact rational controls and accepts exactly scalar-closed pairs. | It does not compute analytic coefficients or Sha, decide real equality without an effective presentation, or decide the quantified recognition predicate. General computability and operational falsifiability claims are excluded; legacy receipts are only supplied propositions. |
| Local/all-prime coverage | Quantified local records are used only in their declared scopes; a finite support and sign/rationality comparison must be supplied where a local-to-global statement needs them. | No wild-prime, high-rank CM, unrestricted signed or all-prime arithmetic applicability from a generic shell or finite model. No uniform theorem from support tables or audit labels. |
| Cascade and AOR | The cascade adapter is a supplied branch-to-valuation comparison; the AOR relation preserves local statuses and obligations. | Neither supplies the low-rank scalar lane, proves global BSD from one valuation, or establishes every external refinement. Neither is used to replace arithmetic inputs in the scalar core. |

These exclusions are mathematical scope decisions for this closeout, not
claims that the original manuscript already states them. They remove the
need to pursue unrelated arithmetic repairs in order to finish the
conditional translation. They preserve the stronger routes as explicitly
unproved research rather than silently certifying them.

The eta scope checks were also rechecked against the primary statements:
[Benois–Büyükboduk, §0.1.2 and §0.2.3](https://arxiv.org/pdf/2403.16076)
normalize v_p(p)=1 and define critical slope as k-1;
[Lang–Wake, Theorem 1.1](https://arxiv.org/html/2501.04162v1)
requires level prime N and residual prime ell at least five, with
ell dividing N+1, and has a specific weight-two Eisenstein Hecke-algebra
target. Therefore N=3,7,11 fail its necessary numerical conditions as
proved in `EtaApplicability.lean`. The half-slope conclusion is the
elementary square-valuation calculation, not a quoted arithmetic theorem.

## 4. Instance and applicability ledger

| Input of the retained composition | Actual matching and scope | Supplied interpretation |
| --- | --- | --- |
| Original target | One shell E, analytic rank, leading value, Sha, regulator, period, Tamagawa product and squared torsion denominator; `strongBSDRightSide_eq` fixes the product. | These scalars are the indicated arithmetic invariants in common conventions, with finite Sha and a defined leading coefficient. Lean does not construct their native arithmetic definitions. |
| Scalar algebra | The subtraction-zero law and denominator-movement law are explicit. Field constructions require operation matches when using shell multiplication/division; cancellation requires exactly the five nonzero factors already characterized. | Standard real BSD coefficients supply the lawful characteristic-zero setting. Prime two in arithmetic is unrelated to scalar characteristic two. |
| Low rank | `lowerRankAnalogLane` is gated by rank zero or one and uses that shell's original coefficients. | The scalar identity is supplied. The supporting cascade does not independently populate it. |
| High rank | `piBSD.gammaHigherGZFixityReadout` matches E, analytic rank and every displayed factor, including kappa and the exact regulator product. | Higher-GZ fixity and kappa normalization are supplied. The source's non-CM condition requires its native meaning; no high-rank CM coverage is inferred. |
| Local descent | `piBSD` matches E,p,L and Tam factor, with both bad-place and lift gates. Its scoped output implies actual primality and oddness. | Additive shallow II/III, tame lift, Sha and OC comparison content remain supplied; matching a local factor to global Tam requires the declared aggregate comparison. No p=2 extension. |
| Signed persistence | `piBSD` matches E,p and Sha factor, and implies primality at the declared admissible prime. | HPS2, tame lift, signed pairing/corestriction determinant and native Sha interpretation remain supplied. No extra oddness restriction is invented for this separate source. |
| CT import | Fixed native family, same shell E and the numerical chiPrime; primality and applicable hypotheses are returned. Generator/target must equal that family's partial selections. | A single imported prime is not coverage of every support prime. Odd/ordinary named routes are not silently extended. |
| A_E import | Pairing/category/complex and statement families are fixed before certification and evaluated at shell.E. | Native pairing and determinant transports are supplied; the generic family is not their construction. |
| Beilinson import | Same shell E, required only at rank at least two, and matched to shell rank. | Archimedean determinant/L-value comparison remains supplied. No rank-at-least-two import is demanded at low rank. |
| Expanded audit landing | `strongBSDConditionalWithAudits` now uses the shell's curve and lift carriers, with explicit E matches, GZ rank match and declared descent/signed prime/lift gates. | This repairs a remaining instance mismatch in the expanded variant; the primary landing was already indexed. Its audit conclusions remain conditional receipt projections. |
| Full-carrier route | C is the specified shell operator; q and original state are fixed; the uniform comparison, original readout match and original-state fixedness are explicit. | Native comparison/application is a conditional hypothesis, not established from opaque applicability or lawfulness field names. |

Distinct self-review checked premise direction, original versus transformed
input, lost fibers, both rank ranges, the same-instance bindings and the
scope of each excluded auxiliary theorem. This is self-review, not an
independent review. The accepted recognition content is allowed to have
target-equivalent scalar strength; the result is not represented as an
independent arithmetic derivation or as a minimal-hypothesis theorem.

## Completion boundary

The three requested closeout items are settled by derived scalar algebra,
an explicit conditional full-carrier comparison, auxiliary exclusions and
instance repairs. Completion of this mathematical closeout does not mean
all 69 manuscript labels are fully mechanized or all legacy claims are
correct. The unchanged manuscript still needs its later authorized edits:
remove indispensability and its proof uses, state the exact conditional
master/closure scope, and implement the auxiliary exclusions above.
Alignment categories are retained against that unchanged manuscript;
passing gates is not a promotion of any native arithmetic claim.

## Verified closeout checkpoint

* `make verify-lean` passes: 99 build jobs including the regression target,
  all 51 manifest declarations checked live, unchanged five-axiom manifest
  trust base, and four compiled conditional-dependency roots checked.
* A separate negative dependency control calls the legacy supplied master
  rule transitively; the probe rejects it at `masterFromRecognitionAudits`
  as intended. Thus the exclusion gate is not only tested on passing roots.
* All 14 new printed axiom closures use only standard Lean foundations;
  normalized scalar fixity itself is axiom-free.
* `make validate test public-audit` passes, including all 26 unit tests.
  The 29 theorem-alignment classifications and 40 supplementary assessments
  retain their categories; their notes and context binding reflect this
  closeout. The context is
  `734a74cfbdde0871ca2a25d29b29a8716303441e4518381749d6933fc362a59b`.
* The paper tree has no changes. The preserved Stark and finite-pairing
  constructions are not replaced by this scoped closeout.

## Manuscript v2 (4 October 2026)

Both papers have since been revised to v2, implementing the decisions
above: indispensability, the derived master application, general
computability/falsifiability claims, the cited-stack eta derivation and the
eta anchor evidence are removed from the manuscripts; the scalar closure
translation and the conditional formed-carrier bridge are stated as
`thm:closure:scalar-closure-translation` and
`thm:closure:formed-closure-bridge`; the two literature no-go theorems are
remarks; and every Lean-coverage statement follows the alignment records.
The label set is now 71 (30 theorem alignments, 41 supplementary
assessments, 52 manifest entries). The historical counts above (69 labels,
29 theorem entries) refer to v1. Each revised section was reviewed for
mathematical and factual correctness by an independent model reviewer
before acceptance.
