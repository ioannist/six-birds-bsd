# OC eta import audit

The displayed eta identity remains an explicit conditional certificate in
Lean. This audit identifies obstacles to deriving it from the named input
stack. It does not disprove an independently defined eta identity, and it
does not alter the manuscripts.

## Exact mechanization boundary

`etaPublishedImports.etaFormulaHolds` is the full displayed eta identity.
`ocEtaFormula` returns that field together with the citation-labelled
proposition fields. The proof does not use the beta square relation or
derive a normalization from the named propositions.

The record is now indexed by its curve and numerical prime. Its prime
and oddness checks are concrete; scalar prime and torsion fields have
explicit natural-number comparison equations; beta and the denominator
factors must be nonzero. The scope predicate is applied to that same
curve and prime. Previously these were unlinked generic arguments,
and the nonzero assumptions were absent. These repairs prevent basic
typing mismatches; they do not instantiate an elliptic-curve torsion
group, an actual coefficient field, or a published theorem's hypotheses.

Thus the Lean theorem proves an implication from a supplied comparison
certificate. It does not establish that the listed published statements,
plus the single named cuspidal-layer conjecture, imply that certificate.
Keeping those two mathematical claims distinct is essential.

## Square relation versus critical slope

For a nonzero beta and the standard valuation normalization,
\[
\beta^2=-p\quad\Longrightarrow\quad
2v_p(\beta)=v_p(-p)=1\quad\Longrightarrow\quad v_p(\beta)=\tfrac12.
\]
At weight two, the usual critical slope is one. Benois–Büyükboduk use
the threshold \(k-1\) for weight \(k\), and their setup begins with a
newform of tame level prime to \(p\); see
[§0.2.1–0.2.3](https://arxiv.org/pdf/2403.16076).
The square relation therefore cannot simultaneously be a certificate
of weight-two critical slope under those conventions.

`EtaApplicability.squareRelationForcesHalfValuation` and
`weightTwoCriticalSlopeIncompatible` prove this calculation. Only the
valuation law at the nonzero beta square is required: no finite-valued
multiplicative valuation is imposed at zero.

The Lean field has been renamed `betaSquareRelation`. Its equation is
unchanged, and the eta formula is unchanged. A different weight,
valuation normalization, representation, or cover may support a
different construction, but needs an explicit comparison before these
critical-slope results can be applied.

This obstruction excludes a specifically critical-slope argument under
the stated normalization, not every result in that paper. Its
Proposition 2.20 also compares non-theta-critical constructions. A
repair might use a noncritical finite-slope route, but would still have
to construct the additive object and verify the level and comparison
hypotheses; that applicability is not supplied by the square relation.

## What Bellaiche's moment lemma actually supplies

Lemma numbering differs among versions. The moment statement is
Lemma 3.21 in the
[author's prepublication version](https://people.brandeis.edu/~jbellaic/preprint/criticalbeforepublication.pdf)
and Lemma 3.12 in the
[earlier arXiv text](https://arxiv.org/pdf/0912.2925).
It relates a moment on a residue class at depth \(n\) to an
eigensymbol evaluation with factor \(\beta^{-n}\), subject to a
nonzero generalized eigenvalue and a specialization condition on
\((U_p-\beta)\phi\). At weight two the allowed classical moment is
\(j=0\); depth two gives a \(\beta^{-2}\) factor.

This supports the shape of that factor in an applicable moment
calculation. It does not by itself identify the moment with
`T_leading_Bellaiche`, define the eta value, establish a finite-slope
additive stabilization, or supply the component/torsion normalization.
The ambient tame-level hypothesis must also be checked. An earlier
version's differently numbered lemma must not be mistaken for evidence
that the cited moment lemma does not exist.

## Lang-Wake's primes and the three anchors

[Lang–Wake, Theorem 1.1](https://arxiv.org/pdf/2501.04162)
has a level prime \(N\) and a residual prime \(\ell\), both at least
five, with \(\ell\mid N+1\). Its target is a specified weight-two
Eisenstein Hecke algebra at level \(N^2\). These numerical conditions
are necessary, but not sufficient, for an application to an eta value.

`EtaApplicability.LangWakeNumericScope` records those numerical conditions.
The following obstructions are proved in Lean:

- The primes cannot be identified: \(N\mid N+1\) would give \(N\mid1\).
- At the \(36a1@3\) anchor, identifying the level prime with the local
  additive prime gives \(N=3<5\). Using full level 36 instead would
  give \(N=6\), which is not prime.
- At the \(49a1@7\) anchor, \(N+1=8\) has no prime divisor at least five.
- At the \(121b1@11\) anchor, \(N+1=12\) has no prime divisor at least five.

Hence choosing a different residual prime still does not put any of
these three level-prime anchors in this theorem's numerical scope.
A route through another Hecke algebra, a different level, or a separate
comparison theorem would require an additional arithmetic bridge.
The word “prime-square” alone does not establish that bridge.

## Anchor verification and repair choices

The current public artifacts record eta values at the three anchors,
but provide no executable computation or complete input tuple for the
leading term, its order, beta, and normalization. Those values alone
do not allow an independent recomputation of the displayed identity.
This is missing verification evidence, not evidence that the values
are wrong.

Restoring the claimed input stack requires the following concrete work:

1. Define the additive finite-slope object and show that its Hecke
   eigenpacket, level, weight, local representation, and valuation
   conventions fit the selected comparison theorem. Resolve the
   half-slope versus critical-slope conflict.
2. Establish the precise moment/leading-term identification at a fixed
   normalization, including the generalized eigensymbol specialization
   hypothesis and the choice of expansion parameter.
3. Prove a component/torsion comparison on the intended additive domain,
   using a theorem with verified applicability. The direct Lang-Wake
   application above does not cover the listed anchors.
4. State the cuspidal-layer nonvanishing/primitivity conjecture precisely
   and show that, combined with the applicable comparisons, it gives
   the eta equation. An arbitrary proposition with that name is not
   this implication.
5. Supply the anchor input tuples and reproducible checks, distinguishing
   finite evidence from a uniform theorem.

The alternatives are an arithmetic repair retaining the intended eta
formula, an explicitly conditional theorem with the missing comparisons
listed as new open inputs, or a theorem on a narrower supported domain.
Changing the source burden or excluding the anchors is a material scope
decision and has not been made in this phase.
