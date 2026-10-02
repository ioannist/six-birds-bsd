# Source-indispensability construction: result and open arithmetic obligations

Status: the algebraic construction and its countermodels are proved in Lean.
Indispensability of the named arithmetic recognition sources is **not proved**.
This document records a research outcome, not a replacement paper claim.

## Why the existing scalar interface cannot prove the proposed necessity

The current higher-GZ carrier includes fixity of the residual

\[
L^*=\kappa\,R\,\Omega\,T.
\]

The quantified recognition predicate additionally identifies its coefficient
with \(\#\Sha/t^2\), and its regulator, period, and Tamagawa factor with
those of the shell. These data alone imply the scalar BSD identity.
`SelShell.gzFixityForcesStrongBSD` proves exactly this, without a p-adic
descent or Sha-persistence argument. In ranks zero and one the recognition
predicate supplies the scalar identity directly as `lowerRankAnalogLane`.

Consequently, changing one numerical factor while freezing the others can
prove sensitivity of the product, but cannot establish that three named
source arguments are required to infer that product identity. Once the
normalized fixity premise is retained, deleting the other source records
does not destroy scalar entailment. Adding a certificate that calls those
records indispensable would assume the research target.

## A different interface with genuine premise independence

The construction in `lean/SixBirdsBSD/Closure/CoupledFactors.lean` starts
before either of two arithmetic normalizations. Write

\[
\begin{aligned}
N &: L^*=aR\Omega b,\\
C_b &: b=T,\\
C_a &: a=\#\Sha/t^2.
\end{aligned}
\]

Here \(a\) and \(b\) are native factors. Their definitions must eventually
come from independently constructed arithmetic objects. They are not
defined by the desired comparison equations. `assemble` proves that
\(N,C_b,C_a\) imply scalar BSD by multiplication and substitution.

Positive rational countermodels prove that no one premise can be dropped
from this universal implication while retaining the other two. Set
\(R=\Omega=\#\Sha=t^2=T=1\):

| Premise removed | \(L^*\) | \(a\) | \(b\) | Premises retained | BSD right side |
|---|---:|---:|---:|---|---:|
| \(C_b\) | 2 | 1 | 2 | \(N,C_a\) | 1 |
| \(C_a\) | 2 | 2 | 1 | \(N,C_b\) | 1 |
| \(N\) | 2 | 1 | 1 | \(C_a,C_b\) | 1 |

The Lean declarations are `localInputNecessary`,
`coefficientInputNecessary`, `fixityInputNecessary`, and
`countermodelsPositive`. These are countermodels on the stated rational
carrier. They are not examples of elliptic curves violating BSD.

## The precise limitation of the independence result

Under \(N\) and \(R\Omega\ne0\), scalar BSD is equivalent to the **single
product equation**

\[
ab=(\#\Sha/t^2)T.
\]

`scalarIffCombined` proves this sharp criterion. In particular, the two
individual comparison equations are sufficient but need not hold whenever
BSD holds. For \(a=2,b=1/2\), and all other quantities equal to one,
native fixity and scalar BSD hold while both individual comparisons fail.
`compensatingFactorsWork` proves this positive counterexample.

Thus the proved necessity is independence of premises for this assembly
interface. It is neither a necessity of each equality for every instance
of BSD nor an absolute impossibility of proving BSD by another method.
It is also not yet necessity of the three particular arithmetic sources.

## Exact obligations for an arithmetic landing

1. Construct native \(a(E)\) and \(b(E)\) on a declared common domain of
   elliptic curves, with the same curve, rank, determinant lines, bases,
   torsion convention, period convention, and local scope throughout.
2. Establish \(N\) without already inserting the coefficient or Tamagawa
   normalization. The present normalized GZ predicate does not provide
   an independent theorem of this form with independently defined factors.
3. Derive a sufficient exact return: either both \(C_a,C_b\), or the
   weaker combined product comparison. Identify precisely which source
   supplies which return and prove the applicability hypotheses.
4. Resolve local unit ambiguity and scope. The current local records carry
   comparisons modulo \(\mathbb Z_p^\times\) in a restricted additive-prime
   lane. Their `tamFactor` and `shaFactor` fields have no defining equation
   relating them to the local comparisons. The matching equalities in
   `piBSD` are supplied additional data. A local valuation or ideal
   comparison alone does not give the proposed global scalar equalities.
5. For a named-source indispensability theorem, specify what information
   remains after each ablation and realize the requisite countermodels in
   that allowed carrier. Free rational countermodels do not establish
   arithmetic realizability or rule out an alternate comparison theorem.

One possible exact return is a determinant-line product formula that fixes
the unit ambiguities jointly. Another is an all-prime valuation comparison
for a positive rational quotient, with rationality and full prime coverage
proved. Restricted prime coverage or positive real data alone do not give
that rational uniqueness argument. These are proposed routes; neither is
implemented as an arithmetic theorem here.

## Decision boundary

The original normalized scalar target cannot support the asserted
indispensability by its present entailment structure. The new native
interface supports a precise algebraic independence theorem, but its
arithmetic inputs remain research obligations. Calling those obligations
imports without proving their source and scope would move the gap into
hypotheses.

The defensible options are to pursue the arithmetic native-factor and
normalization construction, or later describe the established result as
factor sensitivity and conditional premise independence. A stronger
target retaining determinant, orientation, and source readouts may also
have real information requirements, but needs its own defined target and
ablation witnesses. No manuscript has been changed in this phase.

## Verification

The module is imported by the closure umbrella. The regression target
`SixBirdsBSD.Verification.Regression` prints the axiom dependencies of
the assembly, sharp criterion, countermodels, and existing landing.
The concrete rational decisions use kernel reduction. The observed axiom
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
Passing these checks validates the displayed statements, including their
explicit hypotheses; it does not discharge the arithmetic obligations.
