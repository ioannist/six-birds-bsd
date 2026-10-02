# Source-indispensability construction: result and open arithmetic obligations

Status: the algebraic construction, an exact rational local-to-global return,
and source-scope necessity theorems are proved in Lean.
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
implemented as an elliptic-curve arithmetic theorem here. The rational
local-to-global route now has the explicit construction below.

## New construction: exact recovery from local unit comparisons

The module `lean/SixBirdsBSD/Closure/RationalLocalGlobal.lean` closes the
elementary local-to-global step on actual positive rational numbers.
It also proves a sharp necessity theorem for the resulting scalar assembly
rule. It does not change the original normalized recognition interface.

On the native-factor carrier above, define the joint comparison quotient

\[
q=\frac{ab}{(\#\Sha/t^2)T}.
\]

For a prime \(p\), `UnitAt q p` says that neither the numerator nor the
denominator of the **reduced rational number** \(q\) is divisible by \(p\).
This is a concrete divisibility predicate; the module does not construct
a p-adic field or assume a valuation oracle. For \(q>0\), checking this
condition at every prime forces \(q=1\): a numerator or denominator
greater than one would have a prime divisor. Positivity removes the
surviving sign ambiguity; \(-1\) passes every prime-unit check.

Suppose an independently established support bound says every prime
dividing the reduced numerator or denominator lies in a specified set
\(S\). Two local sources supply `UnitAt q p` on scopes \(A\) and \(B\).
If \(S\subseteq A\cup B\) on prime indices, the quotient is exactly one.
Together with native fixity \(N\), this gives the scalar BSD equation on
the stated rational factor carrier. `scalarBSDFromPositiveTwoScopes` proves this return with the
nonzero and quotient-positivity side conditions derived from positive
factor data. Neither separate factor normalization is assumed.

The construction also has a complete coverage criterion:

\[
\begin{gathered}
\text{For every positive native factor package with quotient supported in }S,\\
N\text{ and the retained unit checks on }C\text{ imply scalar BSD}
\quad\Longleftrightarrow\quad
\text{every prime in }S\text{ belongs to }C.
\end{gathered}
\]

`forcesScalarIffCoversSupport` proves both directions. For necessity,
choose a prime \(\ell\in S\setminus C\), and set \(L^*=b=\ell\),
with \(a,R,\Omega,\#\Sha,t^2,T\) all equal to one. Native fixity holds,
every retained unit check passes, and scalar BSD fails because its right
side is one. The quotient is the actual rational number \(\ell\),
supported at precisely that prime. These witnesses are realizable rational
data rather than freely assigned prime labels. They are still not realized
elliptic curves.

If the union of two source scopes covers the support and each source has
a supported prime absent from the other, both are indispensable to this
universal assembly rule. `twoSourcesIndispensableForScalar` proves this.
The regression checks the inhabited example \(S=\{2,3\}\),
\(A=\{2\}\), \(B=\{3\}\). The fixity input is also necessary: the
earlier `missingFixity` package has quotient one and passes every prime
check, but fails scalar BSD. `fixityNecessaryForUnitAssembly` checks this
third ablation in the new interface.

Without an independent support bound, a finite prime list cannot recover
the global value. `finitePrimeUnitNoGo` constructs an actual prime outside
any given finite prime list; its rational value and one have identical
retained unit records. Every operator on those records returns the same
answer on the pair. The regression also checks that even all odd-prime
unit comparisons leave a possible prime-two obstruction.

## Why the named-source endpoint remains open

The new theorem identifies the missing arithmetic bridge:

1. Construct native \(a,b\) independently, and show their joint comparison
   quotient is a positive rational number. Defining the factors by the
   desired comparison equations would bypass this work. The present
   `FactorData` carrier is rational throughout; actual real analytic,
   regulator, and period data require an explicit scalar bridge or an
   appropriate generalization of the assembly carrier.
2. Prove a support bound independently of successful local checks.
   A finite set of investigated primes is not such a bound.
3. Derive the concrete `UnitAt` comparisons for this same quotient from
   the named p-adic and signed-Selmer sources. The current congruence
   fields are arbitrary propositions and do not define their scalar
   `tamFactor` or `shaFactor` through a common quotient.
4. Establish coverage and the genuinely different information supplied
   by each source. The private-prime criterion has not been established
   for the named sources. Different operators at the same prime could
   require a different observation model.
5. For arithmetic source necessity, realize the ablation witnesses in the
   allowed arithmetic carrier, or prove another separation theorem there.
   The rational witnesses prove universal assembly dependence on the
   declared factor carrier. They do not establish that every alternative
   BSD proof needs the same sources.

A concrete next construction is to produce two independently defined
integral lattices in a common rational determinant line. Their relative
index would supply rationality, and an independently controlled finite
cokernel could supply a support bound. Local comparison theorems would
then have an actual index quotient to test. These lattices have not been
constructed for the present elliptic-curve recognition sources. The
existing normalized GZ readout already supplies the scalar target and
cannot fill this role without first establishing a genuinely native
version of its identity.

## Decision boundary

The sign part of the local-to-global return has now been made exact in
`Closure/CTSignTransport.lean`: without positivity, all-prime unit checks
force precisely `q = 1` or `q = -1`. The native negative-defect model
passes every local check and satisfies native fixity while scalar BSD
fails. A source-independent positivity theorem or a proved arithmetic
orientation comparison is therefore still required for this route.

Primary checks of the Cassels–Tate stack exposed a raw negative comparison
on torsion H2, plus distinct odd-prime and ordinary applicability scopes.
The rational sign correction and the simultaneous map/generator correction
are constructed, but their arithmetic identification is open. The
classical 2-Selmer normalization cannot on its own fix a nonzero odd-primary
pairing; the new module proves the requisite coprime-torsion vanishing.
See `ct_import_audit.md`. This preserves the positive rational construction
while identifying a substantive orientation input for an arithmetic return.

The original normalized scalar target cannot support the asserted
indispensability by its present entailment structure. The new native
interface supports precise algebraic independence and support-scoped
local-to-global necessity theorems, but its elliptic-curve arithmetic
inputs remain research obligations. Calling those obligations
imports without proving their source and scope would move the gap into
hypotheses.

The defensible options are to pursue the arithmetic native-factor and
normalization construction, or later describe the established result as
factor sensitivity and conditional premise independence. A stronger
target retaining determinant, orientation, and source readouts may also
have real information requirements, but needs its own defined target and
ablation witnesses. No manuscript has been changed in this phase.

## Verification

Both construction modules are imported by the closure umbrella. The regression target
`SixBirdsBSD.Verification.Regression` prints the axiom dependencies of
the assembly, sharp criteria, countermodels, local-to-global returns,
source-scope necessity statements, and existing landing.
The concrete rational decisions use kernel reduction. The observed axiom
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
Passing these checks validates the displayed statements, including their
explicit hypotheses; it does not discharge the arithmetic obligations.
