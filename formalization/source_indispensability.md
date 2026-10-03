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

## Arithmetic witnesses for the local unit obstruction

`Closure/LocalUnitSupport.lean` now tests the proposed local-to-global
bridge on primary elliptic-curve equations. It proves the numerical
invariant and shallow Tate-branch calculations, then proves information
loss over every observation invariant under local-unit multiplication.
The arithmetic interpretation of the branch outputs is supplied by the
classical Tate algorithm and independently reproduced with PARI/GP;
Neron models are not mechanized here.

The two witnesses use **Cremona labels**:

| Curve | Integral coefficients | c4 | c6 | Discriminant | Reduction at 11 | c11 |
| --- | --- | ---: | ---: | ---: | --- | ---: |
| 121a1 | [1,1,1,-30,-76] | 1441 | 54703 | -121 | II | 1 |
| 121b1 | [0,-1,1,-7,10] | 352 | -6776 | -1331 | III | 2 |

The equations and finite Tamagawa products agree with the primary
[Cremona allcurves data](https://raw.githubusercontent.com/JohnCremona/ecdata/master/allcurves/allcurves.00000-09999)
and [allbsd data](https://raw.githubusercontent.com/JohnCremona/ecdata/master/allbsd/allbsd.00000-09999).
The exact rows and file digests are in `local_unit_support_models.json`.
Their other BSD columns are provenance, not proofs of rank, finiteness,
or Sha cardinality. In particular, 121b1 has recorded rank one.

PARI/GP 2.15.4, run directly on these coefficient lists, returns
`[2,2,[1,0,0,0],1]` and `[2,3,[1,0,0,0],2]` from `elllocalred(E,11)`.
The [official output convention](https://pari.math.u-bordeaux.fr/dochtml/html/Elliptic_curves.html#elllocalred)
identifies these entries as conductor exponent, Kodaira code, minimalizing
coordinate change, and Tamagawa number. Its
[Tate-algorithm implementation](https://pari.math.u-bordeaux.fr/lcov-report/basemath/elliptic.c.gcov.html)
has the potentially-good branches with discriminant valuation two and
three returning component numbers one and two. The present numerical
selector checks primality, p>=5, p|c4, and the exact discriminant valuation.
Those valuations are below twelve and the j-invariant is integral; no
general Tate algorithm is claimed for other inputs.

Both models have discriminant prime support exactly `{11}`, proved from
the integer formulas in Lean without trusting the conductor label. Their
finite Tamagawa products are different, yet both products are units at
11. More strongly, multiplication by the rational 11-adic unit 2 carries
one value to the other; multiplication by 1/2 gives the reverse direction.
`noExactCurveBranchReadoutFromUnitClass` rejects every readout through this
unit-class interface that would recover both equation-driven component
numbers. The observation receives the component number modulo units; it
does not receive the equation or Kodaira code.

This exposes a specific index distinction. A component factor **arising
at bad place 11** can have **rational prime support at 2**. Lean proves
that 2 passes every prime-unit check on `{11}` but is not supported on
that set and is not one. Thus a bad-reduction-place list is not, by itself,
the independent rational-factor support bound required by
`unitsOnSupportForceOne`. No assertion is made that the joint BSD quotient
of either actual curve equals two.

For any odd prime in the shallow scope, the allowed component numbers
one and two are both local units. Consequently their factors disappear
in a congruence modulo that prime's units. In the displayed padic-descent
source, both c_p inverse and epsilon_p are units, so their multiplication
does not change the class of the descent value. The congruence can still
constrain that descent value; it cannot by itself normalize the exact
component factor. The same issue applies to a persistence congruence
with a prime-to-p component number.

The **full source record** retains the exact component number, and its
other structure may contain more information than this congruence. These
results therefore establish loss in a specified arithmetic observation
interface, not indispensability of the whole named source. The pair has
different recorded ranks and other analytic data; it is not an ablation
pair with every retained arithmetic source held fixed. Neither curve is
asserted to satisfy all Sha, tame-extension, signed-Selmer, and descent
hypotheses of a complete recognition instance.

A concrete repair is proved on the one-factor range `{1,2}`:
`recoverShallowFactor` observes whether the factor is a unit at **2** and
returns its exact value. Lean also rejects extending that Boolean readout
to products: 2 and 4 have the same prime-two unit flag but different
values. Exact valuations or an independent integral index are needed
for such products. For 121b1, the coefficient prime two is also the good
supersingular row outside the basic odd-prime Kobayashi scope recorded in
`support_prime_data_audit.md`; a generalized comparison at two requires
its own theorem and applicability proof.

`scripts/check_local_unit_support.py --check` reproduces the invariant,
support, branch, and rational-unit checks offline. Passing `--gp` with a
PARI/GP executable also recomputes local reduction and the finite global
Tamagawa product. False-target controls reject good-reduction input,
small or composite primes, zero valuation inputs, and nonminimal scaling.

### Self review of the arithmetic witness

The carrier, observation, and target are explicit: two fixed equations,
their numerical shallow-branch component outputs, observations invariant
under rational local units, and the exact component number. The no-go
quantifies over every readout on that interface. It excludes access to
the exact factor, equation, or Kodaira code; each would distinguish this
pair. The arithmetic branch identification is a standard imported
algorithm corroborated by independent PARI computation and primary data,
not a conclusion assumed in a Lean certificate. Lean proves the
numerical hypotheses and the rational information-loss theorem, not the
Neron component-group classification. This is an arithmetic test of
normalization and support, while the full named-source endpoint below
remains open.

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

The separate finite construction in `finite_pairing_construction.md`
now supplies actual groups with perfect alternating cyclic-target pairings
and impossibility theorems for every readout through dimension-only or
cardinality-only observations. These replace free finite metadata in the
dimension shadow and strengthen its information-loss claim. Those finite
proofs alone do not identify arithmetic Sha groups or prove indispensability
of the named sources for scalar BSD. The finite determinant return is now
constructed on actual integral hyperbolic presentations in
`Apparatus/FinitePresentation.lean`: a quotient-group isomorphism and
duplicate-free enumeration prove that the determinant is the cokernel
order. This supplies a normalized finite-model return and repairs the
earlier basis-change example. Arithmetic Selmer-complex identification,
compatibility with the named comparisons, and arithmetic ablation
witnesses holding the other named sources fixed remain open.

The exponent-two finite lane now has an arithmetic witness: the certified
two-descent for 571a1, with class-group certification and full pairing
rank, identifies its two-primary group with H_2 through standard descent
theory. Lean independently checks the quartic maps and local numerical
inputs and derives the higher-torsion exclusion. A second certified
descent for 1309a1, combined with its nonzero modular symbol and the
established rank-zero finiteness theorem, now supplies a genuine
arithmetic dimension-only partner. Both curves have two-torsion dimension
two; their finite two-primary orders are four and at least sixteen.
The generic Lean halving construction derives the partner's exact
four-torsion count sixteen rather than assuming it. Thus dimension
alone cannot recover the two-primary order on these actual curves.
The observation excludes curve identity and the other arithmetic source
data; those records are not held fixed between the pair. This proves
arithmetic loss on that specified interface, while full named-source
indispensability and determinant-line comparison remain open.
The subsequent published eight-descent refinement fixes the partner's
exact two-primary order sixteen and realizes the perfect paired H_4
lane. Lean derives the tail exclusion and normalizes every alternating
nondegenerate form on H_4 to the integral hyperbolic presentation.
It also supplies 2045b1 as a stronger partner: all finite Tamagawa
numbers and the trivial torsion group agree with 571a1, as does the
two-torsion dimension, while the two-primary orders are four and
sixteen. No readout through those retained finite inputs recovers the
two-primary finite factor. Since nonvanishing gives finite whole Sha
groups, their whole orders are four and sixteen times odd integers,
respectively, and cannot agree. Trivial rational torsion therefore also
gives a genuine whole-finite-factor obstruction through the same coarse
inputs, without computing either odd part. Lean proves that congruence
return from the derived primary counts. The eight-descent is imported from an identified
published computational proof, not a new supplied conclusion field or
a locally rerun PARI algorithm. Its analytic branch is selected using
an exact primitive Hecke eigensymbol and a proved arithmetic lattice
normalization, with the semistable Manin theorem explicitly imported;
the library's numerical real-period calibration is not the proof of
that scale. The analytic source data are not held
fixed between the pair, and these semistable curves do not supply the
Gamma sources' additive-prime hypotheses. See
`finite_pairing_construction.md`, `sha_four_normalization.json`, and
`sha_dimension_arithmetic_pair.json` for evidence, imported theorems,
scope and self-review. No exact numerical whole-Sha order or scalar BSD conclusion
follows from this comparison.

The construction modules are imported by the closure umbrella. The regression target
`SixBirdsBSD.Verification.Regression` prints the axiom dependencies of
the assembly, sharp criteria, countermodels, local-to-global returns,
source-scope necessity statements, and existing landing.
The concrete rational decisions use kernel reduction. The observed axiom
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
Passing these checks validates the displayed statements, including their
explicit hypotheses; it does not discharge the arithmetic obligations.

## A same-curve unit obstruction for a prescribed square-root comparison

The ordinary three-primary complex of 1913b1 now has a written
arithmetic derived identification with the hyperbolic `3J` presentation,
using checked local/Cartan applicability and separately sourced
three-primary bounds. Its inverse determinant has image `(9)` under
the acyclic trivialization. Two legitimate bases of that same line,
with images nine and eighteen, generate the same three-adic ideal.
The first has a root through the fixed square map from `(3)`; the
second does not, because two is a nonsquare modulo three.

Thus the Fitting ideal alone cannot return rootability of a prescribed
basis. Unlike the different-curve finite-factor pair, this variation
holds the curve, its cohomology, pairing, periods and local factors
fixed. It realizes genuine arithmetic information loss in the unit
of a determinant basis. Lean proves the finite square-class return
and repair by retaining that unit. The necessity is for this specific
comparison task and observable interface, not the full named-source
scalar claim. Choosing some liftable normalized basis is possible;
matching a prescribed native Stark basis is a separate requirement.

The compact complex's H1 is zero and its finite group is in H2.
The subsequent core-vertex construction supplies an actual finite-level
Stark-system return for this curve. Multiplicative inertia supplies the
rank-one element; a constructed central minus identity and a uniform
cocycle proof establish the cohomology hypothesis; local Kummer sequences
establish cartesian compatibility. Published core-vertex existence and
freeness theorems then supply exactly two auxiliary primes at each
coefficient level. At level `Z/27`, bases `epsilon` and `2 epsilon`
have the same complete Fitting ladder `(9),(3),(1)` but different
rootability through the fixed normalized square map. This strengthens
the ideal obstruction to actual Stark-system bases. The arithmetic
existence and comparison are written imported-theorem applications;
Lean verifies the supporting cocycle and finite calculations.

The compatible all-level manuscript shift, native generator and
orientation comparisons remain unresolved. Fixed-lane arithmetic
self-duality is supplied by the later paired derived construction. The
normalized GZ source still entails scalar BSD by itself. See
`odd_primary_selmer_bridge.md` and `stark_core_vertex_construction.md`
for the constructions, imports,
arithmetic-versus-Lean coverage and self-review.

## Promotion to compatible arithmetic systems and an exact square-class repair

`stark_inverse_limit_construction.md` now applies Sakamoto's integral
coefficient and Fitting theorems, after checking integral cohomology
vanishing, propagated Kummer conditions, nested full auxiliary sets
and the actual dual Selmer transition maps. A basis of the full
three-adic Stark-system module lifting the established `Z/27` basis
exists by rank-one base change. It and twice it have identical
component-image ideals at every coefficient level, including their
reduction maps and limits, yet different rootability through a fixed
normalized square map. This is a completed arithmetic carrier, not
a sequence of unrelated finite witnesses.

A digit-lifting proof establishes that a three-adic unit is a square
exactly when its residue modulo three is one. This gives an exact
repair by retaining the erased square-class bit. It also proves that
the square-image subset does not depend on which integral linear lift
of the fixed finite determinant/Stark comparison is chosen. The
comparison is canonical modulo this square-class ambiguity, without
claiming a canonical integral map. Lean constructs all compatible
coefficient levels, one compatible inverse of two, and the no-go for
an arbitrary entire family of generated ideals. The arithmetic theorem
application and general digit-lifting classification are written proofs.

The theorem remains relative to the prescribed-root task and its ideal
observable. It neither identifies the manuscript's native generator
nor establishes named-source necessity for scalar BSD. The native
generator, manuscript degree and orientation comparisons remain
unresolved, as does the stronger original source endpoint. The
subsequent construction below supplies the fixed compact lane's
arithmetic self-duality without resolving these native comparisons.

## Paired derived realization preserves the surviving basis obstruction

The construction in `ct_derived_transport_construction.md` now supplies
the actual arithmetic Nekovar–Flach comparison for 1913b1 at three.
It checks the local conditions, constructs the coefficient connecting
identification with Sha, and retains the raw minus sign. Explicit
negation gives the positive Flach pullback. Matching finite pairings
then determines the derived duality map up to the displayed homotopy.
The normalization chain lift has equal determinants in both degrees,
so it preserves the same canonical determinant trivialization used
by the Stark construction. Lean proves the integral matrix and
rational linking algebra; the arithmetic argument uses stated imports.

This sharper realization leaves the two coherent bases `e` and `2e`
with the same curve, paired derived object and determinant
trivialization. All component ideals remain identical and their
prescribed-square rootability still differs. Thus pairing normalization
does not recover an independently prescribed Stark-basis unit. A native
basis comparison must supply further information; no named recognition
source has been shown to supply exactly that information. The current
GZ predicate still entails scalar BSD alone. The construction is a
genuine arithmetic paired-derived return and a sharper surviving
obstruction, not a proof of the full source-indispensability endpoint.

## Canonical integral comparison and the precise native obligation

`stark_coefficient_naturality.md` now proves that the actual finite
determinant/Stark maps commute with the coefficient transitions defining
the arithmetic Stark module. Its proof uses one common core vertex,
coefficient-natural continuous cochain lifts, the explicit negative
degree-two map, and matched exterior contraction/permutation signs.
The limit is consequently a canonical linear isomorphism `Phi_can`.
Lean constructs the inverse-limit return and its inverse, proves
uniqueness, and rejects an explicit incompatible family of finite
isomorphisms. The arithmetic naturality remains written mathematics
with identified primary imports.

The witnesses can therefore be the canonical basis
`e_can=Phi_can(delta)` and its unit multiple `2e_can`, with the fixed
canonical square map. Every component ideal still agrees and their
rootability differs. The square-image subset agrees with that of any
earlier linear lift of the fixed level-three comparison. Canonicity
has removed a choice from the comparison; it has not recovered the
unit lost by the ideal observation. The exact remaining generator
obligation is to identify the manuscript's independently prescribed
native selection with a square-unit multiple of `e_can`, and then
match its root and target with the specified Pfaffian orientation.
Supplying that coefficient as a certificate would assume the missing
return. Named-source arithmetic ablations and the original scalar
source endpoint remain unresolved.

## A paired Pfaffian root return and a sharper source boundary

`ct_pfaffian_root_construction.md` constructs the actual root line of
the paired rank-two arithmetic presentation and compares its square
to the same determinant/Stark line. The coefficient `u` in the
arithmetic pairing contributes `u^2` to the square comparison. The
inverse-unit root therefore squares to the canonical determinant
basis and returns scalar three. A calculation of the raw/corrected
root orientations retains the raw minus sign and identifies the
matching source correction. The construction descends through
frame changes and unit-lift changes on its declared carrier.

The resulting embedded root ideal is `(3)` with square comparison
into `(9)`. That object and its scalar-three basis can be recovered
from the canonically trivialized determinant ideal alone. Thus this
particular return does not require retaining the pairing coefficient.
Its proof of compatibility with the arithmetic pairing must not be
converted into indispensability of the pairing source. For an
arbitrary prescribed Stark basis the square-class bit remains
necessary: the actual square map is `(u*a)^2 e_can`, so `2e_can`
has no root while sharing every component ideal with `e_can`.

The original manuscript names the native root and height in its
import package but has no independent formulas selecting them.
Identifying them with the root and scalar just constructed would
therefore require additional native definitions and a theorem,
including the H1/div degree convention and scalar-line orientation.
The conditional imported comparison remains valid as a projection.
The canonical root construction does not fill those native fields
or repair the normalized GZ predicate's scalar redundancy.


## Common-cover arithmetic Frobenius split pair

The construction in [`additive_frobenius_descent.md`](additive_frobenius_descent.md)
uses the actual 121a1/121b1 equations on one fixed tame cover at eleven,
`pi^12=11`. The transformed integral models have unit discriminant minus
one, and both good fibers have twelve points and Frobenius polynomial
`T^2+11`. The unfiltered rational Frobenius modules are isomorphic by a
written cyclic-basis argument. Nevertheless the original base component
numbers are one and two. Consequently no function on that common-cover
unfiltered module class can return both component numbers. Lean proves
the polynomial-only no-go and checks the exact quotient equations and
finite point counts. Good reduction and p-adic cohomology are written
arithmetic inputs, not mechanized certificates.

This strengthens the local information-loss evidence with a common-cover
arithmetic construction. Its lens erases inertia/descent, filtration,
integral lattices and the original equations; it does not erase those from
the full named source. The curves do not have matching global ranks or
normalized GZ inputs. Their original modular-symbol U11 lines are both
zero-eigenvalue lines, whereas the cover beta is nonzero; an equivariant
generalized-beta specialization to either original line must vanish.
A new modular/descent bridge is needed for the proposed eta route.
An explicit repair on this pair retains the native tame-inertia action:
its orders are six and four, as derived from the two coordinate scalings.
Marked coordinate characters recover the scale exponent modulo twelve;
the unit transformed discriminant and small-valuation scope make that
an exact base discriminant-valuation return to the shallow Tate branch.
The construction records the unramified extension and character marking,
and does not present this as a uniform rule for all additive curves.
Neither this local no-go nor this sharper obstruction resolves the full
named-source ablations or the scalar redundancy of normalized GZ.


## Intrinsic tame component return and a full-representation boundary

[`tame_component_return.md`](tame_component_return.md) constructs the
native local factor det(1-tau) before considering the component group.
For tame purely additive elliptic reduction with geometric inertia
order six or four, its exact integer values are one or two. The checked
Nicaise Jacobian theorem identifies this with geometric component order;
Frobenius fixes a group of order one or two and gives the exact rational
Tamagawa number. This upgrades the coordinate-marked two-curve repair
into an invariant arithmetic return on the declared domain. Lean proves
matrix covariance, the actual integral image and quotient, and the
Frobenius step. The arithmetic component/cohomology identifications are
written imported-theorem proofs. A comparison with the independent
OC local map and its globally used tamFactor remains open.

The explicit three-isogeny from y^2+11xy+11y=x^3 to
y^2+11xy+11y=x^3-605x-15488 gives a stronger non-CM boundary control. Both have type IV at eleven, but their local
component numbers are three and one. The isogeny, its dual and the
inverse of three construct an isomorphism of the entire integral
T11 Galois modules, compatible with every coefficient level. Therefore
even this full representation class cannot return c11 on a domain
containing this pair. All rational Tate-module classes are also preserved
by this one isogeny; the integral three-adic lattice need not be.
A compatible digit lift constructs a square root of three in Z_11;
rescaling the isogeny map by its inverse also preserves the Weil pairing.
Thus the full integral T11 observation can retain that pairing as well.
The geometric component orders agree, and Frobenius-fixed orders differ.
This shows why the rational component bridge and domain must be retained.

The pair lies outside the manuscript's II/III source scope. Isogeny
also preserves L-functions and ranks, but other integral and normalized
BSD data are not frozen. This is an arithmetic information-loss theorem
for the declared representation interface, not a BSD counterexample or
an ablation of all the other named sources. The normalized GZ scalar
redundancy and the native OC/CT/eta comparisons remain unresolved.
