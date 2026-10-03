# Finite paired-group construction checkpoint

This construction replaces dimension/exponent metadata with actual finite
groups. The Lean group construction is finite algebra. The separate
certified two-descent below now identifies its exponent-two lane with
571a1's two-primary arithmetic group, using external descent theory and
computation. A second certified calculation now realizes an arithmetic
dimension-only separation using 1309a1: its finite two-primary group has
order at least sixteen. The later literature-backed eight-descent
refinement below proves its exact order sixteen and realizes the paired
H_4 lane. The additional partner 2045b1 preserves the other coarse finite
inputs as well. Unequal two-primary orders force unequal whole finite
factors without computing their odd parts. Arithmetic determinant-line
comparison remains open.
The manuscripts are unchanged. The finite implementation is
`lean/SixBirdsBSD/Apparatus/FinitePairings.lean`.

## Carrier, observations, and target

Let H_n = (Z/n)^2, with coordinatewise addition and pairing

    B_n((a,b),(c,d)) = (ad-bc)/n modulo Z.

The implementation uses `Fin n` for residues, with rational representatives
`k/n`. Congruence modulo integers is checked by reduced denominator one;
`sameClassIffIntegerDifference` proves that this is precisely an integral
difference. The cyclic-target embedding respects addition and is injective
for n = 2 and n = 4.

Group laws and alternation/biadditivity are checked on the actual carriers.
Perfectness quantifies over every additive character into `Fin n`, not a
supplied character-coordinate tag. A character is determined by its values
on the two generators; those values yield a unique pairing representative.
This directly proves perfectness for the specified cyclic targets. Their
interpretation as Q/Z pairings uses the elementary fact that characters of
an exponent-n group take values in the n-torsion of Q/Z; the implementation
does not construct the entire Q/Z quotient or quantify over its characters.

Complete duplicate-free enumerations certify the group orders and filtered
two-torsion counts. A concrete additive embedding identifies H_2 with
H_4[2]; unique two-coordinate linear combinations certify their common
two-torsion basis size of two.

## Two independent losses of information

The dimension-only observation has the same value on H_2 and H_4: each
has four two-torsion elements and the displayed two-element basis. Their
orders are 4 and 16. `noOrderReadoutFromTwoTorsionCount` proves that no
function through this observation recovers both orders. This quantifies
over every readout, rather than checking one proposed formula. The theorem
`FiniteSource.dimShaShadow` now includes perfectness and the concrete
equal-two-torsion/unequal-order witness alongside its coordinate residual.

Conversely, H_4 and H_2 direct-sum H_2 both have order 16 and carry perfect
alternating pairings. Their two-torsion has orders 4 and 16, respectively.
`noTwoTorsionReadoutFromOrder` proves that no cardinality-only readout
recovers both two-torsion counts. The direct-sum perfectness proof restricts
an arbitrary character to the two summands and uses their proved
perfectness. The zero pairing fails this same character-representation
criterion, giving a false-target control.

These witnesses establish two finite information requirements. Dimension
alone cannot return group order, and group order alone cannot return the
paired-group carrier's two-torsion structure. Necessity is relative to
these observations and targets. It does not establish indispensability of
each named arithmetic source for scalar BSD.

## Numerical Pfaffian normalization

On the standard ordered generators, the numerical Pfaffians are 1/2 and
1/4. Their reciprocal squares equal the corresponding orders 4 and 16.
This is checked for these presentations only.

On H_4 the additive automorphism (a,b) -> (3a,b) sends the ordered
generators to another ordered generating pair. Evaluating the same
pairing on that pair changes the numerical representative from 1/4 to
3/4. Both classes have order four, but the numerical Pfaffians differ.
This is a basis-change obstruction in addition to the rational-lift
obstruction already proved in `NormalizationChecks`.

Therefore the raw numerical Pfaffian cannot be used as a basis-independent
BSD cardinality factor. An integral presentation and its determinant-line
transport, plus orientation and generator conventions, remain necessary
for the proposed arithmetic return. This checkpoint preserves the valid
finite-shadow construction without treating that remaining comparison as
proved.

## Integral presentation repair

`FinitePresentation.lean` now constructs the integer matrix

    A_n = [[0,n],[-n,0]],    A_n(a,b) = (nb,-na).

For every positive n, the proof identifies equality of residues with
differing by the image of this map. The actual quotient by that relation
is in additive bijection with H_n. Its addition agrees with addition of
integer representatives, and associativity, commutativity, zero, and
inverses are proved on the quotient.

A complete duplicate-free enumeration of this cokernel proves that its
order equals |det A_n| = n^2. This is a return theorem for a determinant
computed from the integer map, rather than a certificate assigning its
value to the desired order. The absolute integral Pfaffian is n and its
square is the finite cardinality factor.

The matrix inverse is constructed over the rationals and both inverse
identities are proved. The linking form is

    -x^t A_n^{-1} y = (x_1 y_2 - x_2 y_1)/n modulo Z.

Adding an image element to either representative changes this rational
lift by an explicitly computed integer. This proves well-definedness
modulo integers from the presentation. On H_2 and H_4, exhaustive kernel
checks recover the previous cyclic-target pairings. Omitting the displayed
minus sign gives a different class at n = 4, so the sign is substantive.

For any integer two-by-two basis matrix B, the upper-right coefficient
of B^t A_n B is proved to be n det B. If det B is +1 or -1, its squared
absolute value remains n^2. In particular,

    B = [[3,4],[4,5]],    det B = -1,

is an actual unimodular lift of the earlier finite basis change on H_4.
It changes the integral Pfaffian from 4 to -4 while preserving the
normalized cardinality factor 16. This repairs the finite example's
normalization without reading 3/4 as an intrinsic scalar Pfaffian.

The proof covers the trivial group at n = 1 with factor one. False-target
controls reject the singular modulus-zero map and a nonunimodular change
that kills a nonzero residue and changes the squared coefficient to 64.
The theorem `noNormalizedFactorFromTwoTorsionCount` now separates the
computed integral factors 4 and 16 using the earlier dimension shadow.

This construction distinguishes three quantities: the chosen rational
pairing coefficient 1/n, the absolute integral Pfaffian n, and the group
order n^2. A scalar BSD Sha factor uses the last quantity when Sha is
finite. Identifying a manuscript determinant-line Pfaffian with that
factor requires its precise duality, square, generator, and transport
conventions. No equality with the arithmetic readout is asserted here.

## Arithmetic two descent for 571a1

The primary Cremona model is

    E: Y^2 + Y = X^3 - X^2 - 929 X - 10595.

A direct PARI/GP 2.15.4 calculation now establishes more than the recorded
analytic Sha value. With random seed one, `ellrankinit(E)` prepares the
descent number field. Applying full `bnfcertify` to its cubic bnf returns
one; the prepared data is then used for `ell2cover` and `ellrank`.
This matters because ordinary number-field class-group initialization is
conditional on GRH until certified. The
[official certification contract](https://pari.math.u-bordeaux.fr/dochtml/html-stable/General_number_fields.html#bnfcertify)
states that full certification removes that condition. No analytic BSD
ratio is used here.

The exact output is

    rational torsion order: 1
    ellrank: [0,0,2,[]]
    number of basis covers: 2

The [official ellrank interpretation](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Elliptic_curves.html#ellrank)
gives algebraic rank bounds zero and zero and rank two for
Sha[2]/2Sha[4]. The torsion calculation gives no rational two-torsion.
The identity C = T + upper + s therefore gives two-Selmer dimension two.
Its exact sequence, with the rank-zero/torsion-one Mordell-Weil quotient,
identifies the two-Selmer group with Sha[2]. These are arithmetic
algorithm outputs interpreted through the standard descent theorems,
not Lean evaluations of an arithmetic Sha type.

Two explicit quartic covers have equations y^2 = Q_i(x), where

    Q_1 = -4x^4 - 60x^3 - 232x^2 - 52x - 3
    Q_2 = -11x^4 - 68x^3 - 52x^2 + 164x - 64.

`Closure/ShaDescent.lean` checks their actual map identities. If N_i and
A_i are the recorded numerator polynomials, then

    A_i^2 = 4 N_i^3 - 4 N_i^2 Q_i - 3716 N_i Q_i^2 - 42379 Q_i^3.

Thus away from y=0 the formulas X=N_i/y^2 and 2Y+1=A_i/y^3 satisfy the
displayed equation of E. Lean proves the polynomial identities for every
rational x. It does not merely assume that the covers have this target.

Both quartics have I=44608 and J=18842960. The Jacobian model in
[Fisher, Section 2 and Lemma 2.1](https://arxiv.org/html/2208.14977v1)
is y^2=x^3-27 I x-27 J; the computed coordinate change
`(X,Y) -> (36X-12,216Y+108)` carries E to that model and has an explicit
rational inverse. Lean checks the coordinate equations. Fisher's
discriminant convention is sixteen times the ordinary polynomial
discriminant: these are respectively -2338816 and -146176. The latter
is the `poldisc` output, with support exactly `{2,571}`. The convention
difference is retained in the fixture. The checked arXiv v1 PDF digest is
`48a8502ffef7db9ca68866d56af96e10fec4f187840a2c07353abb833454a948`.
Fisher's introduction also identifies the implemented ellrank pairing
method and the standard Selmer exact sequence and pairing kernel.

Local-solubility inputs are independently checked rather than inferred
from searching unsuccessfully for rational points:

| Place | First cover | Second cover | Return theorem |
| --- | --- | --- | --- |
| Real | Q_1(-2/17)=293/83521>0 | Q_2(-15/4)=101/256>0 | positive real square root |
| Two | Q_1(1)=-351=1 mod 8 | Q_2(1)=-31=1 mod 8 | odd two-adic square criterion |
| 571 | residue point (0,219) | residue point (2,139) | Hensel, since 2y is nonzero mod 571 |

At every other odd prime, the quartic discriminant is a unit, so the
smooth projective genus-one model has good reduction. The genus-one
Weil bound gives at least one finite-field point, which lifts by
smoothness. Lean checks the table's exact numerical conditions; the
real/local fields, square criterion, Hensel lemma, smooth genus-one
models, and Weil bound are standard mathematical imports, not
mechanized constructions in this project. Completeness and independence
of the two-Selmer basis still rely on the certified descent computation.

### Why the two primary group is finite

The pairing rank equals the dimension of Sha[2], so its restriction there
is nondegenerate. If x is killed by four and y is killed by two, then

    <2x,y> = <x,2y> = 0.

Nondegeneracy on Sha[2] forces 2x=0. Repeating this argument descends
from every power-of-two annihilator. Hence Sha[2^infinity]=Sha[2],
including exclusion of a divisible two-primary tail, without assuming
the entire Sha group is finite. Since Sha[2] has dimension two, this
identifies the two-primary group with H_2, of order four. Its alternating
nondegenerate pairing in any two-element basis has off-diagonal class
1/2, giving the previously constructed hyperbolic pairing.

Lean derives `noNonzeroDoubleOfFourTorsion` from balanced doubling and
nondegeneracy, then proves `primaryCollapse` for every annihilator
exponent and constructs inverse maps between the actual two-primary and
two-torsion subtypes. It also checks that H_2 satisfies the pairing
hypotheses. H_4 is an essential false-target control: its full pairing is
perfect but its restriction to H_4[2] is zero, so the new premise fails
and a nonzero four-torsion double survives. Knowing only the two-torsion
dimension would not justify this collapse.

### Arithmetic scope and self review

This establishes a nontrivial two-primary arithmetic witness using
certified PARI descent and standard arithmetic theorems, with exact
polynomial/local inputs and the torsion return separately proved in
Lean. It does not prove the whole Sha group has order four, exclude
odd-primary components, verify the arithmetic Selmer-complex determinant
presentation, or populate the odd-prime Stark/Pfaffian comparison at
prime two. No conclusion is inserted into a supplied arithmetic
certificate field. The trusted boundary includes the external descent
implementation and standard local/descent theorems; Lean does not
independently implement those algorithms or their cohomology.

Self-review checked the class-group certification, exact output semantics,
map and discriminant conventions, local completeness argument, and the
higher-torsion exclusion. It also checked the H_4 failure control. The
other arithmetic carrier was not realized by this first calculation.
The comparison below now supplies one, with the narrower observation
interface made explicit. Neither calculation proves the whole
named-source indispensability claim.

The fixture is `sha_descent_571a1.json`. Run
`scripts/check_sha_descent.py --check` for offline exact checks, or add
`--gp` with a PARI/GP executable to reproduce the certified arithmetic
descent. Offline validation expressly does not verify basis completeness
or pairing rank from the stored metadata.

## Arithmetic dimension-only separation: 571a1 and 1309a1

The second primary Cremona model is

    F: Y^2 + Y = X^3 - 406957 X - 99924251.

The exact allcurves and allbsd rows and their file digests are retained
in `sha_dimension_arithmetic_pair.json`. The allbsd Sha column, sixteen,
was useful for selecting a candidate. It is not used as an arithmetic
order or upper bound. Direct PARI/GP 2.15.4 calculations on the equation,
with random seed one and full cubic-field `bnfcertify`, give:

| Input/output | 571a1 | 1309a1 |
| --- | --- | --- |
| Class-group certification | [1] | [1] |
| Rational torsion order | 1 | 1 |
| ellrank | [0,0,2,[]] | [0,2,0,[]] |
| Two-Selmer basis size | 2 | 2 |

For 1309a1 the descent alone allows rank zero or two. Failure to find
points does not settle this ambiguity. We resolve it separately, using
an exact modular symbol and the established nonvanishing theorem.

### Nonvanishing and finiteness, without a BSD order formula

Using a 128 MB GP stack, `[M,sy]=msfromell(F,1)` has level 1309 and
weight two. Both `msissymbol(M,sy)` and the corresponding check on its
generator evaluations return one. The evaluation

    mseval(M,sy,[oo,0]) = 64

is nonzero; reversing the path gives -64. The path `[oo,0]` represents
the divisor `[0]-[oo]`. The
[official normalization contract](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Modular_symbols.html#msfromell)
identifies this evaluation with L(F,1)/Omega^+, where Omega^+ is positive.
Only nonvanishing is needed, so changing the nonzero rational scaling
of the eigensymbol would not affect the argument.
The library's real-period calibration uses numerical computation and
rational reconstruction (see the
[PARI scaling implementation](https://pari.math.u-bordeaux.fr/lcov-report/basemath/modsym.c.gcov.html),
`msfromell_scale`); a rational output by itself is not an exact
normalization proof. The independent Hecke/lattice calculation below
establishes the absolute ratio without that calibration. The earlier
nonvanishing deduction only needs the exact eigensymbol line and its
nonzero path evaluation.

All 288 coefficients of `msqexpansion(M,sy,288)` agree with
`ellan(F,288)`. This is the weight-two Sturm bound at squarefree level
1309: the Gamma_0 index is (7+1)(11+1)(17+1)=1728, and 2*1728/12=288.
The [standard Sturm-bound contract](https://doc.sagemath.org/html/en/reference/arithgroup/sage/modular/arithgroup/arithgroup_generic.html#sage.modular.arithgroup.arithgroup_generic.ArithmeticSubgroup.sturm_bound)
uses this weight and index.
The comparison supplements the algorithm's attached-newform contract;
it does not claim to mechanize modularity, modular symbols, or Sturm's
theorem. The first twenty coefficients are retained in the fixture.

The established modularity and Kolyvagin nonvanishing theorem now gives
rank F(Q)=0 and finite Sha(F/Q). The precise finiteness implication is
recalled at the opening of Section 8 of
[Stein and Wuthrich, Computing Tate-Shafarevich Groups of Elliptic Curves Using Iwasawa Theory](https://www.maths.nottingham.ac.uk/plp/pmzcw/download/shark.pdf)
(3 May 2011 draft, printed page 28; checked PDF digest in the fixture).
We do not use that section's subsequent odd-prime Iwasawa bounds at two.
The computed j-invariant is nonintegral, excluding CM as well; Lean
checks the nonzero remainder of c4^3 on division by the discriminant.
These arithmetic theorems and the exact modular-symbol algorithm remain
external to Lean.

### Return from the zero pairing rank

Write G=Sha(F/Q). The documented descent identities are

    C = T + upper + s = T + R + S,
    s = dim_F2(G[2]/2G[4]).

Here T=R=s=0 and C=2, so S=dim_F2 G[2]=2. Since s=0,
G[2]=2G[4]. This is substantive extra information about halving, beyond
the two-torsion dimension.

Choose a half h(a) of each a in G[2]. Each such half belongs to G[4].
There is an explicit set bijection

    G[2] x G[2] -> G[4],       (a,b) |-> h(a)+b,
    G[4] -> G[2] x G[2],       x |-> (2x, x-h(2x)).

Both inverse identities follow from the abelian-group laws and 2h(a)=a.
Consequently #G[4]=#G[2]^2=16. Finiteness of G, proved above, ensures
its two-primary subgroup is finite. It contains G[4], so its order is
at least sixteen. No upper bound on its exponent or order is inferred.
In particular, this two-descent evidence alone does not prove that its
full two-primary paired group is the perfect H_4 model; excluding higher
layers requires the separate eight-descent input below.

`Closure/ShaDimensionPair.lean` derives doubling from actual abelian
addition, constructs these maps and both inverses, and produces a
complete duplicate-free sixteen-element enumeration of G[4] from an
underlying four-element parametrization of G[2]. An existential halving
premise supplies the chosen section through `chooseHalf`; no order is a
field of the input. `primaryOrderLowerBound` proves the lower bound for
any complete primary-group enumeration. The first curve's collapse
similarly produces a complete four-element primary enumeration.
`noPrimaryOrderReadoutFromTwoBasis` then rejects every function of the
common dimension two that would return both orders. The arithmetic
groups and their parameterizations are identified by the external
descent interpretation, not by a new Lean arithmetic certificate.

### Exact arithmetic scope and self review

We have two actual rational elliptic curves with

    dim_F2 Sha(571a1)[2] = dim_F2 Sha(1309a1)[2] = 2,
    #Sha(571a1)[2^infinity] = 4,
    16 <= #Sha(1309a1)[2^infinity] < infinity.

Thus no dimension-only function recovers the two-primary order on the
domain of curves for which that subgroup is finite. This is a genuine
arithmetic information-loss theorem, with certified external arithmetic
and a separately mechanized group return. It closes the earlier
arithmetic-realization gap for this observation and target, without
requiring the exact second order. The four-torsion orders are also
different, four and sixteen.

The observation is **only the two-torsion dimension**, and the target is
**the two-primary order**. Curve identity, periods, Tamagawa factors,
and the other recognition-source records are not part of this retained
observation. Both curves have algebraic rank zero and rational torsion
order one, but their other arithmetic data differ. This is not an
ablation with all other named sources held fixed, and does not establish
indispensability of any entire Gamma source for scalar BSD.

Self-review checked the unresolved descent rank bound for 1309a1,
the direction/sign of the modular-symbol path, all coefficients through
the Sturm bound, the separate finiteness theorem, the group fiber maps,
and the distinction between a lower bound and an exact order. H_4
supplies an inhabited halving control; H_2 fails the halving premise,
even though its two-torsion dimension is the same. No analytic Sha
table value supplies the arithmetic conclusion. A diagnostic
`msissymbol` check on 571a1's short coordinate column returned zero in
this PARI version. Evaluating on **all path generators**, as below,
resolves that representation mismatch and passes the actual relations.
The first curve's earlier order argument uses only its certified descent
and torsion collapse; it did not depend on this diagnostic.

Run `scripts/check_sha_dimension_pair.py --check` for exact offline model
and quartic invariant checks, or add `--gp` with a PARI/GP executable to
reproduce both certified descents and the second curve's symbol checks
and full coefficient comparison. Offline checks alone do not establish
Selmer completeness, pairing rank, or nonvanishing.

At this checkpoint the optional PARI reproduction passed, as did
`make verify-lean` (83 build jobs, the regression axiom prints and all
51 manifest probes), `make validate`, `make test` (26 tests), and
`make public-audit`. The new declarations' printed axiom closures contain
only the previously permitted `propext`, `Classical.choice`, and
`Quot.sound`. The manuscripts were not edited.

## Eight-descent refinement and a matched finite-source pair

### Exact period normalization from the integral lattice

The eight-descent branch below requires a two-adic valuation of the
analytic candidate, so nonvanishing alone no longer suffices. We first
fix the scale independently of `msfromell`. For each of 571a1, 1309a1,
and 2045b1, set `M=msinit(N,2,1)` and use
`msfromhecke(M,[[2,a2],[3,a3],[5,a5]])`, with the eigenvalues computed
from the integral curve equation. The resulting space has dimension
one. Divide a nonzero basis vector by the positive content of its
evaluations on **all** `mspathgens(M)[1]` paths. This yields an integral
primitive plus symbol `v`, whose generator values have gcd one.
`msissymbol` verifies these full evaluations; `msstar(M)*v=v` verifies
the plus sign. Its normalized q-expansion agrees with the curve through
the full weight-two Sturm bound. This computation uses rational and
integer arithmetic, with no period integration or rational reconstruction.
The relevant exact interfaces are
[msfromhecke](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Modular_symbols.html#msfromhecke)
and
[mspathgens](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Modular_symbols.html#mspathgens).
The latter supplies integral group-ring generators; at weight two the
coefficient action is trivial, so their values generate the entire
value lattice.

Here is the arithmetic return fixing the scale. These curves have
squarefree conductor, negative minimal discriminant, trivial rational
torsion, and singleton rational isogeny classes. Thus they are
semistable and optimal. Theorem 1.2 of
[Cesnavicius, The Manin constant in the semistable case](https://arxiv.org/pdf/1703.02951v3)
gives absolute Manin constant one, so integration of the normalized
newform agrees, up to sign, with integration of the minimal Neron
differential. The checked PDF SHA-256 is
`61cde659ac3089225539b58bfdf0082cb63ce39d1ca8bd7f8952b424e7132b6c`.
This is arXiv v3, submitted 26 April 2018; its downloaded PDF has
internal date 14 July 2021. Section 2 of
[Wuthrich, Numerical modular symbols for elliptic curves](https://www.maths.nottingham.ac.uk/plp/pmzcw/download/modsym.pdf)
(20 March 2017, printed pages 3-4) explains the optimal period-lattice
generation and torsion images of cusps. Its Manin-constant assumption
is discharged here by the cited semistable theorem.

At squarefree level every cusp is rational. Manin-Drinfeld makes its
image, relative to the infinity cusp, a rational torsion point, hence
zero on these curves. Therefore every cusp-to-cusp path integral is an
elliptic period. Conversely, optimality means that the Jacobian quotient
has connected kernel; the homotopy sequence of complex tori makes its
map on integral first homology surjective. Abel-Jacobi identifies the
homology of the modular curve with that of its Jacobian. Closed cycles
are generated by cusp paths, so these integrals generate the **whole**
elliptic period lattice, not merely a sublattice. This proves equality
in both directions rather than just a denominator bound.

Negative discriminant gives connected real locus and the lattice
`Z*Omega^+ + Z*(Omega^+/2 + i*b)`, with `b>0`. Its real projection is
exactly `(Omega^+/2)*Z`. Thus the normalized plus symbol has value
lattice `(1/2)*Z`. Since it lies in the same one-dimensional Hecke
eigenline as `v`, whose value lattice is `Z`, its scale is `v/2` up to
sign. Consequently:

| Curve | Primitive absolute value on [oo,0] | Absolute L-value / Omega^+ |
| --- | --- | --- |
| 571a1 | 8 | 4 |
| 1309a1 | 128 | 64 |
| 2045b1 | 32 | 16 |

This proves the absolute ratios from an exact eigensymbol and an
independently justified lattice normalization. It does not choose an
orientation or prove the signed comparison required by the paper.
Absolute values suffice for the two-adic branch valuations below.
The modularity, Manin-Drinfeld, optimality, and integral period-lattice
arguments remain arithmetic imports and a written proof, external to
the mathlib-free Lean development.

### Independently established arithmetic upper bound

[Miller, arXiv:1010.2431v3](https://arxiv.org/pdf/1010.2431v3)
(21 December 2011), proof of Theorem 7.1, printed page 16, reports
the following intermediate computational results for optimal curves
of conductor less than 5000. When the analytic two-primary candidate
has valuation four, a four-descent gives Sha[4] isomorphic to (Z/4)^2
and an eight-descent gives Sha[8]=Sha[4]. The latter is the new input
used here. It is an established arithmetic computation in the proof,
rather than a deduction from a conjectural BSD equality. The checked
PDF SHA-256 is
`52cbe68361e6eb07f94e13197a88eb5295c3f92e339a65d1488324d5489055ae`.
The published computation is not independently rerun by our GP script.
This refinement has an additional literature trust boundary; the
two-descent-only lower-bound theorem above remains available separately.

For 1309a1, independent applicability computations give:

- The integral equation is already globally minimal, and its rational
  isogeny class has one isomorphism class, from `ellisomat`. Hence this
  curve is optimal. Its nonintegral j-invariant verifies the non-CM
  scope of that isogeny-class algorithm.
- Its discriminant is -7^6*11^3*17^2, with primitive c4 at each bad
  prime. The local outputs are I6/c7=2, I3/c11=1, I2/c17=2. The finite
  Tamagawa product is four. GP recomputes these from the equation.
- The discriminant is negative, so there is one real component and the
  connected real period Omega^+ is the full real period. The torsion
  order is one and the rank-zero regulator is one.
- The independently established absolute ratio |L(E,1)|/Omega^+=64 gives
  analytic candidate 64/4=16, of two-adic valuation four. This is a
  branch-applicability calculation, not an assumed arithmetic order.

Thus the **eight-descent result in the proof**, rather than its final
BSD formula, applies to the same primary equation. If every element
killed by eight is already killed by four, induction on any two-power
annihilator proves the entire two-primary group is killed by four.
`ShaFourNormalization.primaryCollapseToFour` proves this without
ambient finiteness, and `primaryFourEquivalence` constructs inverse
maps between the actual primary and four-torsion subtypes. Combined
with the previous halving return, the module now constructs a complete
duplicate-free primary enumeration of length sixteen. H_8 supplies a
false control with a surviving higher layer. Neither the analytic
candidate nor an allbsd Sha entry supplies this upper bound.

### A partner preserving the other finite inputs

The new primary Cremona model is

    J: y^2 + xy = x^3 - x^2 - 5470x - 862675  (2045b1).

Its invariants are c4=262569, c6=746532747, Delta=-5^17*409, checked
from the integer equation in Lean. The equation is globally minimal;
its rational isogeny class is also a singleton. Certified PARI
two-descent gives torsion order one, `ellrank=[0,2,0,[]]`, and two
Selmer basis covers, with full class-group certification. Its exact
primitive plus symbol has absolute value 32 on `[oo,0]`, giving
absolute period-normalized value sixteen as proved above; all 410 Fourier
coefficients through the weight-two bound at level 2045 match the
curve. Nonvanishing gives rank zero and finite Sha as before. Its
local reductions are I17/c5=1 and I1/c409=1, giving Tamagawa product
one. Negative discriminant gives one real component, so the analytic
candidate is 16/1=16. The same independently established eight-descent
result applies. Hence its two-primary group is H_4, of order sixteen.

The original first curve has I1/c571=1 and good reduction elsewhere,
so its Tamagawa product is one as well. In fact every finite-place
Tamagawa number of both 571a1 and 2045b1 is one: this is the good-place
component theorem together with the displayed bad-place calculations.
Their rational torsion groups are both trivial. Consequently:

| Retained arithmetic information | 571a1 | 2045b1 |
| --- | --- | --- |
| Algebraic rank | 0 | 0 |
| Every finite-place Tamagawa number | 1 | 1 |
| Rational torsion group | trivial | trivial |
| Two-torsion Sha dimension | 2 | 2 |
| Two-primary Sha order | 4 | 16 |

Every function of the Tamagawa product, torsion order and two-torsion
dimension returns the same value on this pair, so cannot recover their
unequal two-primary finite factors. `noFiniteFactorReadoutFromCoarseInputs`
proves the generic return from the collapse, halving, and eight-torsion
stabilization premises. The two enumeration lengths are derived, not
fields of a certificate. The arithmetic binding uses the exact
algorithms and the separately identified published computation above.
This is stronger than freezing only the dimension. It still excludes
the analytic coefficient and period, curve identity, and other named
recognition-source records. Those are not held fixed; no full-Gamma
indispensability for scalar BSD follows.

### Return to the whole finite factor without computing odd parts

The nonzero exact plus symbols and the established nonvanishing theorem
give finiteness of the whole Sha group for both 571a1 and 2045b1. Finite
abelian-group primary decomposition therefore writes their whole orders
as `4*u` and `16*v`, where `u` and `v` are positive odd integers. These
orders cannot agree: the first is congruent to four modulo eight, and
the second to zero. Thus the whole Sha orders differ even though
neither odd factor has been computed. Because both rational torsion
groups are trivial, their whole finite BSD factors `#Sha/#tors^2`
differ as well. No BSD equality is used in this deduction.

`unequalWholeOrdersFromPrimaryLayers` proves the arithmetic congruence;
`noWholeFiniteFactorReadoutFromCoarseInputs` combines it with the derived
primary enumeration lengths. This quantifies over every readout of the
same coarse finite inputs and arbitrary odd complements, rather than
assuming exact full Sha orders. The finite primary decomposition and
arithmetic binding remain external to Lean. Hence the pair obstructs
recovery of the **whole** finite factor through those retained inputs,
in addition to obstructing its two-primary part. Exact numerical whole
orders and the other named-source ablations are separate obligations.

### Paired arithmetic realization and integral normalization

The full Sha groups of these rank-zero curves are finite by the
nonvanishing theorem. The elliptic-curve Cassels–Tate pairing is
alternating and nondegenerate after quotienting by the maximal divisible
subgroup; for finite groups that subgroup is zero. See
[Poonen and Stoll, Introduction](https://math.mit.edu/~poonen/papers/sha.pdf)
(1999, author PDF with minor correction dated 23 August 2014; SHA-256
`3b9a619423358bc877fd2123b73a759157a728ec11e0f7b0aa48bd0333d7149a`).
Distinct primary components are orthogonal by biadditivity and coprime
annihilators. Thus the two-primary restrictions are perfect alternating
forms. The first is the earlier H_2 form; the two order-sixteen partners
are perfect forms on H_4. This realizes the arithmetic finite paired
lane that was previously open, with the published descent dependency
made explicit.

Lean now classifies **every** alternating nondegenerate form B on
`Plane 4`, not just an assigned standard matrix. The existing additive
character theorem derives

    B(x,y) = u*(x1*y2-x2*y1),  u=B(e1,e2) in Z/4.

Alternation eliminates the diagonal terms and fixes the reversed
coefficient. Nondegeneracy forces u=1 or u=3: either even coefficient
has the nonzero radical vector (2,0). The additive involution
`(x1,x2) -> (u*x1,x2)` then carries B to the standard pairing.
`perfectFourFormIntegralReturn` composes this derived normalization
with the actual integer presentation A4=[[0,4],[-4,0]]. Its linking form
recovers B modulo integers and its positive determinant is the actual
cokernel order sixteen. Degenerate alternating forms and a nonalternating
nondegenerate dot product are checked false controls.

This gives an integral presentation **of the finite paired group**.
It does not identify A4 with the particular arithmetic Selmer complex,
choose the Stark generator in the manuscript's odd-prime comparison,
or compare its determinant-line orientation with analytic/local maps.
A positive cardinality factor and a raw rational Pfaffian coefficient
remain distinct; selecting a torsion-value lift is still not canonical.
All three curves here are semistable. Their finite-group examples do
not supply the additive-prime hypotheses of the Gamma sources. Moreover
1309a1 has two dividing its Tamagawa product, outside the corresponding
chi_CT applicability condition at two. The matched 2045b1 pair avoids
that Tamagawa obstruction, but prime two is still outside the cited
odd-prime Stark-system scope.

### Representation check, reproducibility, and self review

For the `msfromell` computations on 571a1, the symbol coordinate column has length 95 but
`mspathgens(M)[1]` has 97 paths; for 2045b1 these lengths are 409 and
413. In the checked PARI version, the weight-two `msissymbol` routine
expects values on **all** generators. Its short-column checks return
zero. Computing `ev[i]=mseval(M,sy,path[i])` for every listed path
returns a complete generator vector and `msissymbol(M,ev)=1` in both
cases. This resolves the earlier diagnostic without assuming a failed
check was harmless. The nonzero path values are four and sixteen.

`sha_four_normalization.json` records the source versions/digests,
equations, exact local outputs, and applicability calculations.
`scripts/check_sha_four_normalization.py --check` checks their numerical
consistency offline; `--gp` additionally reproduces minimality,
singleton isogeny classes, local reductions and the new descent/symbol
evidence. Separately, it reconstructs all three plus eigensymbols from
exact Hecke matrices and checks primitive generator values and the full
Sturm comparisons. Their sign-restricted coordinate columns have lengths
48, 148 and 206; the path counts remain 97, 289 and 413. The arithmetic
lattice argument fixes their absolute normalization. The checker
expressly does not reproduce the published eight-descent or mechanize
that lattice argument.

Self-review checked the optimality and T=4 applicability conditions,
period-component convention, integral-lattice surjectivity and equality,
the semistable Manin theorem's hypotheses, scale-free eigensymbol
construction, separation of analytic candidate from
arithmetic upper bound, the published proof's actual intermediate
statement, exclusion of every higher two-power tail, the derived unit
coefficient and inverse coordinate change, and the finite-presentation
versus arithmetic-complex distinction. The trust boundary includes
published computation and standard arithmetic theorems beyond Lean.
The full named-source endpoint remains open; no main paper claim has
been changed.

## Resume point

The finite determinant readout and its return are now constructed for
the hyperbolic integral presentations above. The next arithmetic task is
to identify the relevant integral Selmer-complex presentation and its
pairing with the actual Sha/Tamagawa/torsion data, then prove compatibility
of this normalization with the analytic and local comparison maps.
The exponent-two lane and an arithmetic dimension-only partner are now
realized above. The published eight-descent refinement also realizes
perfect H_4 and a pair freezing the other finite inputs. A pair holding
the analytic and other named recognition sources fixed, and the
arithmetic complex's determinant-line comparison, remain separate
obligations. The rational
conditional assembly and support-coverage results remain documented in
`source_indispensability.md`; this construction supplies concrete finite
carriers rather than resolving their arithmetic hypotheses.
