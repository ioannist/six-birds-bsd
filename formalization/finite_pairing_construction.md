# Finite paired-group construction checkpoint

This construction replaces dimension/exponent metadata with actual finite
groups. The Lean group construction is finite algebra. The separate
certified two-descent below now identifies its exponent-two lane with
571a1's two-primary arithmetic group, using external descent theory and
computation. A second certified calculation now realizes an arithmetic
dimension-only separation using 1309a1: its finite two-primary group has
order at least sixteen. Its exact two-primary order, perfect paired H_4
identification, and arithmetic determinant-line comparison remain open.
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
In particular, this does not prove that its full two-primary paired
group is the perfect H_4 model; higher two-power layers remain possible
on this evidence.

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
`msissymbol` check on 571a1's symbol returned zero in this PARI version;
that unexpected check is not used as evidence here. The first curve
uses the certified descent and torsion collapse, and the second curve
passes both symbol checks. Diagnosing the first symbol check remains a
separate implementation question.

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

## Resume point

The finite determinant readout and its return are now constructed for
the hyperbolic integral presentations above. The next arithmetic task is
to identify the relevant integral Selmer-complex presentation and its
pairing with the actual Sha/Tamagawa/torsion data, then prove compatibility
of this normalization with the analytic and local comparison maps.
The exponent-two lane and an arithmetic dimension-only partner are now
realized above. An exact perfect H_4 realization and a pair holding the
other named sources fixed remain separate obligations. The rational
conditional assembly and support-coverage results remain documented in
`source_indispensability.md`; this construction supplies concrete finite
carriers rather than resolving their arithmetic hypotheses.
