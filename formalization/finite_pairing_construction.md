# Finite paired-group construction checkpoint

This construction replaces dimension/exponent metadata with actual finite
groups. The Lean group construction is finite algebra. The separate
certified two-descent below now identifies its exponent-two lane with
571a1's two-primary arithmetic group, using external descent theory and
computation. The exponent-four partner and arithmetic determinant-line
comparison remain open. The manuscripts are unchanged. The implementation is
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
other arithmetic ablation carrier with the same two-torsion and a
different finite factor is not realized here, so this is not a proof of
the whole named-source indispensability claim.

The fixture is `sha_descent_571a1.json`. Run
`scripts/check_sha_descent.py --check` for offline exact checks, or add
`--gp` with a PARI/GP executable to reproduce the certified arithmetic
descent. Offline validation expressly does not verify basis completeness
or pairing rank from the stored metadata.

## Resume point

The finite determinant readout and its return are now constructed for
the hyperbolic integral presentations above. The next arithmetic task is
to identify the relevant integral Selmer-complex presentation and its
pairing with the actual Sha/Tamagawa/torsion data, then prove compatibility
of this normalization with the analytic and local comparison maps.
The exponent-two lane now has the separate arithmetic realization above.
Realization of its ablation partner on elliptic-curve data is still
needed for the original source-indispensability claim. The rational
conditional assembly and support-coverage results remain documented in
`source_indispensability.md`; this construction supplies concrete finite
carriers rather than resolving their arithmetic hypotheses.
