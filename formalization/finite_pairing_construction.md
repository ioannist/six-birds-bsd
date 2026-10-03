# Finite paired-group construction checkpoint

This construction replaces dimension/exponent metadata with actual finite
groups. It is a finite-algebraic result; no elliptic-curve realization or
arithmetic determinant-line comparison is asserted. The manuscripts are
unchanged. The implementation is
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

## Resume point

The finite determinant readout and its return are now constructed for
the hyperbolic integral presentations above. The next arithmetic task is
to identify the relevant integral Selmer-complex presentation and its
pairing with the actual Sha/Tamagawa/torsion data, then prove compatibility
of this normalization with the analytic and local comparison maps.
Separate realization of ablation witnesses on elliptic-curve data is still
needed for the original source-indispensability claim. The rational
conditional assembly and support-coverage results remain documented in
`source_indispensability.md`; this construction supplies concrete finite
carriers rather than resolving their arithmetic hypotheses.
