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

## Resume point

The next arithmetic task is to construct the normalized finite determinant
readout and prove its return to the actual Sha/Tamagawa/torsion factor.
Separate realization of ablation witnesses on elliptic-curve data is still
needed for the original source-indispensability claim. The rational
conditional assembly and support-coverage results remain documented in
`source_indispensability.md`; this construction supplies concrete finite
carriers rather than resolving their arithmetic hypotheses.
