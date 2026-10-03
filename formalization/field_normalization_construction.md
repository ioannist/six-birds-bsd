# Field normalization and the conditional BSD factors

The paper's target is a conditional BSD-to-Six-Birds closure, not an
unconditional arithmetic theorem. This repair derives its normalization
algebra and exact cancellation conditions over a lawful scalar field.
The arithmetic factors and their recognition comparisons remain supplied.
The manuscripts and public landing statements are unchanged.

## Exact meaning of normalization

Write `Omega`, `Reg`, `Tam`, `Sha`, `d` and `kappa` for the period,
regulator, global Tamagawa product, Sha cardinality, torsion square and
cascade coefficient. Put `C=Omega*Reg*Tam`. Over a field, if C is nonzero,

    kappa*C = (Sha/d)*C iff kappa=Sha/d.

The standard BSD product `((Sha*Reg)*Omega)*Tam/d` equals `(Sha/d)*C`
by commutativity and the field division law. Thus the comparison concerns
the same right side as the shell's formula, including its parenthesization
and factor ordering. No leading coefficient identity is assumed to
prove this comparison.

`kappaNormalizationOverField` proves cancellation of C;
`cascadeProductIffNormalization` derives the comparison with the actual
standard product. `commonFactorNonzero` constructs the nonzero common
factor from the three nonzero period/regulator/Tamagawa inputs. The
pre-existing integer theorem `kappaRNormalizationEquivalence` remains
available for the legacy AOR caller, while these additional declarations
handle fractional coefficients and any separately supplied lawful field
instance on the intended real scalar carrier.

When `d != 0`, `normalizationIffCrossProduct` additionally proves

    kappa=Sha/d iff kappa*d=Sha.

`cascadeProductIffCrossProduct` composes both equivalences. The explicit
nonzero denominator is indispensable when clearing it. Field division
is totalized at zero, so some quotient identities also hold there; those
are not interpretations of a BSD torsion denominator.

Given the normalization, `normalizedLeadingFormsEquivalent` proves
equivalence of the cascade and standard leading-term equations for every
leading coefficient. Conversely, `allLeadingFormsIffNormalization` proves
that uniform equivalence for all leading values implies the normalization:
evaluate the equivalence at `leading=kappa*C` and cancel C.

This clarifies the paper's word “agrees”: its proof compares the two
right-hand sides. Merely asking whether both equations have the same
truth value at one fixed leading value is weaker. For example `0=1` and
`0=2` are both false and hence logically equivalent, even though one and
two are different coefficients. This control does not contradict the
paper's right-side comparison; it prevents an invalid converse reading.

## Constructed and exactly characterized cancellation

The shell stores arbitrary operations as explicit data. Supplying a field
on its scalar type does not automatically identify its `mul` and `div`
with the field operations. Therefore the new constructor takes the two
operation matches

    shell.mul = field multiplication,
    shell.div = field division.

With nonzero `Reg`, `Omega`, `Tam`, `Sha` and `d`,
`SelShell.factorCancellationFromField` constructs the existing six-law
`FactorCancellation` record. Each ordinary multiplier is invertible;
the mixed multiplier `Sha*Reg*Omega` is nonzero by the same field laws;
division by d is injective because d is nonzero. No independent arithmetic
comparison or source-necessity certificate is added.

`factorCancellationIffNonzero` proves the exact converse as well. If any
one of these factors is zero, its cancellation law applied to zero and
one forces `0=1`, contrary to field nontriviality. The mixed multiplier
law adds no new nonzero requirement. Hence on native operations

    FactorCancellation shell
    iff Reg != 0 and Omega != 0 and Tam != 0 and Sha != 0 and d != 0.

This is a characterization of the algebraic assumptions used by the
composite sensitivity calculation. It is not source indispensability.
It also does not force scalar BSD: the false-leading fixture still has
all five factors one and a constructed cancellation package, while its
leading coefficient is two and the arithmetic right side is one.

For the intended real BSD interpretation, positivity of the period,
positive definite height pairing on a full free Mordell–Weil lattice,
positive finite Tamagawa numbers and nonempty finite group cardinalities
provide these nonzero conditions. In rank zero the regulator is one.
These are standard interpretation inputs; this construction does not
mechanize real positivity or construct the arithmetic groups. Finiteness
of Sha and the rank/regulator interpretation remain visible where needed.

## Adversarial evidence and self-review

The exact rational fixture has `Omega=3/2`, `Reg=4/3`, `Tam=6`,
`Sha=4` and `d=9`. Its common factor is twelve, coefficient `4/9`,
and leading term `16/3`. Replacing the torsion square nine by the
torsion cardinality three gives sixteen instead, rejecting that mistaken
denominator convention. These are algebraic values, not an elliptic curve.

The zero-common control uses unequal coefficients one and two multiplying
zero; the products agree. The zero-denominator control has kappa zero,
Sha four and d zero: both totalized products are zero, but the cleared
equation `0*0=4` fails. The fixed-leading control distinguishes uniform
formula comparison from two false equations at one input. Native field
cancellation is constructed on an inhabited shell, and a separate
false-target shell confirms that cancellation does not supply recognition.

Distinct self-review checked factor ordering, quotient laws at zero,
the exact nonzero boundaries in both directions, the shell/native
operation matches, rank-zero regulator convention, torsion squaring,
the universal leading-value quantifier and the difference between scalar
sensitivity and source-record necessity. The closure target and accepted
arithmetic premises remain intact.

Verification uses a full Lean build, regression target and live 51-entry
manifest probe, static validators, public hygiene and all 26 unit tests.
The new declarations have printed axiom closures restricted to standard
Lean foundations. Alignment categories remain unchanged because the
manifest normalization theorem is still the legacy integer declaration
and its arithmetic/real interpretation is not independently mechanized.
