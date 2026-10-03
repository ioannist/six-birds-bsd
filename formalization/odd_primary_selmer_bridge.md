# Ordinary three-primary Selmer-complex construction

This is a supporting construction, with arithmetic imports separated from
Lean finite algebra. It does not change the manuscripts or prove the
full named-source indispensability claim. It gives an actual ordinary
arithmetic instance, an identification of its compact Selmer complex
in the derived category, and a basis-unit obstruction on the same curve.

## Why the matched two-primary pair does not supply this bridge

The 2045b1 equation has good ordinary reduction at two, with
`a_2=1` and `#E_tilde(F_2)=2`. The Tamagawa product one does not discharge
the non-anomalous condition. In fact good ordinary reduction at two
means `a_2` is odd, so `3-a_2` is always even. Merely removing the odd-prime
restriction from the cited theorem would still leave this hypothesis
false. `ordinaryAtTwoIsAnomalous` proves the parity return uniformly;
`matchedPartnerHasLocalAnomaly` counts the actual equation.

This is a substantive local defect. The ordinary unramified quotient has
unit-root Frobenius `alpha`, with `alpha^2-alpha+2=0`. Since `alpha` is a
two-adic unit, `alpha*(alpha-1)=-2` gives `v_2(alpha-1)=1`. Consequently
the fixed subgroup of `Q_2/Z_2` in that quotient is cyclic of order two.
The mod-four root and fixed-class controls are checked in Lean; the
script checks the first seven finite levels as controls, rather than
claiming those levels prove a limit. The valuation calculation proves
the limiting invariant order. The local-condition quotient also has
order two by
[Greenberg, Iwasawa theory for elliptic curves, Proposition 2.5](https://arxiv.org/pdf/math/9809206v1),
printed page 19. Thus a comparison with classical local conditions
requires this correction, not just an extension of the numerical prime
scope. The checked Greenberg PDF digest is in the JSON fixture.

## A nonzero odd-primary arithmetic lane

Use the primary Cremona equation

    E: y^2 + xy = x^3 + x^2 - 34x - 135  (1913b1).

Exact computations from this equation give:

| Datum | Value |
| --- | --- |
| c4, c6, discriminant | 1657, 104275, -1913^2 |
| Conductor and minimal-model transformation | 1913, identity |
| Rational torsion order | 2 |
| Bad-place reduction | I2 at 1913, Tamagawa number 2 |
| Point counts at 3 and 5 | 2 and 4 |
| a3 and a5 | 2 and 2 |

The discriminant is a unit at three and five. Thus reduction at three
is good ordinary and non-anomalous. Three divides none of the torsion,
Tamagawa or residue-field orders. The complete non-CM isogeny calculation
gives two classes, with degree matrix `[[1,2],[2,1]]`; nonintegral j
checks the algorithm's non-CM scope.

`msinit(1913,2,1)` and exact Hecke matrices at 2, 3 and 5 isolate a
one-dimensional eigensymbol with eigenvalues 1, 2 and 2. Normalize by the
content of its **full path-generator values**, giving a primitive integral
plus symbol. Its absolute value on `[oo,0]` is nine. Its full generator
relations pass, its star sign is plus, and all 319 coefficients through
the weight-two Sturm bound agree with the curve. No numerical period
calibration enters this calculation. Nonvanishing, modularity and the
established Kolyvagin theorem give rank zero and finite whole Sha.

For the period scale, Table 1 of
[Miller, arXiv:1010.2431v3](https://arxiv.org/pdf/1010.2431v3),
printed page 17, identifies 1913b1 as optimal. This is an explicit
literature import; the isogeny-class size two alone would not prove
optimality. Its squarefree conductor allows the semistable Manin theorem
used in `finite_pairing_construction.md`.

All cusps are rational, and their images lie in the rational torsion
group of order two. Negative discriminant makes the real locus connected.
Its unique nonzero real two-torsion point has uniformizing representative
`Omega^+/2`. The real projection of the elliptic period lattice is also
`(Omega^+/2)*Z`. Therefore cusp-image translations add no new real
projection values. Every cusp-path integral has real projection in that
lattice, while optimality makes closed-cycle integrals generate the full
period lattice. Both containments give equality. The primitive plus
symbol is consequently twice the normalized plus symbol, up to sign,
and `|L(E,1)|/Omega^+=9/2`. With torsion order two, Tamagawa product two
and rank-zero regulator one, the analytic candidate has absolute value
`(9/2)*4/2=9`, of three-adic valuation two.

The proof of Miller's Theorem 7.2 reports a three-descent giving
`Sha[3]=(Z/3)^2` and explicitly lists 1913b1 among the cases in which
the Stein-Wuthrich algorithm supplies the desired arithmetic upper bound.
These intermediate computations give primary order nine. The subgroup
`Sha[3]` already has nine elements, so the entire three-primary group is
`(Z/3)^2`; no higher layer remains. We import those published computations,
not the final scalar BSD formula, and do not independently rerun them.

## Checking the Cartan hypothesis instead of supplying it

At five the Frobenius polynomial is `X^2-2X+5`. Modulo three it is
`X^2-2X+2`, which is irreducible. Its roots in `F_9` have norm two and
fourth power minus one, hence exact order eight. Thus the Frobenius
element generates the full nonsplit Cartan `F_9^*` in `GL_2(F_3)`.
The arithmetic Frobenius-polynomial theorem is a standard external import.

`frobeniusCartanReturn` checks every two-by-two matrix over `F_3` with
that trace and determinant. Each has eighth power identity, no earlier
positive power identity, and no invariant line. It does not assume a
selected Galois matrix or a Cartan certificate. The identity-matrix
control shows why trace two alone does not suffice.

Hence the ordinary hypotheses, both parts of Hypothesis 4.1, and the
torsion/local conditions of Remark 2.12 in
[Macias Castillo-Sano, arXiv:2603.23978v1](https://arxiv.org/html/2603.23978v1)
are satisfied. For the base field, set `T=T_3(E)`, `A=E[3-infinity]`,
`S={infinity,3,1913}`, and

    C = RGamma_tilde_F(Q,T)

with the ordinary filtration of Example 2.1 and unramified conditions
away from three. Remark 2.12 establishes Hypothesis 2.11 directly over
`Q`, so Lemmas 2.14-2.15 apply here without an auxiliary field or core
vertex. The non-anomalous condition identifies the ordinary local
image with the Kummer image at three, by Greenberg's Proposition 2.5.
Away from three the Bloch-Kato condition is the classical Kummer
condition, and the Tamagawa unit removes the integral unramified
defect. Under the Weil pairing these Kummer conditions are their own
local Tate-duality annihilators. Lemma 2.14 therefore gives the compact
classical Selmer group in degree one and the dual discrete classical
Selmer group in degree two; Lemma 2.15 excludes other degrees.
These are the same identifications summarized by Proposition 4.7(iii).
That proposition is stated in a tower setting, so we use the general
base-field lemmas rather than silently specializing its positive-layer
notation. The relevant degree convention is explicit:

    H1(C) = inverse-limit Sel_{3^m}(E/Q),
    H2(C) = Sel_{3-infinity}(E/Q)^dual,
    H_i(C) = 0 outside degrees one and two.

The Kummer exact sequences give `H1(C)=0`: the Mordell-Weil group is
finite of order two, and multiplication by three on the finite
three-primary Sha group makes its inverse Tate module zero. They give
`H2(C)=Sha[3-infinity]^dual=(Z/3)^2`. This is a derivation using the
proved arithmetic inputs and the cohomology theorem, rather than a
field asserting the intended cohomology.

## Return to an actual presentation and determinant ideal

Put `P=[Z_3^2 --3J--> Z_3^2]` in degrees one and two, where
`J=[[0,1],[-1,0]]`. Its first cohomology is zero and its second is
`(Z/3)^2`. A complex with just one nonzero cohomology group is
quasi-isomorphic to that group in its actual degree. Thus

    C ≃ H2(C)[-2] ≃ H2(P)[-2] ≃ P.

The middle isomorphism is a choice; this is an identification of derived
objects, not a chosen chain-level self-duality comparison. The integer
presentation and quotient are already implemented. Flat base change
from `Z` to `Z_3` gives this three-adic presentation. Lean proves the
integer kernel is zero, constructs a complete duplicate-free cokernel
enumeration of length nine, and computes determinant nine and integral
half-order three.

Finite elliptic-curve Sha has a perfect alternating Cassels-Tate pairing,
and distinct primary components are orthogonal. Its three-primary
restriction therefore gives a perfect form on `(Z/3)^2`. Lean derives
the coefficient of **every** such form, proves it is a unit, and
constructs an additive coordinate change recovering that form from the
inverse linking pairing of `3J` modulo integers. This identifies the
paired finite group; compatibility with the arithmetic self-duality map
and the raw Nekovar sign is still a separate comparison.

Under the canonical acyclic trivialization over `Q_3`, the inverse
determinant line has image `(9)` in `Q_3`. For `P`, this follows directly
by cancelling its differential, whose determinant is nine; transport
through a quasi-isomorphism respects the acyclic trivialization. It
also agrees with the zeroth Fitting ideal of `H2(C)=(Z/3)^2`. Thus the
square-root **ideal** is `(3)`, uniquely in this discrete valuation ring.
One can select a determinant basis with scalar image nine, and a basis
three of this normalized root ideal. An ideal and such a normalization
do not identify the paper's prescribed arithmetic Stark generator or
its image `h_p_CT`.

The paper's unshifted `H1(C)/div` would instead be zero here. Moving
the finite group into degree one requires `C[1]`; the shift also
inverts its determinant line. It cannot be silently applied to just the
cohomology label while leaving the determinant/Stark convention fixed.
No manuscript convention is changed by this supporting counterexample.

## A source-unit obstruction with the curve held fixed

Fix this same arithmetic complex, its acyclic trivialization, the root
ideal `(3)`, and its squaring map into `(9)`. The determinant bases with
scalar images nine and eighteen are both legitimate bases of `(9)`
over `Z_3`: two is a unit. Every cohomology group, Fitting ideal, pairing,
curve, period and local factor is unchanged.

The first basis has roots three and minus three. The second has no root
in `Q_3`: a root would have valuation one, and division by three would
give a unit whose square is two modulo three. The latter is impossible.
Equivalently, on the free `Z/27` residue line `L/27L`, whose scalar
image is `(9)/(243)`, the two bases have coefficients one and two, and
only the first coefficient is a square. Here `(9)/(27)` would instead
have order three and is not this free residue line.

Consequently no readout through the common Fitting ideal, or its
valuation two, decides whether a **prescribed** determinant basis lifts
through that fixed squaring map. This is a genuine arithmetic variation
of a basis on one fixed curve, not an unrealized change of Sha size or
an elliptic curve violating BSD. `unitErasedBasisLosesSquareClass`
proves the valuation and finite square-class obstruction in Lean;
`fixedSquareMapMissesABasis` works for every nonzero residue coefficient
of a fixed squaring map. `retainedUnitReturnsSquareClass` supplies the
finite repair. Lifting the square unit to `Z_3` uses Hensel's lemma,
since the derivative at either nonzero residue root is a unit.

The necessity is scoped to retaining unit information about a prescribed
basis. It does not prevent selecting *some* normalized liftable basis
using the acyclic trivialization, and it does not make a named source
necessary for the scalar BSD identity already supplied by normalized GZ.

## Remaining source comparison and checks

Theorem 3.4 in Macias Castillo-Sano additionally requires core vertices
among its rank-one auxiliary primes. The admissible sets in Section 4.2
have rank-two local quotients; Remark 4.6 is not by itself the required
rank-one construction. The subsequent argument in
`stark_core_vertex_construction.md` now supplies those core vertices
using a multiplicative inertia element, residual cohomology vanishing
and cartesian Kummer conditions, with published arithmetic existence
and freeness theorems. At level `Z/27` it returns actual Stark bases
with the same complete Fitting ladder and different square-root
behavior. A prescribed full Stark basis need not
have a root through a fixed square map, as the same-curve example proves.
The compatible root object, native basis selection, normalized map,
degree shift and combined orientation/sign still require construction.

`OddPrimaryBridge.lean` is finite algebra and exact equation computation.
The arithmetic cohomology and derived-category argument above remain
written mathematics using identified external theorems. The checker
reproduces the model/local and exact Hecke-symbol inputs, not those
theorems or the published upper bound. Source versions, locations,
digests and explicit trust boundaries are in
`odd_primary_selmer_bridge.json`.

Self-review separates ordinary applicability, arithmetic primary bounds,
base-field lemmas versus the tower notation of Proposition 4.7,
compact versus derived-mod-three cohomology, derived-object versus
self-duality comparison, ideal versus prescribed basis, and rank-two
admissible versus rank-one Stark auxiliary primes. The full named-source
endpoint remains open; no final comparison certificate was populated.
