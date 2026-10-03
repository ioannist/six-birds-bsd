# An arithmetic Pfaffian root line and its raw/corrected orientation

This constructs a root object for the actual rank-zero paired complex
of 1913b1 at three. Its square is the same inverse determinant line
already compared canonically with the integral Stark module. The
construction returns the rational scalar three and calculates the
orientation reversal when the raw Nekovar pairing is negated.
It does not identify that constructed scalar or root with the
manuscript's independently prescribed symbols. Those native objects
are still not independently specified by the import package.

## Fixed arithmetic input, rather than a supplied root certificate

Keep `R=Z_3`, `F=Q_3` and the actual ordinary compact complex `C`.
The arithmetic applicability, raw minus-Flach comparison and compatible
derived pairing are proved in `ct_derived_transport_construction.md`.
The canonical integral determinant/Stark map

    Phi_can:L=det_R^(-1)(C) --> S

is constructed in `stark_coefficient_naturality.md`. Neither map is
replaced by an arbitrary comparison field here. Their arithmetic
duality/cochain imports remain external to Lean, with the recorded
primary sources and applicability proofs unchanged.

Use the paired derived representative

    P=[V --A--> W], V=W=R^2, A=3J, J=[[0,1],[-1,0]],

in degrees one and two. The actual corrected perfect pairing has a
residue coefficient `u=1` or `u=2`; this coefficient was derived
from the arithmetic form before choosing its chain representative.
Its cup product is `u*v^t*w` in degrees `(1,2)` and its negative
in degrees `(2,1)`. Thus its first component identifies

    theta:W --> V^dual, theta=u I.

Both choices of `u` are units of `R`. The skew presentation in these
paired coordinates is

    theta A=3u J, Pf(theta A)=3u,
    det(theta)=u^2, det(theta A)=9u^2.

These are computed from the actual paired differential. The
coefficient three is not a supplied target-height label.

## Root line, square comparison and acyclic trivialization

Let `K=det_R(V)`.

Here `K` and `L` are ordinary rank-one modules, with the compact
complex's inverse-determinant convention fixed. An isomorphism of
integer-graded Knudsen–Mumford determinant objects, or a change to
the manuscript's cohomological degree, is not asserted by forgetting
their grading.

Since

    L=det_R(V) tensor det_R(W)^dual,

the dual of `det(theta):det(W)->det(V)^dual` induces a linear
isomorphism

    s_theta:K tensor K --> L.

Write `k=v_1 wedge v_2` and `l=k tensor (w_1 wedge w_2)^dual`
for the displayed frames. Then

    s_theta(k tensor k)=u^2 l.

The canonical acyclic trivialization `lambda_L:L_F->F` sends `l`
to `det(A)=9`. Define the root trivialization

    lambda_K:K_F --> F, lambda_K(k)=Pf(theta A)=3u.

The computed identity `(3u)^2=9u^2` gives the commutative square

    lambda_K(x) lambda_K(y) = lambda_L(s_theta(x tensor y)).

Thus this is a Pfaffian square-root determinant object, not a root
ideal assigned independently of the arithmetic duality. Its integral
image is `(3u)=(3)`, since `u` is a unit. Composition with `Phi_can`
gives the quadratic square map into the same actual Stark module.

Let `delta=l`, the unique determinant basis of scalar image nine.
The root is explicitly

    r=u^(-1) k in K,
    s_theta(r tensor r)=delta,
    lambda_K(r)=3.

In particular the canonical basis `e_can=Phi_can(delta)` is the
square of this constructed root under the integral comparison.
The other root is `-r`. The scalar-three normalization selects `r`
for this construction, without claiming to select the manuscript's
native root. A bare determinant square has not selected that sign.

## Basis covariance and descent on the declared paired carrier

The permitted carrier here consists of the actual paired rank-two
minimal presentations, their changes of free bases, and changes of
the unit lift representing the same derived pairing. A general
Pfaffian functor on all self-dual complexes is not claimed.

For changes of bases `B` on `V` and `D` on `W`, with respective
unit determinants `b,d`, the matrices become

    A'=D^(-1) A B,
    theta'=B^t theta D,
    theta' A'=B^t(theta A)B.

The rank-two Pfaffian identity, already proved as the congruence
law for the integral presentation, gives

    Pf(theta' A')=b Pf(theta A).

Also `k'=b k`, `l'=(b/d)l` and
`det(theta')=bd det(theta)`. Consequently

    det(theta') l' = b^2 det(theta) l,

which is exactly the transformation of `s_theta(k'^2)`.
Both `lambda_K` and `s_theta` therefore respect these changes of
frames. The frame's own numerical Pfaffian may change from three
to six, but its root is changed from `k` to `k/2` and the normalized
return is still three. Forgetting the frame transformation would
confuse a Pfaffian coefficient with an invariant scalar.

There is also a genuine homotopy issue. Replacing the lift `u` by
another unit `u'` with the same residue modulo three represents the
same derived map, by the explicit homotopy previously proved.
The root lines are compared by

    K_u --> K_(u'), k --> (u/u') k'.

This is integral, preserves the rational root trivializations and
commutes with their square maps into `L`. It maps their constructed
roots to one another. The ratios satisfy the composition law, so
these comparisons do not introduce an inconsistent choice at a
third lift.

More intrinsically, every presentation in this declared carrier has
the same image ideal `(3)` under its root trivialization. Identifying
each root line with that ideal gives a unique comparison preserving
the trivialization, and the preceding square identity makes it
compatible with the fixed `L`. Hence the root object descends on
this carrier, rather than merely having the right square in one
frame. This argument uses an actually computed Pfaffian and its
integral image; it does not define a comparison by asking it to
send an unnamed native element to an unnamed native target.

## Exact raw/corrected orientation calculation

Nekovar's raw arithmetic pairing is minus the corrected Flach
pullback. The chain representative therefore has `theta_raw=-u I`
and `theta_corrected=u I`. In rank two,

    det(theta_raw)=det(theta_corrected)=u^2,
    Pf(theta_raw A)=-3u,
    Pf(theta_corrected A)=3u.

The square-line isomorphism is the same, while the two root
trivializations are negatives. The linear comparison from the raw
root line to the corrected root line is `-id`: it preserves the
trivializations and its tensor square acts as identity on `L`.
The scalar-three roots are

    r_raw=-u^(-1)k, r_corrected=u^(-1)k,
    (-id)(r_raw)=r_corrected.

Both have square `delta`, and both return three in their respective
trivializations. Keeping the corrected root fixed while evaluating
the raw trivialization instead gives minus three. Thus the positive
return requires both the pairing correction and the matching source
orientation correction. The raw comparison theorem itself keeps
its minus sign. This computes the sign on these actual constructed
root lines; it does not populate `chiCTpContext.Sigma_NekCT`.

## Native scope, verification and distinct self-review

In the current paper corpus, `sqrt(F)_E^p`, `h_p^CT(E)` and
`vctp_p` are named in the CT theorem and import discussion but have
no independent formulas specifying them. The Lean context accepts
their carriers and partial selections as input. The import supplies
the image equality and positive sign separately. No equality between
those preselected native values and the root/scalar constructed
above follows merely from their names.

This result also identifies a limit on source necessity. The descended
root line is the embedded ideal `(3)` with square comparison into
the canonically trivialized determinant ideal `(9)`. Once that
determinant ideal and its rational trivialization are retained, the
root object and scalar-three basis can be reconstructed from them
without retaining the pairing coefficient. The pairing is used here
to establish compatibility of its actual Pfaffian construction with
that object; it is not proved indispensable for this scalar return.
For arbitrary prescribed Stark bases the square-class obstruction
still applies: the square map is `(u*a)^2 e_can`, so `2e_can`
has no root and shares every component ideal with `e_can`.

There is also the already recorded degree mismatch: for the compact
complex used here, `H1(C)=0` and finite Sha lies in torsion `H2(C)`.
Our root line belongs to that actual compact determinant convention.
Identifying it with the manuscript's `H1(C_p)/div` object requires
the specified shift and its determinant inversion. This construction
does not change the main theorem or edit the papers.

Lean's `CTPfaffianRoot` proves the skew-presentation matrices and
determinants, the root-trivialization square, the explicit inverse-unit
root return, negation invariance of the square and the raw/corrected
root signs. Its exact one/two coefficient controls distinguish the
frame Pfaffian six from the normalized return three. These are integer
and rational coordinate statements; the three-adic arithmetic
application and line descent are written proofs using the earlier
arithmetic comparisons. They are not a mechanized native CT height.

Distinct self-review checked the direction of `det(theta)` and its
dual, the factor `u^2` in the square map, basis changes in both degrees,
the ordinary-line versus graded-determinant scope,
the integral unit division, the lift-change composition law and
trivialization-preserving descent, and the separate raw/corrected
root orientations. In particular `K` is not given the square map
`k^2 -> l` when `u=2`: that would miss the factor four. The scalar
return three is computed after this factor is repaired.

The remaining task is to identify the manuscript's independent native
root and target, including degree and orientation conventions, or to
provide an explicit new interface for discussion. The named-source
scalar indispensability endpoint still fails under the current
normalized GZ entailment and has not been claimed here.

Fresh checkpoint verification passed `make verify-lean` (90 build
jobs) and `make validate test public-audit` (26 tests). All six new
regression results use only the standard Lean axioms `propext`,
`Classical.choice` and `Quot.sound`. The 51 manifest entries,
five declared trust-base axioms and 69 statement-audit statuses
are unchanged. The papers were checked to be unchanged.
