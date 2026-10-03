# Intrinsic tame component return and an isogeny boundary

This construction derives a native local factor from tame geometric inertia
and proves its equality with the rational Tamagawa number on a declared
arithmetic domain. It replaces the previous two-curve coordinate lookup with
an invariant return. A separate explicit isogeny pair shows why the domain
restriction is necessary. Neither result proves the full named-source BSD
indispensability endpoint or fills the OC/eta comparison records. Papers
and their main claims are unchanged.

## Native factor and arithmetic domain

Let E be an elliptic curve over a finite extension K0 of Q_p, with p at least
five. Assume purely additive reduction, tame potential good reduction and
finite geometric inertia order e in {4,6}. Fix an auxiliary prime ell
different from p. The origin identifies E with its own Jacobian. For a tame
inertia generator tau, let

    b_native = det(1-tau | V_ell(E)).

This factor is defined from the Galois representation, before considering
the component group. No Tamagawa number occurs in its definition. Finite
inertia is semisimple in characteristic zero. The Weil pairing gives
det(tau)=1, since all prime-to-p roots of unity are unramified. The action of
an origin-preserving elliptic automorphism on the rational Tate module is
faithful: a nonzero difference of endomorphisms is an isogeny and cannot
annihilate all ell-power torsion. Therefore its order equals the previously
constructed geometric automorphism order.

The two eigenvalues are inverse roots of unity. Exact order six forces
the polynomial T^2-T+1; exact order four forces T^2+1. Consequently

| e | Trace of tau | det(tau) | b_native |
| --- | ---: | ---: | ---: |
| 6 | 1 | 1 | 1 |
| 4 | 0 | 1 | 2 |

For any two-dimensional matrix A, det(1-A)=1-tr(A)+det(A). This expression
is invariant under change of basis and independent of the choice of tame
generator: either primitive generator has the same inverse pair of
eigenvalues. The value is an exact positive integer, not only an ell-adic
valuation or a class modulo units. Lean proves the matrix identity and exact
change-of-basis invariance, then derives both returns from determinant one
and the appropriate trace.

For the fixed 121a1/121b1 models, `additive_frobenius_descent.md` already
constructs the geometric inertia orders six/four from one common tame
good-reduction cover. Thus the hypotheses above are realized independently
of the component targets. The same argument applies to any elliptic curve
with the stated tame, purely additive and inertia-order hypotheses. In
particular it is not tied to the particular degree-twelve cover, coordinate
marking or small-discriminant representative of the previous repair.

## Geometric component group and exact rational return

Pass to the completion of the maximal unramified extension of K0. Its
residue field is algebraically closed, and its Neron component group is the
geometric component group Phi of the original model. Purely additive
reduction and the finite tame good-reduction extension survive this base
change. An elliptic curve with its rational origin has index one and hence
delta(E)=1 in the notation of
[Nicaise, Corollary 3.3(2), printed page 7](https://arxiv.org/pdf/0901.1809v2).
That result gives

    #Phi = P_tau(1) = b_native.

Here P_tau is the characteristic polynomial of TAME INERTIA, not that of
the good-fiber residue Frobenius. Dualizing the Tate module in H1 replaces
the eigenvalues by their inverses and leaves this polynomial unchanged.
The checked corollary includes the tame equality of the full and
prime-to-p component orders. Its Jacobian proof uses the sncd-model formula
and Saito's tame criterion. We use this proof rather than leaving the
erroneous older dependency discussed after Theorem 2.8 unaddressed.

Over the original finite residue field k0, the rational Tamagawa number is
`c(E/K0)=#Phi(k0)`, the number of Frobenius-fixed geometric components. For
orders one and two, every group automorphism is the identity. It follows
that

    c(E/K0) = #Phi = det(1-tau) = 1 or 2.

This is the intrinsic arithmetic comparison on the declared domain. The
Frobenius step is proved, not omitted. Lean checks that an injective
zero-preserving map on the two-element group fixes every element; Neron
models, Galois representations and Nicaise's theorem remain written
arithmetic imports. At p=3 the present hypotheses and their applicability
must be checked separately; this result does not silently cover wild
odd-prime cases.

The result constructs a candidate native local normalization b_native.
It does not identify this determinant with the manuscript's independently
prescribed `descent_p_OC` map or its `tamFactor`. A comparison of those
actual objects is still needed. It also does not establish the Sha
hypotheses of the full recognition record or a global product comparison.

## Integral coinvariant realization

There is an independent explanation of the exact orders through actual
integral cohomology. For ell different from p, the primary
[Edixhoven account, equations (2.2)-(2.4), printed page 31](https://www.numdam.org/item/CM_1995__97_1-2_29_0.pdf)
identifies the ell-primary geometric component group with the torsion of
inertia cohomology, equivalently torsion coinvariants with a Tate twist
(-1). In the tame finite-action lane these coinvariants are
`T_ell/(1-tau)T_ell`. The twist is immaterial to geometric cardinality;
its Frobenius effect is also trivial on the order-two group. It must not
be discarded for general component groups.

Use ell=2. For inertia order six, Q_2[tau] is the unramified quadratic
field: T^2-T+1 is irreducible modulo two and generates its valuation ring.
For order four, Q_2[tau]=Q_2(i), whose valuation ring is Z_2[i]; i-1 has
Eisenstein polynomial T^2+2T+2. In each case the tau-stable rank-two Tate
lattice is a torsion-free rank-one module over that discrete valuation
ring, so is free. Choosing its basis and (1,tau) gives the actual companion
matrices

    tau6=[[0,-1],[1,1]], tau4=[[0,-1],[1,0]].

This establishes arithmetic realizability of the integral presentations;
they are not assigned metadata. With integer coordinates their differences
from the identity are

    1-tau6=[[1,1],[-1,0]], 1-tau4=[[1,1],[-1,1]].

The first map is onto: (a,b)=(-y,x+y) maps to (x,y). The image of the
second consists exactly of pairs with even coordinate sum. Reduction of
that sum modulo two is a surjective additive map with this kernel. Lean
constructs the quotient by the computed image, proves its two-sided
equivalence with Z/2 and checks additivity. Completing at two preserves
these finite cokernels (or applying the same parity calculation over Z_2
does so directly). Finite coefficient checks are controls, not a substitute
for this integral/completed argument.

Thus retaining the native integral descent object returns the full local
component factor on this scope. Passing its scalar to a class modulo
Z_11 units again identifies one and two; the old unit-class no-go remains
valid. Loss by that coarsening does not imply loss by the complete source.

## A realized boundary: equal integral T11, unequal c11

Consider the explicit non-CM rational curves

    E: y^2+11xy+11y=x^3,
    E': y^2+11xy+11y=x^3-605x-15488.

For the source, (0,0) and (0,-11) are the nonzero rational three-torsion
points. Set

    f=x^3+121x+121,
    g=y*x^3-1331x^2-121xy-2662x-242y-1331,
    X=f/x^2, Y=g/x^3.

The exact polynomial identity clearing the denominator x^6 is

    g^2+11fgx+11gx^3-f^3+605fx^4+15488x^6
      =(x^3-121x-242)^2*(y^2+11xy+11y-x^3).

Lean proves this identity for arbitrary integer x,y, without assuming
the target curve equation. It therefore verifies the actual map on the
source equation. The rational map extends between the smooth projective
curves and sends the origin to the origin. The rational function f/x^2
has degree three, so the resulting origin-preserving morphism is a
separable degree-three isogeny phi. Its kernel is the origin and the
two displayed three-torsion points. Independently, PARI `ellisogeny(E,x)`
returns precisely E' and these same map polynomials.

At eleven, the exact local Tate outputs are:

| Curve | c4 | c6 | Delta | Type | c11 |
| --- | ---: | ---: | ---: | --- | ---: |
| E | 11737 | -1270621 | 1376254 | IV | 3 |
| E' | 40777 | 6840251 | 12160580344 | IV | 1 |

Both discriminants have valuation four at eleven, so these integral
models are minimal there. Neither j=c4^3/Delta is an integer, proving
that both curves are non-CM independently of a database label.

They acquire good reduction on the SAME tame cover pi^3=11. First use
the standard short equation with A=-c4/48, B=-c6/864, and then scale by
u=pi. Both c4 and c6 are divisible by 11^2, giving the integral cover
coefficients

    A'=-(c4/11^2)*pi^2/48, B'=-(c6/11^2)/864,
    Delta'=Delta/11^4.

The transformed discriminants are the units 94 and 830584. The good
fibers are Y^2=X^3+3 and Y^2=X^3+7; both have twelve F_11-points.
Their native inertia orders are both three and the polynomial is T^2+T+1.
Nicaise's return gives geometric component order three for each, whereas
the rational fixed-point orders are three and one. The split/non-split
type-IV residue test and PARI reproduce this difference. In particular,
replacing the rational component count by P_tau(1) outside the checked
one-or-two domain would give the wrong answer for E'.

More strongly, phi induces an isomorphism of the FULL integral eleven-adic
Galois Tate modules. Its inverse is (1/3) times the dual isogeny, because
the two compositions are multiplication by three and three is a unit in
Z_11. At every coefficient level the inverse of three is compatible with
reduction; this is one isogeny-induced integral isomorphism and not an
unverified collection of finite matches. Globally, phi also identifies
every rational Tate module, including the rational three-adic module.

The Weil pairing can also be retained. The isogeny map is a similitude
of multiplier three. There is an actual unit alpha in Z_11 with alpha^2=3:
start with r_1=5 modulo eleven and, given r_n^2=3 modulo 11^n, set

    c_n=(r_n^2-3)/11^n,
    t_n=-c_n*(2r_n)^(-1) modulo eleven, chosen in 0..10,
    r_(n+1)=r_n+11^n*t_n.

The derivative 2r_n is always ten modulo eleven and is invertible.
Expanding the square proves the next congruence; the quadratic correction
term vanishes modulo 11^(n+1) for every n at least one. The chosen range
preserves normalized representatives and coefficient compatibility. This
constructs the full inverse-limit root alpha, beginning 5,27,753, and
alpha is a unit. Thus alpha^-1 times the isogeny Tate map preserves the
Weil pairing and still commutes with full Galois action. This is a written
all-level construction, not an inference from finitely many roots. Lean
checks the simple-root inputs and initial controls; the checker tests
additional compatible levels. The nonsquare unit two is a false control,
so this normalization is not asserted for every isogeny degree.

Consequently no function of the isomorphism class of T11 as a Galois
representation can recover c11 on a domain containing this pair. The
same applies to the complete family of rational Tate-module classes,
without specifying polarizations across that family.
Unlike the previous unfiltered-Frobenius split pair, this observation may
retain full Galois action, the integral structure at eleven and the Weil
pairing. The chosen unit is part of the constructed isomorphism, not a
new coefficient field supplying the desired component number. The
isogeny has degree three, so its inverse need not preserve the integral
three-adic lattice, where the component difference can survive.

This no-go is a written arithmetic theorem using explicit isogeny
functoriality and exact local computations. Lean verifies the map identity,
equations, discriminant valuations, good-fiber counts and rejection by
the shallow II/III branch; it does not mechanize Tate modules or the
Neron component computation. The observed representation is its
isomorphism class, not a record retaining the curve equation or identity.

The curves are globally isogenous, so their L-functions and ranks agree.
Other integral and normalized BSD data are not frozen, and their changes
can compensate. This is not a BSD counterexample. Both curves are type
IV and lie outside the manuscript's II/III p-adic descent scope, so this
does not contradict the intrinsic return above or prove indispensability
of the full named recognition sources.

## Self-review, unresolved comparison and reproduction

The positive return uses three separate bridges: constructed inertia type,
the geometric component theorem at its tame purely additive hypotheses,
and Frobenius-fixed components. The type-IV pair falsifies omission of the
third bridge. The integral Tate-module control requires degree prime to
eleven; it does not assert an integral three-adic equivalence. Geometric
inertia on ell-adic cohomology, ell unequal to p, is not the generally
infinite p-adic Galois inertia action. An OC p-adic comparison still needs
the specified potentially crystalline/descent construction and its actual
map normalization. Neither b_native nor the isogeny fills that gap.

The remaining exact return is to identify the independent OC local
determinant with the intrinsic determinant just constructed and to match
the signed persistence and global-factor conventions. Eta's modular
eigenpacket, leading term and torsion normalization remain open. The
normalized GZ predicate's existing scalar entailment is unchanged, so
these local results cannot establish the originally proposed three-source
necessity for that interface.

The JSON fixture records the primary PDF digests, precise theorem scope,
companion matrices and exact isogeny outputs. Reproduce with:

    python3 scripts/check_tame_component_return.py --check
    python3 scripts/check_tame_component_return.py --gp /path/to/gp
    make verify-lean
    make validate test public-audit

The checker distinguishes offline integral/symbolic/finite evidence from
fresh arithmetic GP computations. Repository tests do not establish the
external geometric component theorem or the missing named-source maps.

Fresh checkpoint checks on 2026-10-03 passed: the GP reproduction with
PARI 2.15.4, both make gates, public hygiene and all 26 repository tests.
Lean built 92 jobs, checked all 51 manifest declarations and printed the
eighteen new regression axiom closures. Only standard `propext`,
`Classical.choice` and `Quot.sound` occur where needed; the declared
five-axiom trust base is unchanged. Existing statement assessments and
claim statuses were preserved, and no paper was edited.
