# Common-cover Frobenius loss and the additive eta bridge

This construction supplies an arithmetic split pair on a declared local
observation interface. It also identifies a concrete eigenpacket obstruction
for the eta comparison. Neither result proves indispensability of the full
named BSD sources. The manuscripts and their claims are unchanged.

## Original objects and one common cover

Use the pinned Cremona equations and the independently reproduced local
Tate calculations from `local_unit_support_models.json`:

| Curve | Equation coefficients | c4 | c6 | Delta | Type at 11 | c11 |
| --- | --- | ---: | ---: | ---: | --- | ---: |
| 121a1 | [1,1,1,-30,-76] | 1441 | 54703 | -121 | II | 1 |
| 121b1 | [0,-1,1,-7,10] | 352 | -6776 | -1331 | III | 2 |

The component numbers are arithmetic outputs of the external Tate algorithm,
not consequences of the finite-field point count. The existing Lean module
checks the numerical shallow-branch inputs; PARI reproduces the arithmetic
outputs. At eleven all denominators used below are units.

Completing the square and removing the quadratic term converts a long
Weierstrass equation to `y_s^2=x_s^3+A*x_s+B`, with

    x_s=x_old+b2/12, y_s=y_old+(a1*x_old+a3)/2,
    A=-c4/48, B=-c6/864.

Let `L=Q_11(pi)`, where `pi^12=11`. The polynomial is Eisenstein, so
`[L:Q_11]=12`, the extension is totally ramified, and its residue field
is F_11. Since eleven does not divide twelve, this is a tame extension.
Fix this SAME extension for both curves; no extension degree is changed
between the two observations.

Scale `x_s=u^2 X, y_s=u^3 Y`, using `u=pi^2` for 121a1 and `u=pi^3`
for 121b1. The resulting equations over the valuation ring of L have

| Curve | A'=A/u^4 | B'=B/u^6 | Delta'=Delta/u^12 | Good fiber |
| --- | --- | --- | --- | --- |
| 121a1 | -131*pi^4/48 | -4973/864 | -1 | Y^2=X^3+9 |
| 121b1 | -2/3 | 7*pi^6/108 | -1 | Y^2=X^3+3X |

The displayed coefficients are integral and the discriminants are units.
Thus these models actually give good reduction over L. The reductions use
`-4973/864=9` and `-2/3=3` in F_11. Both reduced discriminants are ten.
Smaller tame covers of degrees six and four respectively also suffice,
but they are not the comparison carrier here.

The Lean quotient-coordinate calculation checks all four scale equations
and both transformed discriminants in Q[pi]/(pi^12-11). It does not construct
Q_11 or prove the Eisenstein and good-reduction theorems. Those are the
standard arithmetic inputs used in this written construction.

## Equal Frobenius data, unequal base component numbers

Exhaustive affine enumeration plus the point at infinity gives twelve
F_11-points on each fiber. An independent quadratic-discriminant count and
PARI's finite-field elliptic routines give the same result. The elliptic
Frobenius polynomial is therefore

    P(T)=T^2-(11+1-12)T+11=T^2+11

for both curves. The point-count/characteristic-polynomial theorem is an
external arithmetic result; see
[Kedlaya's finite-field Frobenius account, slide 2](https://kskedlaya.org/slides/agct2025.pdf).
In particular this constructs an actual good-fiber eigenvalue beta satisfying
`beta^2=-11` and, with `v_11(11)=1`, `v_11(beta)=1/2`.

There is a stronger equality than matching two polynomial coefficients.
Take the unfiltered rational good-fiber Frobenius module `(D,F)` over Q_11:
equivalently, the two-dimensional negative-involution part of rational
Monsky-Washnitzer cohomology used for these genus-one equations. Its
dimension and Frobenius characteristic polynomial are supplied by the
standard cohomology comparison described in
[Kedlaya, Sections 3-4](https://arxiv.org/pdf/math/0105031v2).
This is the genus-one part, not the entire cohomology of the punctured curve.
Because the residue field is F_11, Witt Frobenius on Q_11 is the identity
and F is Q_11-linear. The reciprocal convention `11*F^-1` has the same
characteristic polynomial in dimension two and does not change the argument.

The polynomial `T^2+11` is irreducible over Q_11: a putative root c would
have `2*v_11(c)=1`, whereas the valuation of a nonzero Q_11 element is an
integer. Cayley-Hamilton gives `F^2=-11`. For any nonzero v, the vectors
v and Fv are independent, since a dependence would supply such a root.
They therefore form a basis, in which F has the matrix

    [[0,-11],[1,0]].

Both actual modules are consequently isomorphic as unfiltered rational
Frobenius modules. This last statement is a written linear-algebra proof
with arithmetic cohomology inputs, not a Lean crystalline-cohomology proof.

Define the legal observation to be the isomorphism class of this module,
with the fixed cover L and prime eleven retained. It forgets the original
equation, the marked inertia/descent action, Hodge filtration, integral
lattices and other global data. Any function on this observation has the
same value on the two curves. Their base component numbers are 1 and 2.
Thus no such function can return c11 uniformly even on this two-curve
domain. The polynomial-only version is proved in Lean by
`noComponentReadoutFromCoverFrobenius`; the stronger module-class version
follows from the cyclic-basis proof above.

This is a genuine local arithmetic information-loss result. It is not a
claim that the full cover/descent source forgets c11. Retaining the original
equation permits the Tate algorithm to recover c11, and the observation
explicitly discarded that information. It does not freeze global ranks:
the pinned data lists rank zero for 121a1 and rank one for 121b1. Normalized
GZ, analytic period data and the other named sources are not matched by this
pair. Consequently it cannot establish their ablation or scalar BSD necessity.

## Constructed descent repair

Adjoin the twelfth roots of unity to the common cover. They lie in an
unramified quadratic extension of Q_11, because twelve divides `11^2-1`.
Hensel lifting preserves their distinct residues. Over that unramified
field, `T^12-11` remains Eisenstein and its splitting extension is obtained
by adjoining pi; its cyclic inertia group has order twelve.
Fix a primitive root zeta and a tame inertia generator tau with
`tau(pi)=zeta*pi`. Inertia fixes the residue field, including the reduction
of zeta, which still has order twelve. On the reduced coordinate functions
the actual descent action is

    tau(X)=zeta^(-2s)*X, tau(Y)=zeta^(-3s)*Y,

where s is the scale exponent already derived from the original equation.
For 121a1, s=2 gives weights (8,6) modulo twelve: the X character has
order three and the Y character has order two. The action preserves
`Y^2=X^3+9` and has exact order six. For 121b1, s=3 gives weights (6,3):
X maps to -X, Y maps to zeta^3*Y, and both sides of `Y^2=X^3+3X`
change by minus one. This automorphism has exact order four. The orders
are exact as function-field automorphisms: identity on X and Y requires
both character powers to be one. Lean checks all smaller powers of each
pair of characters, not only their sixth/fourth powers.

This is native descent data constructed without a component-number
input. Its action orders distinguish the actual curves, so retaining
the descent action repairs the two-curve no-go. On this restricted II/III
carrier, the order e gives the computed discriminant valuation `12/e`,
namely two or three; the applicable shallow Tate branch then returns
one or two. This return is restricted to the stated carrier, not a
rule for arbitrary additive curves.

With the coordinate characters marked by the fixed zeta, a more direct
return is also available: the X weight minus the Y weight equals s
modulo twelve. Since `Delta'=-1`, the original discriminant valuation is
`12*v_11(u)=s`; here it lies strictly between zero and twelve, so the
residue recovers the exact valuation. `markedCharacterRepairsScale`
checks the character identity for every s modulo twelve. The marking
and the small-valuation domain are explicit parts of this repair.

The descent action above is on the geometric good fiber after the
unramified extension. It is not an extra commuting Q_11-linear
operator silently added to the previous rational Frobenius module;
the residue Frobenius and inertia satisfy their usual conjugation
relation. The erased action, rather than a new Frobenius eigenvalue,
accounts for this repair.

## Original U11 versus cover Frobenius

The same exact PARI run constructs the plus modular-symbol space of weight
two and level 121. The Hecke matrices at 2, 3 and 5 isolate, for each curve,
a one-dimensional simultaneous eigenline with the curve's coefficients.
The full U11 matrix kills that line. Its normalized q-expansion agrees with
the curve through all 22 coefficients of the weight-two level-121 Sturm
bound (`[SL2(Z):Gamma0(121)]=132`). Modularity supplies the arithmetic
identification with the curve's classical newform. No eta output or
precomputed beta is used in this calculation. The
[PARI modular-symbol documentation](https://pari.math.u-bordeaux.fr/dochtml/html/Modular_symbols.html#mshecke)
identifies its operator at a prime dividing the level with U_p.

Hence the original classical line has U11=0, while the good-fiber beta
is nonzero. This is not just a critical-slope nomenclature conflict.
If specialization rho intertwines U and sends a generalized beta
eigensymbol phi to this classical line, then

    (U-beta)^n phi=0  ==>  (-beta)^n rho(phi)=0  ==>  rho(phi)=0.

The last implication uses invertibility of nonzero beta in the coefficient
field. The first-order specialization condition in the cited moment lemma
also forces zero specialization on this particular U11=0 line. Lean proves
the transport through arbitrary iterates and the zero-kernel return under
explicit equivariance and zero-preservation assumptions. It does not model
the overconvergent specialization theorem. A beta-zero false control shows
why the kernel hypothesis matters.

This excludes a nonzero equivariant specialization to the original curve's
classical line. It allows symbols with zero specialization, and does not
exclude a changed modular representation, twist or non-equivariant descent
with an independently established comparison. A Frobenius eigenvalue from
good reduction on the cover is not by itself a U11 eigenvalue of that
original classical line.

## Self-review and remaining return

The carrier was fixed before the readout: two pinned curves, one specified
cover, and unfiltered rational Frobenius isomorphism class. The component
target comes from independently computed base Tate data. No certificate
field supplies the no-go or the eta formula. Exact quotient identities,
unit discriminants, dual-method point counts and a nonsingular different-
trace control test the construction. Claims about the entire punctured-curve
cohomology or integral structures have not been inferred from a characteristic
polynomial.

The successful output is a common-cover arithmetic split pair, an explicit
tame-descent repair on that carrier, and a sharper specialization obstruction.
The uniform eta return still needs an additive modular object whose relation to the cover beta
and original eigenpacket is proved. The actual moment, leading coefficient,
order, torsion and eta normalization remain to be constructed. The direct
Lang-Wake scope obstruction and the original normalized-GZ scalar redundancy
remain in force. This checkpoint does not populate the eta or CT imports,
change their source burden, or claim a full source-indispensability theorem.

## Reproduction

The fixture `additive_frobenius_descent.json` preserves the cover coefficients,
fibers, operator outputs and primary sources. Run:

    python3 scripts/check_additive_frobenius_descent.py --check
    python3 scripts/check_additive_frobenius_descent.py --gp /path/to/gp
    make verify-lean
    make validate test public-audit

The offline checker reproduces rational-polynomial and finite-field evidence;
its message distinguishes stored modular-symbol outputs from a fresh GP run.
The Lean axiom regression covers the new computational and general transport
theorems. Neither gate certifies the external p-adic cohomology bridge or
the missing eta comparison.

Fresh checkpoint verification on 2026-10-03 passed: both make gates above,
the public hygiene check, all 26 repository tests, and the optional GP run
with PARI 2.15.4. Lean built 91 jobs and checked all 51 manifest declarations;
the five-axiom declared trust base is unchanged. The eleven new regression
closures use only the standard `propext`, `Classical.choice` and `Quot.sound`
axioms where needed. Existing audit assessments and claim statuses were
preserved; refreshed context hashes do not promote an open arithmetic claim.
