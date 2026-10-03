# A compatible arithmetic Stark-system obstruction at all coefficient levels

This promotes the finite-level construction for 1913b1 at three to the
full three-adic Stark-system module. The two witnesses are coherent
arithmetic systems, not independently selected elements at each level.
Every component-image ideal at every level, and hence the entire
integral Fitting ladder, is identical on them. Their prescribed-square
rootability differs. Retaining one residue square-class bit repairs this
particular loss. The manuscript's native generator and orientation
comparison are still not constructed. Arithmetic self-duality on the
fixed compact lane is supplied by the subsequent
`ct_derived_transport_construction.md`, with the raw sign kept explicit.
The later `stark_coefficient_naturality.md` also supplies the canonical
integral determinant/Stark comparison by checking the actual finite maps.

The arithmetic freeness and base-change theorems are external imports
with applicability proved below. Lean constructs the completed
coefficient carrier and proves the unit/ideal obstruction uniformly on
it. The root-lifting classification and arithmetic application are
written proofs. No paper is edited and no final comparison field is
populated.

## Fixed inputs and permitted variation

Keep exactly the curve, prime, compact ordinary complex and canonical
acyclic trivialization of `stark_core_vertex_construction.md`. Thus

    R=Z_3, T=T_3(E), H1(C)=0, H2(C)=(Z/3)^2,
    L=det_R^(-1)(C), tr(L)=(9), tr(delta)=9.

The root ideal is `M=(3)` with distinguished basis `m=3`; its fixed
square identification sends `m tensor m` to `delta`. A root of a line
basis means an element whose tensor square is that basis under the
declared identification. It is not an arbitrary choice of a basis of
the square-root ideal. The reduced determinant line is `L/27L`, with
scalar image `(9)/(243)`. The quotient `(9)/(27)` is a different,
three-element module and must not be used as a free `Z/27` line.

The permitted variation is a unit multiplying a basis of the actual
Stark-system module. It changes no curve, local condition, pairing,
period, torsion convention, or auxiliary-prime family. The observable
retains all component-image ideals at all coefficient levels, with
their reduction maps, and their integral limits. It erases the unit
of the prescribed basis. The target is rootability of that prescribed
basis through a fixed normalized square comparison.

## Constructing one compatible arithmetic module

For each `n>=1`, take `A_n=E[3^n]`, `R_n=R/3^n` and the classical
Kummer structure `F_n`. The preceding construction establishes
Sakamoto's Hypothesis 3.12 for the integral representation as well as
for its reductions: residual irreducibility and zero invariants, the
same multiplicative-inertia element fixing the whole cyclotomic field,
and the central minus-identity cocycle argument. Here
`H_infinity(T)=Q(E[3^infinity],mu_{3^infinity})`. Its Galois group embeds
in the product of the full matrix image and the cyclotomic group, so
the previously constructed `(-I,1)` is central at this level too.
The cocycle calculation applies directly to this profinite group;
finite-level vanishing is not being passed through an unchecked limit.

The coefficient quotient `A_{n+1} -> A_n` induces the surjection

    E(Q_v)/3^(n+1) E(Q_v) -> E(Q_v)/3^n E(Q_v)

on Kummer images. In the map of Kummer sequences, the middle `E` map
is multiplication by three and the right `E` map is identity. This
shows that the propagated structure from `F_{n+1}` is exactly `F_n`,
as required before Sakamoto's Remark 5.1. Cartesian compatibility was
proved from the quotient injection in the preceding construction.
The core rank is zero for every `n` by Weil self-duality.

Use the full sets `Q_n=P_n(F_n)` of Definition 3.15, excluding the
fixed ramified and local-condition places as in that definition. They
are nested: the relevant fields over `Q` are
`Q(mu_{3^n},E[3^n])`, and conjugacy to the same inertia element at
level `n+1` implies conjugacy at level `n`. Each full set is infinite
by Chebotarev and contains a two-prime core vertex by the already
checked localization argument. We do not replace these full sets by
arbitrary infinite subsets, on which the localization conclusion need
not hold, nor by the finite two-prime witnesses.

[Sakamoto, Section 5 and Theorem 5.4](https://msp.org/ant/2018/12-10/ant-v12-n10-p02-s.pdf)
now gives the free rank-one module

    S = SS_0(T,{F_n},{Q_n}) = lim_n S_n,
    S_n = SS_0(A_n,F_n,Q_n),
    S/3^n S --pi_n--> S_n  (isomorphism).

The coefficient transition uses his Proposition 4.12 and the inverse
of restriction to the smaller prime set; it is not merely a sequence
of unrelated rank-one modules. In particular the maps `pi_n` are
surjective and compatible.

Under Cartier duality and the Weil pairing, the inclusions in the dual
Selmer direct limit are the natural inclusions of classical torsion
Selmer groups. The map of Kummer sequences for
`E[3^n] -> E[3^(n+1)]` has identity on the middle `E` and multiplication
by three on the right `E`; on the `H1(E)` term it is identity. Since
the Mordell-Weil group has order two, these Selmer groups identify
with `Sha[3^n]`, and their limit is the actual `Sha[3^infinity]=(Z/3)^2`.
This checks the group in Sakamoto's Definition 5.5, rather than
inferring its value from the cardinalities of finite groups alone.
His Theorem 5.6 therefore gives, for every basis `e` of `S`,

    I_0(e)=(9), I_1(e)=(3), I_i(e)=R for i>=2.

These are integral closed ideals. Their reductions give the finite
Fitting ladders, including the vanishing zeroth ideals at the first
two coefficient levels.

## Lifting the established finite comparison without claiming canonicity

At level three keep the actual canonical map already constructed by
[Macias Castillo-Sano, Theorem 3.4, version 1 (25 March 2026)](https://arxiv.org/html/2603.23978v1#S3.SS1):

    phi_3: L/27L --> S_3, e_3=phi_3(delta mod 27L).

Choose any basis `b` of `S`. The element `pi_3(b)` is a basis of `S_3`,
so `e_3=a_3 pi_3(b)` for a unique unit `a_3` of `Z/27`. Choose an
integer representative `a` of `a_3`. It is not divisible by three,
so it is a unit in `R`. The actual element `e=a b` is a basis of `S`
and has `pi_3(e)=e_3`. This constructs a coherent lift, using the
surjective coefficient theorem; arbitrary lifts that might be nonbases
are not invoked.

Define the `R`-linear isomorphism `Phi:L -> S` by `Phi(delta)=e`.
Its reduction at level three is `phi_3`, since both maps are linear
maps of rank-one modules agreeing on their basis. Its reductions at
other levels are compatible by construction through the `pi_n`.
This is a chosen lift, not a proof that it equals the canonical
Macias Castillo-Sano map at every other level. Such coefficient
naturality does not follow from this chosen lift. The later
`stark_coefficient_naturality.md` proves it from the actual cochain,
determinant and core-evaluation maps, yielding a canonical integral
comparison with the same square-image subset.

Fix this `Phi` once and define

    q_Phi: M -> S, q_Phi(v m)=v^2 e.

This is the square map followed by a linear comparison; `q_Phi` itself
is quadratic, not linear. The witness `e` has roots `m` and `-m`.
The witness `2e` has no root: a root would give `v^2=2` in `R`, whose
reduction modulo three is impossible. Both witnesses are actual
elements of the same arithmetic `S`, with every reduction compatible.

Every component map defining its image ideals is linear. Multiplying
the basis by two multiplies that image by two, which is a unit at
every coefficient level and in `R`. Thus the two images are the same
ideal, component by component. Their reduction maps and inverse-limit
ideals are consequently identical. This proves equality of the whole
declared observable, not only of the zeroth ideal or a finite prefix
of the Fitting ladder.

If a readout from that observable decided rootability for every basis,
it would have to give the same answer on `e` and `2e`, although one
is rootable and the other is not. No such readout exists. Conversely,
retaining the full Stark basis preserves the missing coefficient.
This is a source-information necessity for the prescribed-root task,
not indispensability of a named recognition source for scalar BSD.

## Exact repair and independence from the chosen lift

For any unit `u` of `R`,

    u has a square root in R <=> u mod 3 = 1.

Necessity follows from the two nonzero residues in `F_3`. Here is a
constructive proof of sufficiency. Write `u_n` for its compatible
representatives modulo `3^n`. Start with `r_1=1`. Given a representative
`r_n` with `r_n^2=u_n mod 3^n`, choose the unique digit `t_n` in
`{0,1,2}` satisfying

    2 r_n t_n = (u_(n+1)-r_n^2)/3^n mod 3,
    r_(n+1)=r_n+t_n 3^n.

The quotient in this formula is an integer, possibly negative, because
of coefficient compatibility. The coefficient `2r_n` is nonzero modulo
three. Expanding the square proves the new congruence: the term
`t_n^2 3^(2n)` vanishes modulo `3^(n+1)` for every `n>=1`. The new
representative is bounded by `3^(n+1)` and reduces to `r_n`. Hence these
digits construct a compatible element of `R` whose square is `u`.
Starting with `-1 mod 3` gives the other branch; uniqueness of each
digit proves exactly two roots. No convergence of unrelated witnesses
or unverified compactness assertion is needed.

It follows that rootability of a basis `u e` is returned exactly by
one residue bit: whether `u mod 3` equals one or two. The complete
Fitting data has erased this bit. Higher coefficient precision in
those ideals cannot recover it.

Moreover, if `Phi'` is any other linear lift of the same `phi_3`,
then `Phi'(delta)=w e` with `w=1 mod 27`. The criterion just proved
constructs a unit `s` with `s^2=w`. Thus

    {v^2 e : v in R} = {v^2 Phi'(delta) : v in R}.

The square-image subset of `S` is independent of the choice of lift.
Its rootability predicate can therefore be defined directly: pull a
basis back at level three through `phi_3` and retain its unit
coefficient modulo three relative to `delta`. This is a canonical
square-class readout relative to the fixed finite comparison, although
this chosen-lift argument does not construct a canonical integral map
or square-root element. The subsequent coefficient-naturality proof
supplies the integral map; a prescribed native square-root comparison
remains separate. The distinction removes dependence of
the no-go witness on the unproved higher-level map naturality.

## Lean coverage and distinct self-review

`lean/SixBirdsBSD/Closure/StarkInverseLimit.lean` defines `ThreeAdic` as
all compatible residues modulo `3^(n+1)`, with proved bounds and
compatibility for constants and multiplication. It is the standard
inverse-limit carrier for `Z_3`; no finite cut-off is part of its type.
It constructs a single inverse of two by the recursion

    b_0=2, b_(n+1)=b_n+3^(n+1), 2b_n=3^(n+1)+1.

The identity and compatibility are proved for every natural `n`.
Lean then proves equality of the principal ideals before/after unit
scaling, one has a root, two does not, and no readout from an arbitrary
entire family of such ideals can recover rootability. The last
theorem quantifies over the complete family index type. The arithmetic
instantiation, general root-lifting criterion and independence of the
chosen lift are written proofs, not separately mechanized theorems.

Self-review checked the integral Hypothesis 3.12, the direction of both
Kummer-sequence maps, nested full prime sets, cartesian propagation,
the actual dual direct-limit maps, the surjective rank-one base change,
the existence of a unit lift, reduction of the correct determinant
module, the quadratic nature of the square map, and every quantifier
in the ideal observable. The root-lifting digit uses an integer
difference, not truncated natural subtraction. The basis lift is
explicitly noncanonical, and its square-class independence has its
own proof rather than being inferred from ideal equality.

Remaining obligations for the original endpoint are unchanged in
substance: identify the manuscript's independently prescribed native
Stark generator and root object; carry the arithmetic self-duality
and raw Nekovar comparison established in
`ct_derived_transport_construction.md` into the manuscript's target;
resolve the degree shift and normalized
Pfaffian image; and establish named-source ablations on an allowed
arithmetic carrier. The normalized GZ predicate still entails scalar
BSD alone in the current interface. This completed-carrier obstruction
does not change that fact or claim a new proof of the full landing.
