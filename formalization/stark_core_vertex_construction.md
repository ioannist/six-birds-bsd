# Arithmetic core vertices and a Stark-basis unit obstruction

This continues the 1913b1 construction in `odd_primary_selmer_bridge.md`.
It supplies the missing rank-one core-vertex applicability argument for
the determinant-to-Stark-system theorem. The arithmetic existence result
is written mathematics using published theorems; Lean proves its finite
algebra and a uniform cocycle calculation. No manuscript or final
`chi_CT` comparison certificate is changed.

## Fixed arithmetic inputs and target

Fix the curve 1913b1, `T=T_3(E)`, the ordinary compact complex `C` over
`Z_3`, and its canonical acyclic trivialization. The previous construction
gives `H1(C)=0`, `H2(C)=(Z/3)^2`, and inverse determinant line `L` with
scalar image `(9)`. Its underlying arithmetic imports remain explicit:
Miller's intermediate descent/upper bound and the general compact-Selmer
cohomology theorem were not mechanized or rerun here.

For every positive integer `n`, put `R_n=Z/3^n`, `A_n=E[3^n]`, and let
`F_n` be the classical Kummer Selmer structure. Good ordinary,
non-anomalous reduction at three and the Tamagawa unit identify it with
the structure attached to the ordinary filtration. These are the local
conditions required by Macias Castillo-Sano, Definition 2.5, not a new
relaxed global structure. The relevant field is `Q` throughout.

The target is to construct a set of auxiliary primes with free rank-one
local quotients containing a core vertex, with core rank zero. This is
the extra input to their Theorem 3.4, beyond Hypothesis 2.11 already
checked in the previous construction.

## The rank-one element comes from multiplicative inertia

In [Sakamoto, Algebra & Number Theory 12 (2018)](https://msp.org/ant/2018/12-10/ant-v12-n10-p02-s.pdf),
Hypothesis 3.12(H.2) requires an element `tau` fixing `H_infinity` with
`A_n/(tau-1)A_n` free of rank one over `R_n`. For `Q`, the Hilbert class
field is trivial and the units are `{1,-1}`, so his `H_infinity` is
exactly `Q(mu_{3-infinity})`. Complex conjugation does not meet this
fixing condition: it acts nontrivially on these roots of unity.

Use inertia at 1913 instead. The checked minimal equation has
`v_1913(Delta)=2` and `v_1913(c4)=0`, so reduction is multiplicative
of type `I_2`. After at most an unramified quadratic extension it is a
Tate curve with parameter `q` of valuation two. The uniformization and
discriminant formula are reviewed in
[Conrad's modular-curve notes, Section 19, printed pages 43-44](https://virtualmath1.stanford.edu/~conrad/248BPage/handouts/modularcurves.pdf).
We use Tate uniformization as an external theorem and derive the needed
inertia action from it.

Write `q=pi^2 u`. All compatible three-power roots of the unit `u` and
all three-power roots of unity lie in the maximal unramified extension,
since the residue characteristic is 1913. On the Tate torsion basis
`(zeta_{3^m},q^{1/3^m})`, choose a compatible tame inertia generator
sending `pi^{1/3^m}` to `zeta_{3^m} pi^{1/3^m}`. Its action on `T` is

    tau = [[1,2],[0,1]].

The unramified quadratic twist has trivial restriction to inertia,
so the same conclusion holds without assuming split reduction over
`Q_1913`. Inertia at 1913 fixes `mu_{3-infinity}`. Since two is a
three-adic unit, `(tau-1)T` is the full first coordinate line, and the
quotient is the second coordinate `Z_3`. Reduction gives exactly the
required free rank-one quotient for every `R_n`. `inertiaInputs`,
`transvectionRankOneThree`, and `transvectionReturn27` verify the
equation-derived valuations and finite linear-algebra returns in Lean.
They do not construct the local Galois representation in Lean.

## Residual irreducibility and cohomology vanishing

The Frobenius at five from the previous construction generates a nonsplit
Cartan on `E[3]`. It has no invariant line or nonzero fixed vector;
the Weil pairing identifies the residual Cartier dual with `E[3]`.
Thus Sakamoto's Hypothesis 3.12(H.1) holds.

For (H.3), consider the full closed image of `G_Q` in `GL_2(Z_3)` and
choose a Frobenius matrix `g` at five. Its fourth power is minus identity
modulo three; `frobeniusFourthPowerIsNegative` checks this for every
matrix with the equation-derived trace and determinant. Put `u=-g^4`.
Then `u=I+3B`, and

    u^(3^k) = I mod 3^(k+1),
    g^(4*3^k) = -u^(3^k) --> -I.

The congruence follows by induction: cubing `I+3^s B` with `s>=1`
increases the congruence depth by at least one. Consequently closedness
of the actual Galois image gives the element `-I`, not just residual
minus identity. Its cyclotomic character is its determinant, namely one,
by the Weil pairing. For `H_infinity(A_n)=Q(mu_{3-infinity},E[3^n])`,
the corresponding element in the Galois group embeds as `(-I,1)` in
`GL_2(R_n) x Z_3^*`. It is central and acts as minus identity on both
residual modules.

Here the cohomology vanishing has a direct cocycle proof. If `z` is this
central element and `c` is a continuous cocycle with values in `E[3]`,
compare `c(gz)=c(zg)`. The result is

    2 c(g) = c(z) - g c(z),
    c(g) = g c(z) - c(z),

since minus two equals one in `F_3`. Thus every cocycle is the explicit
coboundary of `c(z)`, and both groups in (H.3) vanish. The proof works
for the entire profinite group; it is not inferred from a finite sample
of Galois levels. `centralNegativeCocycleIsCoboundary` proves the
identity uniformly over an arbitrary group carrier in Lean. It uses
centrality, the minus action, and the cocycle equation, and supplies the
actual coboundary; it does not assume cohomology vanishing.

## Cartesian local conditions and two auxiliary primes

The remaining local compatibility is Sakamoto's Definition 3.8. For any
local field `Q_v`, the Kummer sequence identifies the local quotient for
`A_n` with `H1(Q_v,E)[3^n]`. The socle inclusion `A_1 -> A_n` induces
the natural injection

    H1(Q_v,E)[3] -> H1(Q_v,E)[3^n].

Indeed, the map of Kummer sequences uses identity on their middle `E`
and multiplication by `3^(n-1)` on their right `E`. The propagated
condition in the other direction is also the classical condition: the
map `A_n -> A_1` uses multiplication by `3^(n-1)` on the middle `E`
and identity on the right, giving the surjection
`E(Q_v)/3^n E(Q_v) -> E(Q_v)/3 E(Q_v)`. Thus the quotient injection is
exactly the one required in Definition 3.8. Infinite places have zero
positive cohomology here because three is odd. No cartesian-condition
certificate is inserted as an assumption.

The structure is self-dual under the Weil pairing, so its core rank in
Sakamoto's Definition 3.19 is zero. The ordinary compact complex also
has Euler characteristic zero, by its `3J` representative. Macias
Castillo-Sano's Proposition 2.4 therefore gives `chi(Filtration)=0`.
These two ranks agree.

Apply Sakamoto's Proposition 3.22 and Proposition 4.4 to `A_n` over
`R_n`. His auxiliary primes have Frobenius conjugate to the element
`tau` above, with the stated cyclotomic condition. Lemma 3.17 gives
free rank-one unramified and singular local groups. Excluding
`{3,1913}` and any previously selected prime is permitted, since the
nonzero-localization primes are infinite in number.

In this case precisely two primes suffice to kill the dual Selmer
group. The original dual group is `(Z/3)^2` for every `n>=1`, by the
Kummer sequence and the proved primary group. A nonzero localization
into a free rank-one `R_n` module has image of order three: the source
is killed by three and `R_n[3]` has order three. Its kernel therefore
has dimension one. Apply the same nonzero-localization statement to
that kernel, using the Weil identification to supply the same nonzero
class on both sides of Proposition 3.22, and choose a second, distinct
prime. The strict dual
Selmer group then vanishes. One such prime cannot kill a two-dimensional
source. This is an existence construction using the published
Chebotarev localization theorem; specific numerical primes or cubic
descent representatives are not independently computed here.

Call their product `m_n`. Sakamoto's Lemma 4.6, using the cartesian
condition just proved, makes the relaxed Selmer group free of rank two
over `R_n`. This freeness does not follow from a cardinality equality
alone. Together with the rank-one local quotients and vanished strict
dual group it verifies all three conditions of Macias Castillo-Sano's
Definition 2.16, with their required core rank zero. Hence Hypothesis
2.17 and the core-vertex hypothesis in Theorem 3.4 are now established
on this actual arithmetic lane.

## Actual finite-level determinant/Stark return

Fix `n=3`, `R_3=Z/27`, and the full infinite auxiliary prime set `P_3`
from Sakamoto's Definition 3.15, with length index three. The two
selected primes form a core-vertex witness inside this set; they are
not the entire set. Its infinitude permits arbitrarily large core
extensions and all the higher component-image ideals. The
Poitou-Tate sequence gives a complex of free rank-two modules whose
kernel and cokernel are both `(Z/3)^2`. Smith normal form over this
principal ideal ring puts its differential into `diag(3,3)`, and a
unimodular coordinate change puts it into `3J`. Macias Castillo-Sano's
Theorem 2.20 identifies this actual Poitou-Tate complex canonically
with `C tensor^L R_3`. Its degree-two comparison uses minus the
Poitou-Tate map, as recorded in their equation (2.3.8); no positive
Cassels-Tate sign is inferred from it. Choosing Smith bases still does
not construct a compatible arithmetic self-duality map.

This explains both degrees: the compact `H1(C)` is zero, while
`H1(C tensor^L R_3)` is the nine-element kernel of reduced `3J`.
`localisationModelCounts27` checks that kernel and the 81-element image
in Lean. It is a check of the finite representative, external to the
canonical arithmetic quasi-isomorphism.

[Macias Castillo-Sano, Theorem 3.4](https://arxiv.org/html/2603.23978v1#S3.SS1)
now supplies an actual linear isomorphism

    phi_3: L/27L --> SS_0(A_3,F_3,P_3).

Let `delta` be the unique basis of `L` with scalar image nine under the
fixed acyclic trivialization. Then `epsilon=phi_3(delta mod 27L)` and
`2 epsilon` are bases of this actual Stark-system module. Every
component map is multiplied by a unit, so their entire sequences of
component-image ideals coincide. Corollary 3.5 identifies these with
the complete Fitting ladder of the dual Selmer group:

    I_0=(9),  I_1=(3),  I_i=R_3 for i>=2.

Fix the normalized root ideal `(3)` and its squaring map to `L`, and
transport its reduction through `phi_3`. The first basis has roots of
coefficient `1` and `-1`; the second has no root, since its residue
coefficient is the nonsquare two. Therefore no function through the
complete Fitting ladder decides rootability of a prescribed Stark
basis, even with this curve and auxiliary-prime set fixed. The two
bases are actually realized in the source's module, rather than freely
supplied labels. `fittingLadderLosesBasisSquareClass27` checks the
ideal invariance and square-class obstruction over `Z/27`.

This necessity concerns retaining basis-unit information for this
prescribed-root task. It does not force a named source to be necessary
for scalar BSD, or show that the manuscript's independently specified
native generator is either of these selected bases. Choosing a liftable
normalized basis remains possible. Integral compatibility across all
coefficient levels, the native root object, the raw Nekovar pairing
comparison, degree convention and normalized map/sign remain separate
obligations. Only the finite-level determinant-to-Stark comparison is
claimed here.

## Coverage, provenance and self-review

The source PDF versions and digests are in
`stark_core_vertex_construction.json`. The arithmetic use of Tate
uniformization, local Tate duality, core-vertex existence/freeness and
the canonical Poitou-Tate/Stark comparison is external to Lean. The
closed-image limit is a written proof; it is not established by sampled
finite-level controls. Lean additionally verifies the exact valuation,
Frobenius fourth power, explicit central-element cocycle coboundary,
transvection and finite Fitting/square-class calculations.

Distinct self-review checked the following hinges: `tau` fixes the
whole cyclotomic field; the nonsplit twist is unramified; the inertia
coefficient is a unit because the minimal valuation is two; the closed
image contains exact minus identity; its determinant fixes the
cyclotomic coordinate in the combined infinite extension; the socle
map acts by inclusion on local Kummer quotients; the two core ranks
agree; localization shrinks the strict dual group rather than a
relaxed one; freeness uses Lemma 4.6; the finite source is the
untruncated Stark-system module, not only its zeroth ideal; and the
normalized square map is fixed before basis variation. Neither an
abstract basis existence assertion nor an arithmetic compatibility
conclusion is hidden inside a new Lean record.
