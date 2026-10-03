# Kummer completion, component erasure, and the corestriction boundary

This construction uses the actual curve y^2=x^3+385x+1225 from
[`global_tame_product.md`](global_tame_product.md). It compares the local
point subgroup E_0(Q_p) with E(Q_p), including their entire odd-primary
Kummer images and compatible completions. It then checks the ordinary
restriction/corestriction candidate for the good cover at five. Neither
comparison identifies the manuscript's independently prescribed OC or signed
map, or establishes full named-source indispensability.

## Construct the canonical quotient comparison

Let A be an abelian group, H an additive subgroup, and suppose cA is contained
in H. Take integers u,v with cu+mv=1. Inclusion induces

    i_m: H/mH -> A/mA.

Every ambient class has an explicit representative in H: set h=cu a. Then
h-a=-mv a, so i_m([h])=[a]. If a belongs to H after multiplication by m,
then a=cu a+vm a belongs to H already. Consequently, for h,h' in H,

    h-h' in mA  iff  h-h' in mH.

This proves injectivity as well as surjectivity. The explicit inverse is
s_m([a])=[cu a]. It is well defined inside H/mH: if a-b=mx, then
cu(a-b)=m(cu x), with cu x in H. Both inverse laws follow from these
calculations. Inclusion is canonical; different Bezout choices produce
the same inverse because that inverse is unique.

The hypotheses concern an ordinary subgroup and an annihilator of A/H.
They do not supply a Kummer, component, determinant or BSD conclusion.
Finiteness of A/H is not needed for this algebraic statement. In the arithmetic
application, its known finite order supplies c.

## All coefficient levels and the actual completion

If 2A is contained in H and p is odd, put m=p^n and

    u_n=(p^n+1)/2, v_n=-1.

Then 2u_n+mv_n=1 at every n, including the trivial level n=0. The explicit
inverse sends [a] to [(p^n+1)a]. The forward maps commute with the natural
quotient reductions, since they are all induced by the same inclusion.
Their inverses commute as well: apply the injective forward map to both
candidate composites and use its two inverse laws. Thus there are inverse
maps on the actual compatible-sequence objects

    lim_n H/p^n H  <->  lim_n A/p^n A.

`KummerComponentErasure.lean` constructs both quotient types, their maps,
the transition maps, the compatible-sequence types, and the two completed
inverse laws. This is not an inference from sampled levels. Lean proves
a bijection of these carriers. The maps are group homomorphisms because
they are induced by inclusion and scalar multiplication. With the inverse
limit topology of discrete quotient groups they are continuous, since each
coordinate depends on the corresponding coordinate only. Those group and
topology assertions are written mathematics, not additional Lean coverage.

## Equality of embedded Kummer images

For K=Q_p and m=p^n, the Kummer boundary kappa_m factors through A/mA for
A=E(K). Its factorization comes from the multiplication-by-m exact sequence,
not a new component-comparison certificate. See
[Milne, Elliptic Curves, IV section 2, equation (28), printed pages 112-113](https://www.jmilne.org/math/Books/EC2.pdf),
including its local-field row. The standard point subgroup E_0(Q_p), defined
by nonsingular reduction, is described in II section 4, Theorem 4.1,
printed pages 62-63 of the same book.

If [A:E_0(K)]=2, then 2A is contained in E_0(K). The constructed representative
Q_n=(p^n+1)P belongs to E_0(K), and Q_n-P=p^n P. Therefore

    kappa_(p^n)(E_0(K)) = kappa_(p^n)(E(K))

as actual subsets of the same H^1(K,E[p^n]), at every n. This retains much
more than equal dimensions or abstract group orders. Every operation on the
fixed ambient cohomology and these embedded subsets, including restrictions
of a fixed pairing, receives identical inputs. Compatibility of the Kummer
boundaries with coefficient transitions also preserves the full family.
Lean proves the subset equality for any map respecting the quotient relation
and the all-level no-readout theorem below. Galois cohomology, Kummer exactness
and their arithmetic interpretation remain explicit external inputs.

For the actual curve, fresh PARI Tate outputs give c_5=c_7=2 and type III
at both places; the native tame-inertia computation independently returns
the same component orders. The standard local definition c_p=[E(Q_p):E_0(Q_p)]
therefore supplies exactly the subgroup hypothesis above. The fixture and
reproduction command are the existing `global_tame_product.json` and
`scripts/check_global_tame_product.py --gp <executable>`. No new curve rank
or Sha assertion is inferred.

There is also an explicit point witnessing properness at both places:
P=(0,35) satisfies the curve equation and reduces to (0,0) on y^2=x^3
at five and seven. Both partial derivatives vanish there, so P is outside
E_0 in the checked minimal models. The tangent slope is 11/2, giving

    2P=(121/4,-1611/8).

The doubling formula and cleared curve equation give
1611^2=121^3+385*121*16+1225*64. Reduction of 2P gives (4,3) at five and
(4,6) at seven, both nonsingular since the y derivative is nonzero.
Lean checks the exact equation, tangent and reduction inputs. This exhibits
the marked-subgroup loss using an actual local point, not only an existential
coset argument or an assigned arithmetic tag.

## A precise loss witness and a native repair

Declare the carrier to be marked subgroups H of this fixed A with 2A contained
in H. The lower lens retains every embedded Kummer-image subset at every
p-power level, and erases the marking. Compare H=E_0(K) with H=A. Their
indices are two and one but their entire lower observations agree. Hence
no function of that family can recover the marked index, or even decide
whether the marked subgroup is all of A. Lean's `noMarkedSubgroupReadout`
proves the latter universal no-readout statement from the constructed
family equality and a genuine point outside H.

This is a marked-subgroup obstruction. For a target asking for the canonical
E_0 of a given curve, the equation determines that subgroup independently.
The full recognition source also retains the component number and may
retain inertia. Neither is erased by the theorem. These are not two distinct
arithmetic curves holding all other named sources fixed. Keeping the curve
equation in a lower source therefore invalidates an inference that its
canonical c_p cannot be recovered.

At coefficient prime two, the canonical inclusion has cokernel

    coker(H/2H -> A/2A) = A/(H+2A) = A/H.

Thus that comparison retains the missing component quotient exactly.
Alternatively, the native integral inertia cokernel in
[`tame_component_return.md`](tame_component_return.md) returns its order two
on this checked domain. These repairs add a different coefficient observation
or retain inertia; the odd-primary family cannot manufacture it. Lean checks
the control H=2Z: the classes of 2 and 0 coincide in Z/2Z but not in H/2H,
and the actual modulo-two map has unequal image subsets for H and Z.
The coprimality hypothesis is essential.

## Test ordinary restriction/corestriction on the actual good cover

At five let L=Q_5(pi), pi^4=5. The polynomial is Eisenstein, and Q_5 contains
the fourth roots of unity by the complete square-root construction in
[`cover_beta_refinement.md`](cover_beta_refinement.md). Thus L/K is a cyclic
Galois extension of degree four; the curve has good reduction over L.
For M=E[5^n], ordinary continuous cohomology satisfies

    Cor_(L/K) Res_(L/K) = [4].

The transfer identity is
[Milne, Class Field Theory, II Proposition 1.30, printed page 70](https://www.jmilne.org/math/CourseNotes/CFT.pdf).
For finite discrete coefficients and an open subgroup of an absolute Galois
group, the same identity follows from continuous cochains. The finite group
Gal(L/K) has order invertible on M and its invariants, so its positive-degree
cohomology vanishes by averaging. Inflation-restriction gives

    H^1(K,M) -> H^1(L,M)^Gal(L/K)

as an isomorphism. Multiplication by 4 is a coefficient unit. The normalized
corestriction (1/4)Cor is the inverse on this invariant summand, not on all
of H^1(L,M). These statements are compatible with every coefficient level.
Lean proves the Bezout inverse and normalized left-inverse implication;
the native cohomology identity and inflation-restriction are written imports.

The same return respects actual ordinary Kummer images. If kappa_L(P) is
Galois invariant and 4t=1 modulo 5^n, then the base point t Norm_(L/K)(P)
has restricted Kummer image

    t sum_g g kappa_L(P) = 4t kappa_L(P) = kappa_L(P).

This proves surjectivity onto invariant Kummer classes without assuming that
an invariant point class has an invariant representative. Naturality gives
the other inclusion. It still supplies no exact component multiplier two:
this ordinary comparison is an isomorphism, and two is already a 5-adic unit.

There is a concrete rank obstruction to taking a usual determinant of the
norm on the full point completions. The formal logarithm identifies an open
subgroup of E(F), for a finite extension F/Q_5, with an additive lattice in F.
Here is the analytic step behind that identification. In the formal parameter
t at infinity the invariant differential is (1+sum_(r>=1) b_r t^r)dt,
with integral b_r. Integrating gives a characteristic-zero formal logarithm
t+sum_(r>=2) b_(r-1)t^r/r, which respects the formal group law. These
are the differential/log constructions in the
[Sage formal-group reference](https://doc.sagemath.org/html/en/reference/arithmetic_curves/sage/schemes/elliptic_curves/formal_group.html#sage.schemes.elliptic_curves.formal_group.EllipticCurveFormalGroup.log).
For positive v_5(t) its terms converge, since r v_5(t)-v_5(r) tends to
infinity. On a sufficiently deep ideal the higher terms define a strict
contraction after subtracting the linear term, so contraction inversion
makes the logarithm an isomorphism onto that ideal. The local formal parameter
identifies this neighborhood with an open subgroup of the point group.
The point group is compact and this subgroup has finite index, so the
finite quotient adds no rank after rationalization.
Thus the rationalized completion dimensions are [F:Q_5]. For this cover they are
four over L and one over K. In the local logarithm coordinates the norm is
trace, whose row on the basis (1,pi,pi^2,pi^3) is (4,0,0,0), since the
conjugates multiply pi by the four fourth roots of unity. The full map is
rectangular. A determinant-line construction would need a specified
invariant summand or relative complex and its normalization; a determinant
of this full linear map is not available. The formal-logarithm identification
and the norm/cohomology compatibility here are written arithmetic, not Lean.
The norm is trace in these coordinates because the logarithm is a group
homomorphism with coefficients in K, and hence commutes with every Galois
conjugation of a sufficiently small point.

## Distinct self-review and surviving obligations

Self-review checked the subgroup annihilator versus its exact index;
surjectivity versus injectivity; the direction of the quotient relation;
explicit inverses versus assumed comparison fields; compatibility of the
entire inverse limit; image subsets versus abstract isomorphism; the actual
index-two arithmetic instantiation; the coefficient-two failure control;
and a marked-subgroup target versus the curve's canonical E_0. It separately
checked restriction/corestriction order, normalization by the extension
degree, invariant summands versus whole cover cohomology, and unequal
point-module ranks versus determinant-line maps.

The native OC object and its normalization remain unidentified. Signed
Selmer conditions need not be the ordinary Kummer conditions used here;
their actual comparison with `gammaShaPersistence`, and its global Sha
readout, remains open. Full integral p-adic Galois data is not claimed to
lose c_p in this shallow scope. No recognition or eta certificate is filled
with the new conclusion. The normalized higher-GZ input still already
entails scalar BSD, so an indispensability proof for the other named sources
with that full input fixed cannot follow from these local constructions.

Fresh checkpoint verification passed: `make verify-lean` (95 jobs and all
51 manifest declarations), `make validate test public-audit` (26 unit tests,
29 semantic entries and 40 supplementary assessments), and independent
PARI reproduction through the global-product checker. All 24 new regression
axiom probes were inspected: 23 use only the standard Lean axioms and the
equation-derived point inputs are axiom-free. Audit statuses and unresolved
obligations were retained. These checks establish the represented algebra
and record consistency, not mechanization of the written arithmetic imports.
