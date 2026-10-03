# Good-cover Frobenius refinement and the OC beta boundary

This construction continues the actual curve y^2=x^3+385x+1225 from
[`global_tame_product.md`](global_tame_product.md). Both its shallow places
have native inertia factor det(1-tau)=2. Nevertheless their good covers have
different Frobenius regimes. The construction proves a new restricted loss
of information and repairs it by retaining the selected root's unit status. It does
not identify that root with the manuscript's additive U_p stabilization,
derive an eta value or establish full named-source indispensability.

## Two independently computed good fibers

On the covers pi^4=p, the coefficients already constructed are
(77,49 pi^2) at five and (55,25 pi^2) at seven. Reducing them gives:

| Place | Good fiber | Points | Frobenius trace | Polynomial |
| ---: | --- | ---: | ---: | --- |
| 5 | Y^2=X^3+2X | 2 | 4 | T^2-4T+5 |
| 7 | Y^2=X^3+6X | 8 | 0 | T^2+7 |

Lean exhaustively counts affine points plus infinity. The Python checker uses
both exhaustive enumeration and a quadratic-discriminant count, and fresh
PARI independently returns the same counts and traces. The arithmetic
identification of the count with Tate-module trace uses
[Milne, Proposition V.7.5, printed page 217](https://www.jmilne.org/math/Books/EC2.pdf);
the Frobenius determinant is its degree p. The same polynomial supplies the
good-reduction crystalline Frobenius eigenvalues, by the standard comparison
for good reduction. Neither arithmetic cohomology comparison is mechanized.

An independent Hasse check classifies the first fiber as ordinary and the
second as supersingular. At five, c4=-96 is four modulo five; at seven,
-c6=0. These are the Hasse-invariant formulas in those characteristics; see
the [Sage reference and implementation](https://doc.sagemath.org/html/en/reference/arithmetic_curves/sage/schemes/elliptic_curves/ell_field.html#sage.schemes.elliptic_curves.ell_field.EllipticCurve_field.hasse_invariant).
The checker also calculates the coefficient of X^(p-1) in
(X^3+A X)^((p-1)/2): four at five and zero at seven. PARI's
`ellissupersingular` gives zero and one respectively. Lean checks the
numerical c4/c6 inputs; the Hasse criterion is an external arithmetic import.

## The square relation has a necessary trace condition

For P(T)=T^2-aT+q and Q(T)=T^2+q there is a universal Bezout identity

    T P(T) - (T-a) Q(T) = a q.

In a characteristic-zero field with q nonzero, a common root can exist only
if a=0. Lean proves this over lawful abstract fields, not just integer or
rational test values. At five, the right side is twenty, so no eigenvalue
of the actual good-cover Frobenius can satisfy beta^2=-5. Its inverse-square
factor also cannot equal -1/5. At seven, the actual polynomial itself gives
beta^2=-7, so the inverse-square factor is -1/7 for either eigenvalue.

This excludes a proposed identification of the square-relation beta with
this ordinary cover Frobenius. It is not a contradiction in the manuscript's
conditional eta record: that record explicitly assumes its square relation
and refers to a chosen additive U_p object. A different operator or twist
would need its own definition and comparison. Shallow type III by itself
does not ensure a trace-zero good cover.

The obstruction survives every positive unramified residue degree. Traces
t_f of powers of the five-adic Frobenius satisfy

    t_0=2, t_1=4, t_(f+2)=4t_(f+1)-5t_f.

For every f>=1, t_f is one or four modulo five. Lean proves this for all f,
and then excludes a common root of T^2-t_f T+5^f and T^2+5^f in every
characteristic-zero field. The first eight traces are 4,6,4,-14,-76,-234,
-556,-1054. This is a uniform theorem, not extrapolation from those samples.
The ordinary Newton slopes are zero and f for Frobenius over F_(5^f), so
neither eigenvalue can have valuation one-half under v_5(5)=1. Ordinary
reduction is geometric and survives further good-reduction covers. Thus
changing the residue degree does not provide the proposed beta^2=-5 either.
The Newton-slope and geometric-invariance facts remain written imports;
Lean's all-degree polynomial theorem has the precise q=5^f normalization.

## Construct both refinements in the complete five-adic field

Here P(T) has roots beta_plus=2+i and beta_minus=2-i with i^2=-1. Construct
i in Z_5 with i=2 modulo five as follows. Given r_n with

    0 <= r_n < 5^n, r_n=2 mod 5, r_n^2+1=0 mod 5^n,

put m=5^n, k=(r_n^2+1)/m and choose the unique digit d in {0,...,4}
with d=-4k modulo five. Set r_(n+1)=r_n+m d. Since 2r_n=4 modulo five,

    r_(n+1)^2+1 = m (k+2r_n d+m d^2)

is divisible by 5m. The new root has the old residue modulo m, remains two
modulo five and lies in [0,5m). Starting with r_1=2, induction gives a
compatible root at every coefficient level. Completeness gives i in Z_5,
and its square is minus one because the equation holds modulo every 5^n.
This argument constructs the complete root; finite checker samples are
controls, not the proof of the limit. The initial roots are
2,7,57,182,2057,14557.

The plus root is a unit with residue four. The minus root has valuation
exactly one, since i=7 modulo twenty-five gives 2-i=-5 modulo twenty-five.
Each residue branch has exactly one root: for two polynomial roots b,c,
subtracting their equations gives (b-c)(b+c-4)=0; on either common branch,
b+c-4 is a unit. Lean proves the field cancellation statement; the written
reduction argument supplies the nonzero multiplier. Thus the ordinary
unit-root condition independently selects beta_plus.

## A loss witness and its repair

The two selected eigenspaces belong to the same curve, cover and unrefined
Frobenius module. The declared lower lens keeps the native inertia determinant
and the Frobenius trace/determinant, namely (2,4,5), and erases the selected
eigenline. Their inverse-square factors are

    beta_plus^-2=(3-4i)/25,
    beta_minus^-2=(3+4i)/25.

They differ by -8i/25 and hence are unequal. Lean derives both expressions
and their inequality over every characteristic-zero field containing such i.
It proves that no function of the lower lens can return both selected-root
factors. The complete five-adic digit construction realizes the hypotheses
arithmetically. Retaining the selected root's unit/nonunit status repairs
the readout on both refinements: return the plus-root factor for a unit and
the minus-root factor otherwise. Lean proves this uniform repair from the
polynomial equations and the two observational unit-status conditions.
The written digit construction establishes those conditions for the actual
five-adic unit predicate. They do not supply a factor-equals-target field.

If a target prescribes the ordinary unit root from the outset, that root is
already the unique unit root of the polynomial. The two-refinement no-go
does not apply to that restricted target, and does not prove that an extra
recognition source is needed to choose the unit root. The no-go concerns
returning the factor of an independently selected refinement after erasing
which refinement was selected.

Although the first expression has denominator twenty-five, it is a unit:
its numerator has valuation two. Computing it to precision 5^n from the
displayed fraction requires the root to precision 5^(n+2). The checker
retains these extra two levels and compares against direct inversion of the
unit beta. The other inverse-square has valuation minus two. Ignoring the
precision loss would give incorrect residues even in these small controls.

This witness concerns beta^-2, not a complete eta value. The leading moment
may change with the refinement, and no invariance or freezing of that moment
has been proved. Neither this split pair nor its unit-root repair establishes
the paper-native OC descent map or its globally normalized Tam factor.

## Original target, remaining bridge and distinct self-review

The source carrier's `LC_triv_E_L` and `LC_triv_E` are still arbitrary types,
and `descent_p_OC` is an arbitrary map between them. The displayed local
congruence and the eta identity remain supplied propositions. The repository
does not yet define a native ordinary/anticyclotomic leading coefficient,
its trivialization or the cover-to-base operator independently of those
comparisons. Constructing a candidate component factor does not fill this gap.

A next arithmetic comparison must specify the modular object on the cover
and base, the chosen eigenline in each regime, the leading-term functional
and integral normalization, and the action of the actual descent map. The
ordinary and supersingular cover regimes above must be handled separately.
Giving the operator a determinant chosen to equal c_p would encode the
missing conclusion rather than derive it. The original normalized GZ input
also still entails scalar BSD by itself; proving independent necessity of
the other two sources while keeping that input fixed is impossible.

Distinct self-review checks the polynomial obstruction in characteristic
zero (the modulo-five common root zero is a deliberate boundary control),
the original additive curve versus its smooth cover, unramified degree versus
Frobenius normalization, count versus imported cohomology, complete digit
limit versus finite samples, unit versus nonunit eigenvalue, selected-root
factor versus eta with its moving moment, and scoped readout necessity versus
full named-source indispensability. No paper claim or recognition certificate
has been changed by this construction.

Fresh checkpoint gates passed: `make verify-lean` (94 jobs and all 51
manifest declarations), `make validate test public-audit` (26 unit tests),
and the fixture's PARI reproduction of Tate/rank and both good-fiber outputs.
All 14 new regression axiom closures use only standard Lean axioms. These
checks verify the represented algebra and numerical inputs; the written
arithmetic cohomology and complete five-adic instantiation remain imports.
