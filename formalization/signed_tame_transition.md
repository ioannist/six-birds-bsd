# A native tame/cyclotomic transition and the signed-map obstruction

The target remains a comparison with the independently prescribed signed
pairing/corestriction source. The carrier constructed here is the actual
local field tower of the supersingular good cover at seven on
y^2=x^3+385x+1225. Its operations are field inclusion, a square-root
coordinate, the cyclotomic power relation and the field norm. The construction
repairs the uniformizer return and excludes a proposed power-series route.
It does not produce a signed local pairing or a global Sha readout.

## Source selection and exact boundary

[Forras-Lei, arXiv:2609.13063v1](https://arxiv.org/pdf/2609.13063v1), dated
11 September 2026, offers a potentially supersingular route. Its arithmetic
identification in Proposition 4.4 and main theorem assume CM; our curve is
non-CM. Definition 3.17 supplies the alternating trace pattern, but does not
identify the project's signed map. There are additional literal checks:
the displayed binomial argument in (3.4), printed page 8, has constant term
one; after correcting that argument, its stated prefactor still fails the
quartic leading-coefficient relation. Remark 3.2, printed page 7, also states
disjointness incompatible with the quadratic overlap below. These issues
exclude importing this displayed transition as our local operator. No
judgment about every conclusion of the preprint is inferred.

The PDF's SHA-256 is recorded in `signed_tame_transition.json`; pages 7-8
were visually checked against the extracted equations. This is a newly
examined candidate, not a previous dependency of the BSD landing.

## Realize the quartic field and its cyclotomic overlap

Let K be the unramified quadratic extension of Q_7 and take pi with
pi^4=-7. Then L=K(pi) is a cyclic tame quartic extension. This is the
existing good cover after an unramified unit change: in F_49=F_7(i), i^2=-1,
the element 2+2i has square i and fourth power -1. Its simple Hensel lift
xi in K has xi^4=-1. Multiplying the original fourth root of seven by xi
gives pi. Thus the same curve has good supersingular reduction over L;
its order-four inertia is unchanged. The lift and field identification
are written arithmetic; Lean checks the residue identities.

Scaling by this pi gives coefficients -55 and 25 pi^2, so the good fiber
over F_49 is Y^2=X^3+X. Exact enumeration and independent PARI both give
64 points, trace -14 and determinant 49. This is the square of the old
trace-zero residue-degree-one Frobenius: its eigenvalues are both -7.
Thus the relation beta^2=-7 for the old operator becomes beta_new^2=49,
not -49, for the degree-two operator. Lean checks this algebra. A signed
or eta comparison must keep the operator and residue-degree conventions.

Choose compatible primitive 7^n-th roots zeta_n, n>=1, and set
F_n=K(zeta_n), L_n=L F_n. A quadratic overlap is explicit already at n=1.
For z=zeta_1 put

    g=z+z^2+z^4-z^3-z^5-z^6.

The polynomial identity

    g(X)^2+7 = (1+X+...+X^6)
                (X^6+X^5-3X^4+X^3+X^2-7X+7)

gives g^2=-7. Therefore K(sqrt(-7)) is in both L and F_1. Their intersection
has degree dividing gcd(4,6)=2 and is exactly this quadratic field, not K.
At every n, gcd(4,6*7^(n-1))=2, so the same intersection persists. In
particular [L_n:F_n]=2 and [L_n:L]=3*7^(n-1). For n>=2 the successive
extension L_n/L_(n-1) has degree seven. The Lean polynomial identity proves
the overlap's square root; the field-degree implications use the standard
cyclotomic degree and finite Galois intersection formulas.

## Construct actual uniformizers and their polynomial return

Write t_n=1-zeta_n, a uniformizer of F_n. The product formula for seven
gives -7=u t_n^(6*7^(n-1)), with u a principal unit. To see its residue,
divide each factor 1-zeta_n^a by t_n: the quotient reduces to a. The product
of all units modulo seven is -1, and each residue occurs 7^(n-1) times.
Thus the extra minus sign gives residue one. Fourth powers are bijective
on principal units by Hensel, since four is prime to seven. The exponent
6*7^(n-1) is two modulo four. Kummer classes then identify L_n/F_n with
F_n(sqrt(t_n))/F_n. The possible sign is absorbed by i in K. This derives
the coordinates from the actual field, rather than assigning them.

Take lambda_n with lambda_n^2=t_n. It is a uniformizer of L_n. Its valuation
under v_7(7)=1 is

    v_7(lambda_n)=1/(12*7^(n-1)).

The native cyclotomic operation zeta_n -> zeta_n^7 gives the exact relation

    lambda_(n-1)^2 = 1-(1-lambda_n^2)^7
      = 7 lambda_n^2 -21 lambda_n^4 +35 lambda_n^6
        -35 lambda_n^8 +21 lambda_n^10 -7 lambda_n^12 +lambda_n^14.

Lean derives this from the two square-coordinate equations. The sign is
fixed by t_n=1-zeta_n; changing it would not return the chosen lower
uniformizer. This polynomial relation is valid at every tower level and
does not assume an analytic branch on the full open unit disc.

## Why an integral single-variable square-root transition fails

Consider any formal series A(X) with A(0)=0 satisfying

    A(X)^2 = 1-(1-X^2)^7.

Its linear coefficient a must satisfy a^2=7. With pi^4=-7, the choice
a=i pi^2 has the correct square. Neither a=pi nor a=pi^2 has that square
in characteristic zero. After choosing either valid sign of a, formal
uniqueness over L gives

    A(X)=a X sqrt(U(X)),
    U(X)=1-3X^2+5X^4-5X^6+3X^8-X^10+X^12/7.

The binomial expansion must use U-1, whose constant term is zero.
An expansion in powers of U itself has infinitely many contributions
to the constant coefficient and is not a formal-series substitution.
It does not converge seven-adically either. For j=7^r,

    binom(1/2,j) = product_(0<=k<j)(1-2k)/(2^j j!)

is a seven-adic unit. For each 1<=b<=r, exactly j/7^b numerator factors
are divisible by 7^b; no factor is divisible by 7^(r+1). These counts equal
the factorial's valuation counts, and the factor 2^j is a unit. The terms
at these indices do not tend to zero when the argument is one.

Even the corrected formal expansion is not an integral series. In Z=X^2,
its uniquely forced coefficients through Z^6 are

    sqrt(U)=1-(3/2)Z+(11/8)Z^2-(7/16)Z^3
              -(13/128)Z^4-(13/256)Z^5+(281/7168)Z^6+...

Squaring and solving the coefficient equations derives these values.
Lean proves both the equations and their unique return; the offline checker
derives them recursively, and PARI independently reproduces them.
Since 7168=7*1024 with numerator and 1024 prime to seven, the last coefficient
has valuation -1. Consequently A's X^13 coefficient has valuation
1/2-1=-1/2, or -2 when normalized by v_L(pi)=1. Thus A is not in O_L[[X]].
A change between the two valid signs cannot repair integrality.

The corrected binomial series also cannot be evaluated on the required
tower uniformizers. For n>=2 the exact native relation gives

    U(lambda_n)=t_(n-1)/(7 t_n),
    v_7(U(lambda_n))=1/7^(n-1)-1<0.

The argument U(lambda_n)-1 has that same negative valuation. At j=7^r,
the binomial coefficient is a unit and the valuation of its term tends
to minus infinity. The terms fail even the necessary convergence condition.
This is an all-level obstruction, not extrapolation from finite samples.
The formal series over L exists near zero; that does not give an integral
endomorphism or a branch valid at these uniformizers.

## A legal repair retaining the actual field norm

For n>=2, let N_n be the field norm L_n -> L_(n-1). Its conjugates on the
cyclotomic field give

    N_n(t_n)=product_(j=0..6)(1-zeta_n zeta_1^j)=1-zeta_(n-1)=t_(n-1).

Therefore N_n(lambda_n)^2=lambda_(n-1)^2. The two possible values are
lambda_(n-1) and -lambda_(n-1). Since the extension degree is odd,
N_n(-lambda_n)=-N_n(lambda_n). Choose the sign so that

    N_n(lambda_n)=lambda_(n-1).

Starting with either branch at n=1, this constructs a norm-compatible
branch at every level by induction. The choice is uniquely determined
among the two roots because the lower uniformizer is nonzero. The square
coordinates alone erase that sign; the retained native norm and lower
branch repair it. Lean proves the uniform branch-return implication
from the square identity and odd-norm sign law. The actual field norm
and the infinite tower instantiation are written mathematics.

This repair uses the multiplicative norm of field elements. It must not
be confused with the additive trace in a formal group or the point norm
on E(L_n). Constructing the signed local generators, their Kummer/dual
pairing, the actual determinant-line map, and its normalization remains
the next obligation. The repaired uniformizer return alone does not
establish the relaxed Honda identification or Coleman-map comparison.

## Mechanization and distinct self-review

`SignedTameTransition.lean` proves the Gauss identity and overlap square,
native polynomial transition, leading-slope repair, unramified residue
phase, coefficient factorization and forced root coefficients, valuation
inputs, degree control and branch repair. It does not implement local
fields, formal power series, seven-adic convergence or signed arithmetic.
The checker verifies the exact polynomial and coefficient records; optional
PARI reproduction checks the independent cyclotomic quotient and root series.
No named-source certificate has been populated.

Self-review checked: the distinction between the full cyclotomic tower
and its Z_7 subtower; the quadratic tame/cyclotomic intersection; the sign
in t=1-zeta; the required square of the leading coefficient; legal formal
substitution versus analytic convergence; a finite nonintegral coefficient
versus the independent all-level divergence argument; multiplicative field
norm versus additive elliptic trace; a norm-compatible branch versus signed
generator production; and CM theorem scope versus the non-CM example.
The manuscript claims and the remaining OC, CT, signed and normalized-GZ
source obligations are unchanged.

Fresh checkpoint checks passed: `make verify-lean` (96 jobs and all 51
manifest declarations), `make validate test public-audit` (26 unit tests,
29 semantic entries and 40 supplementary assessments), and the new checker's
independent PARI reproduction of the Gauss identity, root coefficients and
F_49 point count. The inspected candidate PDF matches the recorded digest.
All 14 new regression axiom closures use only standard Lean axioms. These
gates check the represented algebra and provenance inputs, not the unresolved
native signed pairing or determinant-line comparison.
