# Native local-to-global component product

The carrier is the curve

    E: y^2 = x^3 + 385x + 1225.

The permitted native observations are the geometric tame-inertia actions at
five and seven. Define their factors as det(1-tau), before consulting component
groups, and multiply the factors with their distinct place labels. This gives
an actual global component-product return on this curve. It supplies neither
the paper-native OC comparison nor full named-source indispensability. The
papers and their main claims are unchanged.

## Equation, support and arithmetic controls

Exact equation arithmetic gives c4=-18480, c6=-1058400 and

    Delta = -4300534000 = -2^4 * 5^3 * 7^3 * 6269,
    j = 9199872/6269.

The nonintegral rational j excludes CM, using the standard integrality theorem
for CM j-invariants. Lean checks the invariants and nonintegrality, not the CM
theorem. It also proves primality of every displayed factor and the universal
prime-divisor equivalence: p divides |Delta| exactly when p is in
{2,5,7,6269}. Primality of 6269 is derived from the exhaustive divisor check
below 80 and the fact 80^2>6269; this avoids a large recursive certificate.
Consequently the integral equation has good reduction at every other prime
by the standard discriminant criterion, and those component factors are one.
This is an all-prime argument, not a sampled conductor lookup.

Fresh PARI/GP 2.15.4 gives the following Tate outputs, reproduced by
`scripts/check_global_tame_product.py --gp <executable>`:

| Place | Conductor exponent | Kodaira type | Component number |
| ---: | ---: | --- | ---: |
| 2 | 4 | II | 1 |
| 5 | 2 | III | 2 |
| 7 | 2 | III | 2 |
| 6269 | 1 | I1 | 1 |

All local model changes and the global minimal-model change are the identity.
The conductor is 122872400 and the global Tamagawa product is four. These
are exact arithmetic computations using Tate's algorithm, external to Lean.
In particular, the wild prime two is not passed through the tame p>=5 theorem.
The PARI meanings of the local type codes and global product are documented
in its [elliptic-curve reference](https://pari.math.u-bordeaux.fr/dochtml/html/Elliptic_curves.html).

With fixed seed 20261003, `ellrank` returns lower and upper Mordell-Weil rank
bounds [2,2]. Its returned points are (0,35) and
(22800/49,3445805/343), whose curve equations the checker verifies exactly.
Independence and the rank upper bound are PARI arithmetic descent outputs,
not a Lean proof inferred merely from two points. This algebraic rank result
is ancillary: no analytic rank claim, Sha finiteness or p-primary Sha vanishing
is inferred from it. In particular it does not instantiate higher-GZ scope.

## Construct the local factors independently

At either p=5 or p=7, let pi^4=p and scale x=pi^2 X, y=pi^3 Y. The resulting
model has coefficients

    A'=385/p, B'=(1225/p^2) pi^2, Delta'=Delta/p^3.

At five these are A'=77, B'=49 pi^2; at seven they are A'=55, B'=25 pi^2.
The discriminant is a unit, so this model has good reduction. The equation
pi^4=p is Eisenstein and has degree four, prime to p. After an unramified
extension adjoining fourth roots of unity, its normal closure is tame.
For a primitive fourth root zeta the geometric inertia action on the good
fiber is

    (X,Y) -> (zeta^-2 X, zeta^-3 Y).

It has exact order four: its square is elliptic inversion, which is nontrivial
in these odd characteristics. The original models have purely additive type
III, independently checked by the shallow Tate inputs and the PARI outputs.
The good fiber is nonsingular because A' is a unit and p>=5. These calculations
establish the tame order-four domain before reading a component target.

The construction in [`tame_component_return.md`](tame_component_return.md)
then gives inertia characteristic polynomial T^2+1 and det(1-tau)=2 at each
place. Its checked [Nicaise Corollary 3.3(2)](https://arxiv.org/pdf/0901.1809v2)
identifies this determinant with geometric component order. A group of order
two has no nontrivial automorphism, so Frobenius fixes it and the rational
component number is also two. This arithmetic argument uses ell-adic geometric
inertia for ell different from p; it does not replace a p-adic OC descent map.

Thus the native product is

    B_native(E) = det(1-tau_5) det(1-tau_7) = 2*2 = 4.

The independent local outputs at two and 6269 contribute one, and the proved
discriminant support exhausts all bad places. Therefore B_native(E) equals
the whole finite Tamagawa product. No equality to Tam was included in the
definition of either native factor.

## Ablation, normalization and source scope

Removing either tagged local leaf changes this construction's product from
four to two. A single local determinant therefore cannot be identified with
the global Tamagawa product on this example. This is dependency of this native
product assembly; it is not a countermodel to scalar BSD with the other named
recognition sources frozen. The existing `piBSD` record matches each local
readout's `tamFactor` to global `shell.Tam`. This is a valid conditional field
if the readout represents the global aggregate, but its arithmetic assembly
is not supplied by identifying it with one local component factor.

Four is a unit at every odd prime, in particular both shallow source places.
Its coefficient support is {2}, although c_2=1. Observing local congruences
only modulo units at five and seven misses this exponent entirely. Merely
adding Boolean unit flags at all primes also cannot recover multiplicity:
two and four have the same flags. Exact rational quotient-unit comparisons,
as used in `RationalLocalGlobal`, are stronger and do detect their difference.
The full set of bad places includes two on this particular curve; no claim
that this set misses the coefficient support is made.

## Numerical source-carrier repair

`RecognitionSources.gammaPadicDescent` now requires actual `IsPrime p` and
p%2=1. Its nondivisibility statement is the concrete proposition not(p|c_p),
derived from primality, oddness and c_p in {1,2}; it is no longer an arbitrary
proposition field. Arithmetic additivity, tameness, Sha vanishing and the
local comparison remain supplied and are not inferred from numeric scope.
The numerical prime-three control certifies only these elementary conditions.
`gammaShaPersistence` separately requires actual primality; no unsupported
oddness exclusion is imposed. `piBSD` inherits these facts at its matched
prime. The descent inheritance retains both the bad-place and specified-lift
hypotheses, rather than inferring a readout from either alone.

## Mechanization and distinct self-review

`GlobalTameProduct.lean` proves the equation/support statements, two shallow
branches, cover divisibility inputs, exact native product, integral basis
invariance, leaf-removal controls and coefficient-support/unit obstructions.
`checkedTateProfile` is explicitly an imported computation trace. Equality of
the native product with that trace is finite algebra; identifying the trace
with Neron components uses the written arithmetic imports above. Lean does
not implement Neron models, local Galois representations or arithmetic rank
descent. The fixture and checker retain the original exact arithmetic outputs.

Distinct self-review checks: all-prime support versus finite samples; prime
two's wild reduction versus the tame theorem; component number versus
geometric order; one local determinant versus the global product; distinct
places with identical matrices versus duplicate counting; rank bounds versus
analytic rank; unit flags versus quotient valuations; and product-leaf
dependence versus full source ablation. No source certificate has been
populated with a missing OC, CT or eta conclusion. The normalized GZ input
still independently supplies scalar BSD; full named-source indispensability
under that frozen input remains obstructed.

Fresh checkpoint gates passed: `make verify-lean` (93 jobs, all 51 manifest
declarations), `make validate test public-audit` (26 unit tests), and the
independent PARI reproduction of this fixture. The 18 new regression axiom
closures use only standard Lean axioms. These gates cover the represented
algebra and records; they do not mechanize the written arithmetic imports.
