# Arithmetic Nekovar--Flach transport and a compatible derived presentation

This continues the fixed 1913b1, prime-three construction. It establishes
the applicability of Nekovar's raw pairing comparison to the actual
compact complex, identifies its finite lane by a coefficient connecting
map, and constructs a compatible self-dual presentation in the derived
category. The raw minus sign is retained. Negating the raw cup product
gives the positive Flach comparison. This is not a computation of the
manuscript's final Pfaffian orientation or native Stark generator.

The arithmetic argument uses published local/global duality and Selmer
complex theory. Lean proves explicit integral chain maps, a homotopy,
linking-form transport and equation-derived local inputs. It does not
formalize continuous cohomology or the derived category. No comparison
conclusion is supplied as a new certificate field. Papers are unchanged.

## Primary sources and fixed conventions

The complete archival copy of
[Nekovar, Selmer complexes, Astérisque 310 (2006)](https://numdam.org/item/AST_2006__310__R1_0.pdf)
has now been obtained and its relevant constructions checked. The PDF
has 568 pages and SHA-256
`61c84e5ad3252a2e520747215ac57a282addc2b58c824a3637bcd77bbe02153f`.
The previous incomplete download was not used as a complete source.
Printed page 349 was also inspected as an image because OCR obscures
the equation's sign. This is a check of the sections used below, not
an audit of the whole book or the complete errata.

The checked locations are: condition (P), Section 5.1; local-error
construction and global-duality triangle, 6.2.3, 6.3.4 and 6.7.6--8;
extended/classical Selmer comparisons, 9.6.3 and 9.6.7.2--3; torsion
pairing construction, 2.10.7--14 and 10.2.2--5; and the explicit
Flach comparison, 10.8.1--7, printed pages 347--351.

[Flach's original article](https://gdz.sub.uni-goettingen.de/id/PPN243919689_0412)
is available in the publisher-volume facsimile at GDZ. Printed pages
113--117 were checked: the local-subspace definitions, pairing formula
(11), and Theorem 1's perfectness conclusion. Nekovar's adapted
construction is the one used for the comparison here. Identification
with a particular classical Cassels--Tate/Pfaffian target convention
is not inferred just from equality of the Selmer groups.

Keep `R=Z_3`, `F=Q_3`, `T=T_3(E)`, `A=E[3^infinity]`, and the ordinary
complex `C` from `odd_primary_selmer_bridge.md`. Its arithmetic imports
remain unchanged: `H1(C)=0`, `H2(C)=(Z/3)^2`, the three-primary bound
and finite-Sha identification use the previously recorded external
descent and cohomology results. Over `F`, this actual complex is acyclic.

The cochain convention is `d_Hom(f)=-(-1)^degree(f) f d` when the
target differential is zero, and shift `[k]` multiplies the differential
by `(-1)^k`. Thus, for `P=[R^2 --A_0--> R^2]` in degrees one and two,
with `A_0=3J`, `J=[[0,1],[-1,0]]`, its shifted dual is

    D(P)=RHom_R(P,R)[-3]=[R^2 --A_0^t--> R^2], A_0^t=-A_0.

## Matching the local conditions, including the bad prime

Nekovar 10.8 uses ordinary submodules at three and zero submodules at
the other finite places in `S={infinity,3,1913}`. The compact complex
previously constructed uses an unramified local complex at 1913.
These descriptions must be compared before applying the pairing theorem.

Splitness at 1913 is established directly. The reduced Weierstrass
equation has a singular point `(485,714)`. At that point both first
derivatives vanish, and the tangent quadratic is

    Y^2+XY-(3*485+1)X^2
      = (Y-346X)(Y-1566X) mod 1913.

The slopes are distinct rational residues. Together with the established
minimal discriminant valuation two and unit `c4`, this is split
multiplicative type `I_2`. The independent square check
`295^2+c6=1913*100` gives the same split criterion. Lean checks the
point, derivatives, tangent coefficients and distinctness, not a
supplied reduction-type tag.

Tate uniformization identifies `T^I` with the first Tate line `R(1)`:
the inertia coefficient two is a unit, as proved earlier. Arithmetic
Frobenius acts on this line by 1913. Hence the unramified local complex
is represented by

    [R --1912--> R].

Its differential is a unit in `R`, since `1912=1 mod 3`. It is acyclic,
so its map to the full local complex can be replaced by the zero local
condition in the derived category. This uses more than the Tamagawa
unit: nonsplit multiplicative reduction with the opposite Frobenius
could have produced a nonunit here.

The full local complex at 1913 is acyclic too. The Neron reduction
sequence has a pro-1913 formal subgroup, a split torus of residue
order 1912, and a component group of order two. None contributes
three-primary torsion or a quotient by a three-power. Thus
`E(Q_1913)[3^n]=0` for all `n`. Local Tate duality, using the Weil
pairing, gives `H2(Q_1913,E[3^n])=0`. The local Euler-characteristic
formula away from three then gives `H1(Q_1913,E[3^n])=0` as well.
The three-cohomological dimension of this local field is two.
Continuous inverse-limit cohomology yields `RΓ(Q_1913,T)=0`: the
finite-level complexes are all acyclic, and their cohomology limits
and derived-limit terms are zero. This is not an inference from a
bounded collection of residue checks.

At three use the actual saturated ordinary line `T^+`. The Weil
pairing gives an isomorphism `T/T^+ -> Hom_R(T^+,R)(1)`, so its
module-level local error is zero. At 1913 the zero/zero conditions
have module-level error `T`, whose local cohomology has just been
proved zero. Consequently Proposition 6.7.6(iv) and Theorem 6.3.4
give an actual global cup-adjoint isomorphism

    C --> RHom_R(C,R)[-3].

Here the Weil form is a perfect duality, all modules are free and of
finite type over the regular DVR, and condition (P) holds because
the prime is three. Transposition data for these submodule conditions
are provided by 6.7.8. Proposition 10.2.5 gives skew-symmetry of the
torsion pairing. Since two is invertible on `F/R`, it is alternating.
The zero global error and Proposition 2.10.12 give perfectness. Thus
the perfect alternating form used below is the actual arithmetic raw
cup form, rather than an independently assigned finite form.

## The finite arithmetic identification and its sign

The coefficient triangle `C -> C tensor F -> C tensor^L(F/R)` has
a connecting isomorphism

    delta_B: H1(C tensor^L(F/R)) --> H2(C),

because `C tensor F` is acyclic. The discrete extended group on the
left is the classical `Sel_{3-infinity}(E/Q)`: the ordinary local
quotient at three has no invariants by the previously established
non-anomalous condition; at 1913 the local invariants vanish by the
reduction argument above; and global three-primary torsion is zero.
These remove the invariant/error terms in the extended-to-classical
sequence (the cone construction underlying 9.6.3). The local Kummer
comparison is also explicitly supplied by 10.8.3 and 9.6.7.2--3.
Since the Mordell-Weil group has order two, this identifies the left
group with the actual `Sha[3^infinity]`, not just a group of equal order.

There is a small but material cochain sign. In 10.8.6 the displayed
rational cochain is `X=(-a_1,a^+_{1,v},A_{0,v})`, with `dX=i(x)`.
Modulo `T`, its global class is `-alpha`, where `alpha` is the
Selmer class used in 10.8.5. Therefore that construction's map
`theta(alpha)=[x]` equals `-delta_B(alpha)`. The same sign occurs
in the second argument. Bilinearity cancels these two signs, and
Proposition 10.8.7 gives the precise arithmetic equation

    U_raw(delta_B(alpha),delta_B(beta))
       = - <alpha,beta>_Flach.

Accordingly, `U_corrected=-U_raw` is the positive Flach pullback.
The raw theorem is not rewritten as a positive theorem. Nor does
the correction determine a Pfaffian orientation, native generator,
or the manuscript's target height.

## Lifting finite pairing normalization into the actual derived map

Choose coordinates on `H2(C)=(R/3)^2`. The previous coefficient
argument, which applies to every perfect alternating form, writes
the corrected form as `u*(x_1 y_2-x_2 y_1)/3 mod R`, where its
residue coefficient is one or two. Lift it to the unit `u=1` or
`u=2` of `R`. Raw and corrected forms have coefficients `-u` and
`u`, respectively.

On `P` the chain map with degree components

    a_u^1=u I, a_u^2=-u I

has `a_u^2 A_0=A_0^t a_u^1`. It is an isomorphism since `u` is a
unit. Its cup form has value `u v^t y` on degrees `(1,2)` and
`-u x^t w` on degrees `(2,1)`. The torsion construction from
2.10.7--14 evaluates it at `(x,A_0^(-1)y)` in the latter degrees,
giving

    -u x^t A_0^(-1)y = u*(x_1 y_2-x_2 y_1)/3 mod R.

This agrees with `linkingLift`'s existing negative-inverse convention.
In particular the explicit chain map `a_u` represents the corrected
form, while `a_(-u)` represents the raw form. The map/sign distinction
has been calculated, not selected to populate a positive certificate.

Why does matching that finite form also match the derived map? An
arbitrary chain map `P -> D(P)` has components `(F_1,B)` satisfying
`B A_0=A_0^t F_1`; cancellation of three forces `F_1=J B J`.
Its finite pairing determines `B mod 3`, since `A_0^(-1)=-J/3`.
If another target matrix `B'` induces the same pairing, then
`B-B'=3K` for a matrix over `R`. The explicit homotopy `H=J K`
satisfies

    F_1-F'_1=H A_0, B-B'=A_0^t H.

Thus the maps are homotopic. Bounded free resolutions compute these
derived morphisms, so the actual transported arithmetic cup-adjoint
is the same derived morphism as `a_(-u)` (or `a_u` after correction).
This closes the compatibility gap for this rank-zero paired derived
object. It does not select a canonical chain map or coordinates.

The coordinate normalization itself has a chain lift

    h^1=diag(1,u), h^2=diag(u,1), h^2 A_0=A_0 h^1.

Pulling back `a_1` along it gives `a_u`. Both determinants are `u`,
so the induced determinant-line multiplier is their ratio one.
Consequently this paired derived normalization preserves the canonical
acyclic trivialization and its basis `delta` of scalar image nine.
It is compatible with the same determinant/Stark line used previously.

## Coverage, self-review and surviving source obligation

Lean's `CTDerivedTransport` proves the chain equation, the forced
source matrix, the explicit homotopy, the normalization chain lift,
equal determinants, pulled-back cup matrices and exact rational linking
return. Those are integer/rational statements. The same algebra over
`Z_3`, the arithmetic cup map and the cohomological application are
written mathematics with the external imports above. The book/errata
and classical scalar normalization remain separate from a successful
Lean build.

Distinct self-review checked the splitness using the actual tangent
quadratic, the direction of Frobenius, the entire local cohomology
vanishing, the extended-group invariant terms, both connecting-map
signs, the shifted dual differential, the torsion-product evaluation,
the homotopy identities over the DVR, and cancellation of determinant
multipliers. The pairing coefficient is derived from the actual
arithmetic form before the presentation is constructed.

The coherent Stark bases `e` and `2e` from the preceding construction
still have the same curve, paired derived object, determinant
trivialization and component ideals, but different prescribed-square
rootability. Normalizing the finite pairing does not recover that
independently variable Stark-basis unit. A comparison identifying
the manuscript's independently prescribed native basis must supply
additional information. This result therefore does not prove that
a named Cassels--Tate recognition source alone repairs the unit loss,
or that all named sources are necessary for scalar BSD.

Fresh checkpoint verification passed `make verify-lean` (88 build jobs),
`make validate test public-audit` (26 tests), and the independent
`check_odd_primary_bridge.py --check --gp` reproduction with PARI.
All ten new Lean results depend only on standard Lean axioms
(`propext`, `Quot.sound`, and, for the rational linking return,
`Classical.choice`). The 51 existing manifest entries, five declared
trust-base axioms, and 69 statement-audit statuses are unchanged;
successful checks do not upgrade the original comparison theorem.

Open: canonical integral determinant/Stark naturality; the prescribed
native generator and root object; its image in the classical Pfaffian
target with the stated degree and final orientation; and arithmetic
named-source ablations. The current normalized GZ predicate still
entails scalar BSD by itself. None of these obligations is weakened
or silently supplied by this supporting construction.
