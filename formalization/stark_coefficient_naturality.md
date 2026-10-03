# Coefficient naturality of the arithmetic determinant/Stark comparison

For the fixed curve 1913b1 at three, the finite maps of Macias
Castillo–Sano fit together with the actual Stark coefficient maps.
They therefore define a canonical integral linear isomorphism

    Phi_can: L=det_R^(-1)(C) --> S, R=Z_3.

This supplies the coefficient-naturality obligation left open in
`stark_inverse_limit_construction.md`. It does not identify the
manuscript's independently prescribed native Stark generator, a
classical Pfaffian target, or named-source necessity for scalar BSD.
The word canonical here is relative to the fixed arithmetic complex,
local conditions and determinant/Stark conventions, not a choice of
coordinates or a newly supplied image certificate. Papers are unchanged.

## Imports and the actual finite maps

Keep the curve, `T`, ordinary local conditions, nested full auxiliary
sets `Q_n`, core rank zero and arithmetic hypotheses already established
in `stark_core_vertex_construction.md` and
`stark_inverse_limit_construction.md`. Write `R_n=R/3^n`,
`A_n=T/3^nT`, and `S_n=SS_0(A_n,F_n,Q_n)` for positive `n`.
Let `t_(n+1,n):S_(n+1)->S_n` be Sakamoto's coefficient map followed
by the inverse of restriction from `Q_n` to `Q_(n+1)`. These are the
maps defining the previously constructed arithmetic `S`.

Use the fixed version of
[Macias Castillo–Sano, arXiv:2603.23978v1](https://arxiv.org/pdf/2603.23978v1),
SHA-256
`77f7cb9c5e4a3ed2078ae3782499092e035f6054d4e23ab8e9159d42012731c7`.
The relevant construction is Lemma 2.22 and Sections 2.3.2–3,
printed pages 17–20, together with Propositions 2.9 and 2.18,
Proposition 3.3 and Theorem 3.4, printed pages 23–25.
The theorem itself supplies each finite canonical isomorphism

    phi_n:L/3^nL --> S_n.

Coefficient naturality is derived below from its explicit maps; it is
not inferred merely because every finite map is called canonical.

For the coefficient transition use
[Sakamoto, Algebra & Number Theory 12 (2018)](https://msp.org/ant/2018/12-10/ant-v12-n10-p02-s.pdf),
SHA-256
`e674f67b2a9f51df164871708b73725fb3445f7d9ff6e4a20213be7e66c15f64`:
Lemma 3.17, Lemma 3.25, Remark 4.5(2), Lemma 4.6,
the construction before Proposition 4.12 and Section 5.
The Stark exterior conventions can be compared explicitly using
Definition 2.3 and Lemma 2.1 of that paper and formula (47) and
Proposition A.3 of
[Burns–Sano, arXiv:1612.06187v1](https://arxiv.org/pdf/1612.06187v1),
printed pages 47–49, SHA-256
`661deb8cdb0de31b8195b55eac68fe1f59ae96947d40debef03e0711b0f297e3`.
The latter is the checked preprint formula, not an audit of every
statement in its later journal version.

## One common core vertex for an adjacent coefficient square

Fix `n>=1`. Choose a core vertex `m` in `N(Q_(n+1))` at level
`n+1`. By the checked cartesian conditions and Sakamoto Remark 4.5(2),
the same `m` is a core vertex at level `n`. This is stronger than
choosing unrelated core vertices at the two levels.

For `j=n,n+1`, put

    V_(j,m)=H1_(F_j^m)(Q,A_j),
    W_(j,m)=direct_sum_(q|m) H1_/F_j(Q_q,A_j),
    P_(j,m)=[V_(j,m) --lambda_(j,m)--> W_(j,m)] in degrees 1,2.

Both terms are free of rank `nu(m)`, by Lemmas 3.17 and 4.6. Moreover
the *natural* coefficient maps identify

    V_(n+1,m) tensor R_n = V_(n,m),
    W_(n+1,m) tensor R_n = W_(n,m).

For the first assertion, Lemma 3.25 gives the split injection of the
reduction of the free relaxed group into the reduced global group.
Propagated local conditions put its image in the reduced relaxed
Selmer group. Both modules are free of the same rank by core-vertex
freeness. The split injection is then an isomorphism: its splitting
restricts to that target, and the complementary finite module has
length zero. The second assertion is the actual local base change
of Lemma 3.17. No claim of base change for arbitrary nonfree Selmer
groups is needed. Localization commutes with coefficient reduction,
so these are an identification of complexes, not just of term ranks.

Proposition 2.18 identifies these free complexes with the relevant
Poitou–Tate complexes. Enlarge the finite set `S` to contain `m`
for this adjacent square. The natural chain inclusion sends the
relaxed global group into `H1(G_(Q,S),A_j)` and the auxiliary local
quotients into the full local sum. It is a quasi-isomorphism by the
Poitou–Tate exact sequence and the vanished relaxed dual group.
All its maps commute with coefficient reduction.

## Cochain lifts commute with reduction before determinants are taken

For each global or local module `X` in Lemma 2.22, denote its cochain
lift map by `l_j`. Given a continuous cochain `rho` with values in
`X/3^(n+1)X`, choose a continuous lift `rho_tilde` into `X`.
The same lift also lifts the reduction of `rho` modulo `3^n`.
Therefore, in the quotient of the continuous-cochain module,

    reduction(l_(n+1)(rho)) = l_n(reduction(rho)).

Independence of the lift is exactly Lemma 2.22: two lifts differ by
`3^j` times a continuous cochain. Their difference vanishes in that
quotient. This argument is uniform in `n` and does not select lifts
coherently in advance.

The explicit representative of `C` in Section 2.3.2 is fixed over `R`
and has torsion-free terms. Its ordinary coefficient reductions
compute derived reduction over this DVR. Section 2.3.3 defines
the Poitou–Tate comparison `varphi_j` as follows: in degree one,
take the global lifted cochain modulo coboundaries; in degree two,
take the *negative* of the local lifted cochains in the first
summand and zero in the global two-cochain summand. The quotient
maps, localization, coboundaries and this fixed minus sign all
commute with coefficient reduction. Consequently on the free
common-core complexes there is an actual commutative derived square

    P_(n+1,m) tensor R_n --varphi_(n+1) tensor R_n--> C tensor^L R_n
              |                                          ||
              v                                          ||
          P_(n,m) ----------------varphi_n---------------> C tensor^L R_n.

If the chosen finite set is enlarged further, inflation of global
cochains and inclusion of old local summands give the same comparison.
At a newly added good place a global unramified class has zero image
in the local quotient. Such finite unramified classes lift through
the integral unramified complex (its quotient group has cohomological
dimension one). Thus the additional local lifted component vanishes
in the representative's quotient too. This checks compatibility with
Proposition 2.9 and the usual Selmer-complex independence of `S`;
the finite set enlarged for the adjacent square is not new input
to the final integral map.

## The determinant/Stark square, including exterior signs

At a core vertex the Stark component is

    X_(j,m)=det(V_(j,m)) tensor det(W_(j,m))^dual
            =det^(-1)(P_(j,m)).

Exterior biduals here are actual top exterior powers because the
modules are free. Their duals and determinants commute with the
identified base change. Sakamoto's coefficient map is defined by
evaluation at this same core vertex, this natural base change of
`X_(j,m)`, and inverse evaluation. Macias Castillo–Sano's Proposition
3.3 uses the same evaluation and determinant identification.

The exterior convention is not a hidden unit choice. In Burns–Sano
formula (47), contraction by a wedge `f` is dual to `z -> f wedge z`.
This is exactly the map in Sakamoto Lemma 2.1, where the dual of the
removed quotient is wedged first. Fix increasing order on rational
auxiliary primes. Decomposing the full local dual determinant as
removed primes first, then retained primes, introduces the same
permutation sign in both definitions. In Macias Castillo–Sano this
is encoded by the local dual factors in Lemma 3.1 and Definition 3.2;
in Sakamoto it is the determinant decomposition of Definition 2.3.
The interchange of the displayed ungraded tensor factors does not
introduce another sign. These identifications intertwine the Stark
transitions. In a coefficient square the set `m` and its ordering
are fixed, so every such exterior sign is unchanged on reduction.

Taking inverse determinants of the preceding derived square and
then evaluating at `m` now gives

    t_(n+1,n)(phi_(n+1)(z mod 3^(n+1)L))
        = phi_n(z mod 3^nL)  for every z in L.

Evaluation at a core vertex is injective, so checking that component
checks the full Stark system. Restriction to `Q_(n+1)` and its inverse
are also determined by that component. This proves the asserted
square for the actual coefficient maps defining `S`, for every `n`.

## The canonical integral return

The free rank-one module `L` is complete, so `L=lim_n L/3^nL`.
Define `Phi_can(z)` to have component `phi_n(z mod 3^nL)` at level
`n`. The square just proved shows that it belongs to the actual
inverse limit `S`. This constructs the integral map rather than
choosing one basis lift at one level.

Each `phi_n` is invertible. Their inverses commute with reduction
by cancellation in the forward commutative square. A compatible
system in `S` therefore has compatible inverse images in `L/3^nL`,
which have a unique preimage in complete `L`. These constructions
are inverse `R`-linear maps. The map is unique with the stated
reductions because both limits are separated. Independence from
the auxiliary core vertices follows from the finite constructions,
not from freeness alone.

Let `delta` be the unique element of `L` whose image under the fixed
canonical acyclic trivialization is nine. Then

    e_can=Phi_can(delta)

is a canonical basis for these conventions. With `M=(3)` in the
same rational trivialization, the quadratic map
`q_can(v*3)=v^2 e_can` is now determined by the canonical integral
comparison. The previous same-curve witnesses can be chosen as
`e_can` and `2e_can`: every component ideal agrees, but only the
first has a root under this fixed square map. For any earlier chosen
linear lift of `phi_3`, its basis differs from `e_can` by a unit
congruent to one modulo 27. The already proved digit-lifting
criterion makes that unit a square, so the earlier square-image
subset agrees with the canonical one.

## Coverage and distinct self-review

Lean's `StarkCoefficientNaturality` constructs the inverse map on
compatible families, derives its naturality from the forward square,
proves both inverse identities and uniqueness, and refutes a limit
map for an explicit family of finite isomorphisms that fails that
square. The false control uses the fixed residue-three tower with
identity at the first level and multiplication by two afterwards.
It prevents inferring an integral comparison merely from finite
isomorphisms. It is not an arithmetic source-ablation example.

Arithmetic coefficient naturality, cochain lifts, exterior conventions
and the determinant functor are written mathematics using the
primary constructions checked above, rather than mechanized Galois
cohomology. No final native image or positive scalar orientation
has been supplied as a certificate field.

Distinct self-review checked the common core vertex and its survival
under base change, the split injection rather than an unsupported
general Selmer base-change assertion, the natural localization maps,
the actual negative degree-two cochain formula, exterior contraction
order and permutation signs, independence of an enlarged finite `S`,
and inverse compatibility and completeness. Canonical integral
naturality is therefore supplied on this fixed lane. The native
manuscript selections, degree/target conventions, final Pfaffian
orientation and named-source arithmetic ablations remain open.

Fresh checkpoint verification passed `make verify-lean` (89 build
jobs) and `make validate test public-audit` (26 tests). The seven
new regression results use only `propext` and `Quot.sound`;
`inverseNaturality` uses no axioms. The 51 manifest entries,
five declared trust-base axioms and 69 statement-audit statuses
are unchanged. This verification covers the represented limit
algebra and repository consistency, not arithmetic mechanization
or completion of the original source comparison.
