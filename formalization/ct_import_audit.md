# Cassels–Tate import: source checks and constructive sign repair

The conditional Lean comparison is a valid projection from a supplied
comparison record. The following source checks do not establish that the
named arithmetic papers populate that record. They identify the bridges
needed to do so. No manuscript or final normalized sign certificate has
been changed.

## Primary statements checked

| Source | Verified statement and scope | Consequence for this interface |
| --- | --- | --- |
| [Sakamoto, 2018](https://msp.org/ant/2018/12-10/ant-v12-n10-p02-s.pdf), notation and Theorems 4.10, 5.6 | Odd residue characteristic; the cartesian Selmer/core-vertex hypotheses and a Stark-system basis control higher Fitting ideals of the dual Selmer group. | This supplies a Fitting-ideal route. It does not specify the manuscript's square-root Stark generator, normalized Pfaffian map, or a prime-two extension. |
| [Macias Castillo–Sano, v1](https://arxiv.org/html/2603.23978v1), Theorem 3.4 and Corollary 3.5 | At an odd prime, a Selmer-complex determinant modulo a prime power is identified with a Stark-system module, under Hypothesis 2.11 and a core vertex with matching core rank. A determinant basis is an input to the Fitting-ideal consequence. | The source is a full determinant, rather than the proposed square-root Fitting object. A specific basis and its square-root/Pfaffian transport still need construction. |
| The same preprint, Theorem 4.2 | Good ordinary reduction above the odd prime, non-anomalous/Tamagawa conditions in Hypothesis 4.1, and a Cartan-subgroup image condition; derived orders 1 through p−1. The Bertolini–Darmon pairing equals minus the Nekovář pairing. | This is a derived-height comparison. It cannot be used as a sign-free Cassels–Tate Pfaffian comparison or an unrestricted supersingular theorem. |
| [Nekovář, Selmer complexes](https://www.numdam.org/item/AST_2006__310__R1_0.pdf), Proposition 10.8.7, printed page 349 | In the setting of 10.8.5–6, the raw cup product on torsion H² is minus the Flach pairing. | The manuscript's H¹/div source needs an explicit shift/identification. A positive normalized sign needs a defined correction and orientation calculation; it is not the raw cited equation. |
| [Fisher–Schaefer–Stoll](https://mathe2.uni-bayreuth.de/stoll/papers/yoga.pdf), Theorem 6.3 | Over a number field, the Cassels–Swinnerton-Dyer pairing on n-Selmer × 2-Selmer equals the multiplicative encoding of the classical Cassels–Tate pairing. | The cited theorem number is correct in this version. It supplies classical pairing normalization with a two-torsion argument, rather than a Fitting or odd-primary square-root generator theorem. |

These checks were made against primary statements on 2026-10-02. The
Macias Castillo–Sano and coauthor-hosted Fisher–Schaefer–Stoll PDFs were
checked in extracted text around the cited statements. Their downloaded
PDF SHA-256 digests are respectively
`77f7cb9c5e4a3ed2078ae3782499092e035f6054d4e23ab8e9159d42012731c7`
and `6c6f01166085b952f13a82488233126b9b8b6531848f31d638da44d38790d22e`.
The Nekovář check now uses the complete 568-page archival PDF, SHA-256
`61c84e5ad3252a2e520747215ac57a282addc2b58c824a3637bcd77bbe02153f`,
with the relevant local-duality, torsion-product and comparison sections
checked and printed page 349 inspected visually. Flach's original
publisher-volume facsimile, printed pages 113–117, was also checked.
A whole-book/errata audit, Knudsen–Mumford downstream applicability,
and the manuscript's classical scalar/Pfaffian normalization remain open.
See `ct_derived_transport_construction.md` for the fixed arithmetic lane.
The eight symbolic T_E labels also lack a statement-by-statement assignment
to these arithmetic results in the Lean interface.

## What has been constructed

`lean/SixBirdsBSD/Closure/CTSignTransport.lean` proves the following on
explicit rational carriers. These algebraic lemmas do not construct a
Galois representation, Selmer complex, or arithmetic determinant line.

1. Given a supplied cohomology map f and raw comparison
   `raw(x,y) = −flach(f(x),f(y))`, negating the raw pairing produces the
   positive pullback comparison. A simultaneous negation of a linear map
   and its source generator preserves the image. A final positive sign is
   therefore possible, but requires identifying both corrections in the
   arithmetic objects.
2. Opposite alternating rational lifts with upper-right entries 1/2 and
   −1/2 have identical entries modulo integers and different Pfaffians.
   Squaring the coefficients also loses their sign. Neither torsion-valued
   pairing data nor a determinant square alone selects that scalar sign.
3. A rational class modulo integers killed by two and by an odd integer
   is zero. The proof explicitly returns an integer representative using
   `(2k+1)r − k(2r) = r`. In a biadditive classical pairing, an
   odd-primary first argument and a two-torsion second argument give just
   such a class. Thus the mixed pairing in the classical 2-Selmer result
   cannot itself normalize a nonzero odd-primary pairing. The nonzero
   two-torsion class 1/2 is a checked control: two-torsion alone does not
   force vanishing.
4. For an actual rational quotient, being a unit at every prime is
   equivalent to being +1 or −1. The negative-defect factor model has
   native fixity and passes every prime-unit check, while failing scalar
   BSD. The earlier positive-quotient theorem removes precisely this
   remaining ambiguity.

The rational sign corrections must not be mistaken for selecting a lift
of every F/O-valued pairing. The earlier lift-dependence counterexample
still applies. An arithmetic presentation and determinant-line target are
required before these scalar operations are the intended readout.

## Repair path preserving the intended conditional endpoint

Define the actual complex and its degree convention, identify its torsion
cohomology with the classical finite lane, and carry the raw negative
comparison through that identification. Then construct the square-root
determinant object and its orientation, transport a specified Stark
generator, and compute the combined sign/unit change. The normalized
positive sign may be retained if that computation proves it; inserting
the positive certificate before this calculation would assume the bridge.

The odd-prime scope and the ordinary scope of the derived-height theorem
must be kept separate from a prime-two or signed supersingular extension.
The current Lean comparison remains conditional on all its supplied
comparison and sign fields. Completing their arithmetic realization,
unit normalization, and source assignment remains open.

## Repair of curve and prime matching

The previous `chiCTpComparison` accepted a curve, an arbitrary prime-type
element, and four unindexed propositions, but did not use them to select
the comparison record. A single record could provide the same map,
generator, target, and sign at every nominal curve/prime. This was a
mechanization mismatch with the instance-specific mathematical statement.

The repaired interface fixes a `chiCTpContext` before taking a comparison
certificate. That context declares the hypothesis and theorem families,
source and target carrier families, canonical-map property, sign, and
partial native generator/target selections. `chiCTpImport context E p`
now contains applicability at exactly E and the numerical prime p,
including the project's concrete primality predicate. The same indices
select every hypothesis, carrier, theorem statement, and sign.

Native selections can be unavailable. The certificate must exhibit the
generator and target and prove that they equal the context's preselected
values at this instance. This avoids assuming the existence of Stark
bases at all curves and primes. Two certificates for one fixed context
and instance have the same selected generator and target. An unavailable
selection prevents a certificate even when the hypothesis packet holds.
No uniqueness of the entire comparison map follows from this consistency
lemma; that needs an appropriate canonical-map theorem.

Both scalar landing variants and the shell AOR instance now require the
CT record at the shell's curve. The comparison and landing return the
matched applicability packet explicitly. This does not establish that
the record covers every support prime, that its target is the shell's
Sha factor, or that the other import structures describe the same
arithmetic complex. Those remain separate mathematical identifications.

`CTInstanceChecks.lean` provides positive and false-target controls using
the proved hyperbolic normalization. Its Bool-indexed presentations have
moduli two and four, with assigned local scopes three and five. The
comparison squares integral half-orders to the determinant factors four
and sixteen. Wrong-instance, composite-prime, absent-selection, and
wrong-map controls reject the corresponding certificates or returns.
The eight citation labels are True in this diagnostic. It verifies the
interface on actual finite computations, not the named arithmetic
theorem stack or the existence of an arithmetic Stark basis.

Self-review checked that the positive diagnostic is inhabited, that
selection ablations retain applicability, that the sign remains an
independently supplied normalization certificate, and that the scalar
landing still follows from its existing recognition predicate. Thus this
repair prevents accidental substitution within a declared family but
does not establish arithmetic source indispensability or make the CT
import necessary to the scalar landing.

## Arithmetic finite normalization now realized, with its scope preserved

Certified two-descent for 571a1 and 1309a1 supplied an arithmetic
dimension-only separation. A checked intermediate eight-descent result
in Miller's small-conductor proof now identifies 1309a1's entire
two-primary group with H_4. The new 2045b1 partner gives the same H_4
lane while preserving every finite-place Tamagawa number and the trivial
rational torsion group of 571a1. See `finite_pairing_construction.md`
for the published computation, applicability calculations and trust
boundary; this is not a locally rerun eight-descent.

`ShaFourNormalization.lean` derives a unit coefficient for every
alternating nondegenerate form on H_4, constructs an additive coordinate
normalization, and returns the actual integer hyperbolic presentation
and positive cokernel order sixteen. Classical Cassels-Tate alternation
and nondegeneracy on finite elliptic-curve Sha groups supply the
arithmetic paired interpretation. This realizes a paired finite-group
presentation. It does not identify the same presentation with Nekovar's
arithmetic complex or a chosen Stark-system generator and determinant
orientation. Those source-comparison maps remain open.

At two, 1309a1 also fails the nondivisibility-of-Tamagawa condition:
its product is four. The matched 2045b1 example has product one, but
prime two still lies outside the cited odd-prime Stark-system scope.
There is also a non-anomalous local-condition obstruction at two:
2045b1 has good ordinary reduction and residue-field order two. Its
ordinary discrete quotient has an invariant subgroup of order two.
The local classical/ordinary comparison therefore needs a correction;
removing only the odd-prime restriction would not supply the bridge.
All three curves are semistable, so they do not provide the Gamma
sources' additive-prime instances. Populating the existing chi_CT
certificate with their finite cardinalities would bypass these
substantive applicability and comparison obligations.

## An actual ordinary complex and a prescribed-basis obstruction

The new 1913b1 instance at three satisfies the ordinary, non-anomalous,
Tamagawa and torsion conditions. Exact point counts at five give a
Frobenius polynomial whose reduction has roots of order eight; Lean
checks every matrix with its trace and determinant, proving the
nonsplit Cartan condition rather than supplying that condition as a
certificate. The published three-descent and arithmetic upper bound
identify its three-primary Sha group with `(Z/3)^2`.

The cohomology theorem and Kummer sequences give `H1(C)=0` and
`H2(C)=(Z/3)^2` for the ordinary compact complex. Hence it is
noncanonically quasi-isomorphic to the actual `3J` presentation in
degrees one and two. Its inverse determinant has image `(9)` under
the acyclic trivialization, and its square-root ideal is `(3)`.
Lean proves the presentation's kernel/cokernel return and normalizes
every perfect alternating form on this group. The arithmetic derived
identification and determinant-functor argument are written proofs
with explicit imports, external to Lean.

On this one fixed curve, bases with scalar images nine and eighteen
generate the same three-adic ideal. Only the former lifts through the
fixed squaring map on `(3)`. Thus retaining the ideal loses information
needed to lift a prescribed basis. The finite square-class obstruction
and its unit-retention repair are proved in Lean. This is arithmetic
basis variation on an actual determinant line; it is not a source
indispensability theorem for scalar BSD.

Rank-two admissible sets in the source's Section 4.2 do not themselves
give the rank-one core vertices required by Theorem 3.4. The separate
construction in `stark_core_vertex_construction.md` now supplies that
input by checking Sakamoto's hypotheses on the actual curve: a
multiplicative inertia transvection, residual irreducibility, exact
central minus identity and cocycle vanishing, and cartesian Kummer
conditions. Published existence/freeness theorems give two auxiliary
primes at each coefficient level. The determinant/Stark isomorphism
therefore applies over `Z/27`, and the complete Fitting ladder loses
the rootability of a prescribed Stark basis under unit scaling.
Its arithmetic theorem applications are external to Lean; the finite
calculations and uniform cocycle proof are mechanized. The subsequent
`stark_inverse_limit_construction.md` supplies coherent arithmetic
Stark bases at every coefficient level, with identical component ideals
and different normalized-square rootability. It proves an exact residue
square-class repair and independence of the square-image subset from
the chosen integral lift of the fixed finite comparison. This does
not construct a canonical integral comparison or the native generator.
The compatible all-level native Stark basis, manuscript degree shift
and orientation remain open. The subsequent paired derived construction
below resolves arithmetic self-duality and the raw Flach comparison on
this fixed compact lane. In the compact convention here,
the proposed unshifted `H1(C)/div` is zero. Shifting it to the finite
degree also inverts the determinant convention, which must be carried
through the comparison. See `odd_primary_selmer_bridge.md` and its
fixture for the exact source chain and self-review.

## Actual arithmetic pairing and compatible derived transport

`ct_derived_transport_construction.md` now matches the local conditions
of the actual 1913b1 compact complex to Nekovar's Section 10.8. An
equation-derived split node at 1913 gives two rational tangent slopes;
the invariant Tate line has Frobenius 1913, so its unramified local
differential 1912 is a three-adic unit. The entire local cohomology
complex is acyclic, which also removes the bad-prime duality error.
The ordinary Weil line removes the error at three. Global duality
therefore supplies the actual perfect alternating raw torsion pairing.

The coefficient connecting map identifies Sha with torsion H2. Both
arguments of Nekovar's cochain construction acquire a minus sign;
these cancel each other but leave Proposition 10.8.7's raw minus-Flach
equation. Explicit negation gives the corrected positive comparison.
An explicit chain map on `3J` represents this arithmetic duality:
matching finite pairings forces matching derived maps by a displayed
homotopy. Its coordinate normalization has equal determinants in both
degrees and preserves the canonical acyclic trivialization.

Lean checks the integral matrix equations, homotopy and rational linking
return, together with the split-node and unit inputs. Arithmetic duality
and derived-category applicability are written imported-theorem proofs,
not new Lean certificate fields. This does not select the prescribed
native Stark unit or classical scalar orientation. The full named-source
endpoint and the eight symbolic T_E assignments remain unresolved.
