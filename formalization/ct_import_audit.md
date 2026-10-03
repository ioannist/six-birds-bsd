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
The Nekovář check uses the
archival page-349 extraction; a complete book/errata audit has not been
completed. Knudsen–Mumford determinant theory and the original Flach
paper still need the exact downstream theorem/hypothesis comparison.
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
