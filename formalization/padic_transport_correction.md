# Correct finite and dual exponential transports

The ordinary local source in the current manuscript assigns the dual
exponential the type
\(H_f^1(\mathbb Q_p,V)\to D_{\rm dR}(V)/\mathrm{Fil}^0\).
That type belongs to a finite-lane logarithm under appropriate
isomorphism hypotheses. It is not the dual exponential.

The exponential has direction
\[
\exp_V:D_{\rm dR}(V)/\mathrm{Fil}^0\longrightarrow H^1(\mathbb Q_p,V),
\]
and its dual, indexed with the dual representation, has direction
\[
\exp^*_{V^*(1)}:H^1(\mathbb Q_p,V)\longrightarrow
\mathrm{Fil}^0 D_{\rm dR}(V).
\]
See [Berger, introduction, pp. 100–101](https://www.maths.tcd.ie/EMIS/journals/DMJDMV/vol-kato/berger.dm.pdf).
The representation indexing matters even though elliptic-curve Tate
modules admit a self-duality identification.

The logarithm is generally defined first on the exponential local
condition \(H_e^1\), with a quotient accounting for crystalline
Frobenius invariants. The dual exponential kills the geometric local
condition \(H_g^1\), which contains \(H_f^1\). Its restriction to the
finite condition is therefore zero. These are distinct maps with
distinct targets, rather than interchangeable scalar conventions. See
[Darmon–Rotger, §1.3, equations (36)–(37)](https://web.mat.upc.edu/victor.rotger/docs/DR3.pdf).

## Mechanized correction

`Apparatus.PAdic.FiniteExponentialComparison` records the exponential
into the finite condition and a two-sided inverse logarithm, with the
de Rham quotient as its target. This is an explicit isomorphism input;
the module does not assert that every de Rham representation has such
an isomorphism. Arithmetic use must establish the exponential's image
and kernel in the relevant reduction and twist convention.

`DualExponentialReciprocity` records the other target, the de Rham
pairing, the cup pairing, the exponential on the dual representation,
reciprocity, finite orthogonality, and nondegeneracy of the de Rham
pairing. `dualExpKillsFinite` derives vanishing on finite classes from
those pairing laws. It does not assume that vanishing as a field.
`dualExpFiniteNotInjective` then derives noninjectivity whenever the
finite carrier has two distinct elements.

The proof has the following exact argument: for a finite class \(h\),
reciprocity identifies the pairing of \(\exp^*h\) with any dual de Rham
class with a cup pairing against a dual exponential class. Orthogonality
makes all these pairings zero. Nondegeneracy forces \(\exp^*h=0\).
Consequently its restriction to a nontrivial finite vector space cannot
supply a nonzero comparison determinant.

`pAdicMap` now uses the inverse logarithm on the ordinary finite lane.
The signed lane has a distinct comparison carrier. No shared type named
`Exp` silently identifies finite and signed/Iwasawa comparisons. The
determinant-line readout and signed comparison remain supplied external
transport data.

## What this repairs and what it leaves open

The ordinary and signed coordinate projector calculations remain valid:
the full identity source has zero residual, omitting the first coordinate
has residual trace one, and unsigned signed-coordinate aggregation has
residual trace one. Replacing the mislabeled ordinary comparison
coordinate by a finite logarithm preserves these finite computations.

This correction does not establish arithmetic realization of three
independently varying local coordinates, integral determinant transport,
Fontaine–Laffaille/Wach normalization, a real scalar realization of a
p-adic determinant, or signed Iwasawa specialization. In particular,
renaming a coordinate is not a proof of those comparisons. The signed
branch requires its own precise local conditions and regulator before
attaching a determinant to the existing coordinate diagnostic.

The manuscripts and extracted provenance record are unchanged. Their
dual-exponential notation must be corrected in the later paper phase.
The Lean regressions instantiate the new interfaces with nontrivial
rational coordinate data to check consistency and distinguish the two
maps. That model is not presented as Galois cohomology.
