# Height differential and regulator: a conditional bridge

The target is the paper's conditional BSD-to-Six-Birds translation. The
Neron–Tate pairing, Mordell–Weil lattice and arithmetic comparison transport
are supplied inputs. This construction derives the coordinate algebra used
by the height column; it does not require an unconditional BSD theorem or
independently construct these arithmetic inputs. The manuscripts are unchanged.

## Full-source Schur return

Fix half-vectorized symmetric tangent coordinates, dimension
`n = r(r+1)/2`, and the paper's Euclidean audit energy `C = I_n`.
The legal source is the full coordinate vector, `L(x)=x`. For any linear
readout row `d`, the blocks are `K_LL=I`, `K_DL=d`, `K_LD=d^T` and
`K_DD=sum_i d_i^2`. The first Moore–Penrose equation at the identity is
`I G I=I`, hence `G=I`; the identity also satisfies the other three
equations. Therefore

    Xi = dot(d,d) - dot(d,I d) = 0.

`HeightRegulator.heightSchurCollapse` now proves this identity for arbitrary
finite rows over a lawful `Lean.Grind.CommRing`, preserving the old integer
callers. `heightIdentityPenrose` checks all four transpose-based equations;
`heightIdentityPenroseUnique` proves uniqueness. On the intended real
Euclidean carrier, transpose is the adjoint. No general complex Hermitian
pseudoinverse or positivity theorem over arbitrary rings is asserted.

The empty tangent has energy zero (`heightZeroRank`). The rank-zero
regulator has empty determinant one. These are different operations and
different constants. The present Lean development has no real-analysis
library or constructed real instance; its generic algebra can be specialized
to any separately supplied lawful real scalar implementation.

## Deriving the height differential

For a supplied rank-two symmetric matrix and variation

    H = [[a,b],[b,c]], D = [[A,B],[B,C]], Delta = ac-b^2,

`determinantVariationPolynomial` derives the exact identity

    det(H+tD) = Delta + t(cA-2bB+aC) + t^2(AC-B^2).

At `Delta != 0`, `inverse2Correct` proves that the declared matrix
`[[c,-b],[-b,a]]/Delta` is an inverse. The normalized first-order row in
coordinates `(A,B,C)` is

    d_H = (c/Delta, -2b/Delta, a/Delta).

`logDetRow2Correct` proves both its value on the variation and equality
with `tr(H^-1 D)`. The factor two arises because both off-diagonal entries
vary with the single coordinate B. `heightDifferentialSchurCollapse`
returns this derived row to the exported full-source Schur calculation.
The nonzero determinant is explicit: totalized field division at zero does
not create an inverse. The normalized row algebra alone also holds at
zero, but then has no inverse or logarithmic-differential interpretation.

For positive definite real H, Delta is positive. The displayed polynomial
is positive for sufficiently small real t by continuity. Its derivative
at zero is `cA-2bB+aC`; the ordinary real chain rule gives
`d(log det)_H(D)=(cA-2bB+aC)/Delta`. This analytic interpretation is a
written proof, not a Lean differentiation theorem.

The same written argument gives the all-rank readout. For any invertible
real H, put `A=H^-1 D`. Determinant multiplicativity gives
`det(H+tD)=det(H) det(I+tA)`. In the permutation expansion of
`det(I+tA)`, the identity permutation contributes first-order coefficient
`sum_i A_ii`; every other permutation moves at least two indices and has
at least two factors of t. Thus the first-order coefficient is `tr A`.
When `det H>0`, continuity and the chain rule give
`d(log det)_H(D)=tr(H^-1 D)`. For symmetric H, half-vectorization of D
then gives diagonal row entries `(H^-1)_ii` and off-diagonal entries
`2(H^-1)_ij`. Substituting this row into the all-dimension identity
above proves the claimed Schur return. The determinant/differentiation
steps in this all-rank argument remain written rather than mechanized.

## Pairing and basis bridge

`heightPairing2 H` constructs the coordinate pairing

    p_H(x,y) = a x1 y1 + b(x1 y2+x2 y1) + c x2 y2.

Its symmetry, first-variable additivity and scalar law are proved directly;
symmetry supplies the corresponding second-variable laws. The concrete
`determinantFromPairing2` uses the four pairing values on the fixed basis.
`heightRegulatorMapRank2` shows that specializing the existing generic
map to this operation returns Delta. The point and lattice-marker inputs
remain unused metadata in that generic map: this coordinate specialization
does not construct a Mordell–Weil lattice or an intrinsic determinant line.

For basis columns `(u,w)` and `(v,z)`, `heightBasisChangeFromPairing`
derives the new Gram entries from evaluations of that same pairing.
`determinantBasisChange` proves

    det(A^T H A) = (uz-vw)^2 det H.

`unimodularRegulatorInvariant` derives equality of the coefficients when
`uz-vw` is one or negative one. This covers either orientation of an
integral unimodular change after embedding its entries in the scalar ring.
For arbitrary rank, the written determinant multiplicativity proof gives
`det(A^T H A)=det(A)^2 det H`, hence the same invariance for
`A in GL_r(Z)`. The all-rank determinant-line realization and arithmetic
regulator comparison remain supplied mathematical content, rather than
consequences of these rank-two coordinate theorems.

## Controls, scope and self-review

Regression uses the exact rational matrix `[[2,1],[1,3]]`, with
determinant five and row `(3/5,-2/5,2/5)`:

- Its pre-source energy is `17/25` and its full-source residual is zero.
- The purely off-diagonal variation has readout `-2/5`, unequal to
  `-1/5`; this rejects omission of the off-diagonal multiplicity.
- The singular matrix `[[1,1],[1,1]]` has determinant zero and its
  totalized inverse fails the identity-product test.
- A shear and a basis swap preserve determinant five. Scaling one basis
  column by two gives determinant twenty, rejecting invariance under
  arbitrary finite-index changes.

These are algebraic fixtures, not computed arithmetic heights of a curve.
In particular, the legacy scaled integer row for 389a1 remains an
approximation fixture; this repair does not identify its coefficients
with that curve's exact height matrix or certify the printed decimals.

Distinct self-review checked the vech ordering, off-diagonal factor two,
inverse domain, both basis orientations, finite-index exclusion, rank-zero
constants and transpose interpretation. The choice `C=I` refers to the
declared vech coordinates; it is not an assertion that this audit energy
is invariant under arbitrary changes of lattice basis. The zero residual
is the full-source identity calculation in the chosen coordinates. It
does not prove source indispensability for the scalar BSD projection,
nor replace the separately supplied height-to-BK comparison. These
boundaries preserve the accepted conditional endpoint.

Verification uses the regression build, full Lean build and live manifest
probe, static validators, unit tests and public-tree hygiene. The new
declarations have printed axiom closures; only ordinary Lean foundations
are allowed. The alignment categories remain unchanged because real
analysis, the exact arithmetic examples and all-rank determinant-line
construction have not been mechanized.
