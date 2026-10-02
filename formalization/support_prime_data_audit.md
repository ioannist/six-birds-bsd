# Support-prime numerical and applicability audit

The finite prime counter and the universal coverage split pair have been
repaired in Lean. The former now ignores zero, one, and composites; its
congruence theorem also ignores arbitrary changes outside the prime
truncation. The latter now has one completion satisfying all-prime coverage
and another failing it. This remains a formal coverage model, with no claim
that every completion is realized by an elliptic curve.

The original 76-row atlas referenced by the mathematical source record is
not present in the public repository. `support_prime_numeric_rows.csv` is
an independent numerical reconstruction, not a recovered copy of that atlas.
It contains the 75 pairs from five curves and the 15 primes below 50, plus
the missing bad-prime pair `(571a1,571)`.

The fixture `support_prime_models.json` records the five curve models and
the separate rank-two example using **Cremona labels**, with the source URL,
retrieval date, and digest of the downloaded
[Cremona curve data](https://raw.githubusercontent.com/JohnCremona/ecdata/master/allcurves/allcurves.00000-09999).
In this data, `571a1` has recorded rank zero and `389a1` has recorded rank
two. The fixture does not prove their ranks or Sha cardinalities.

`scripts/check_support_prime_data.py --check` reproduces every numerical
row without network access. It compares exhaustive point enumeration with
an independent quadratic-root count, including a direct characteristic-two
formula. It also checks the good-reduction Hasse bound, agreement between
the conductor and discriminant prime supports, and the elementary bad
reduction classification from the given minimal model. It records good,
multiplicative, or additive reduction; it does not run a full Tate algorithm
or reconstruct a Kodaira symbol.

The paper-supplied R4b flags are kept separate from these derived values.
Their lists contain the seven conductor primes across the five curves, six
of them below 50. The Lean `b50ResidualBelow50` now computes the recorded
counts from these flagged prime rows instead of returning five hardcoded
numbers. Verifying those counts does not prove that every remaining row
has a valid ordinary or signed arithmetic comparison.

## Five small-prime signed applicability obligations

The reconstructed data contains five good supersingular rows outside the
basic numerical scope of the cited Kobayashi plus/minus theory:

| Curve | Prime | Exact point count | a_p | Missing basic hypothesis |
| --- | ---: | ---: | ---: | --- |
| 11a1 | 2 | 5 | -2 | odd prime; a_p=0 |
| 37a1 | 2 | 5 | -2 | odd prime; a_p=0 |
| 37a1 | 3 | 7 | -3 | a_p=0 |
| 121b1 | 2 | 3 | 0 | odd prime |
| 571a1 | 2 | 3 | 0 | odd prime |

Kobayashi's hypotheses require an odd prime and zero Frobenius trace,
not just supersingularity. See the author's
[introduction, Main results](https://www.ms.u-tokyo.ac.jp/preprint/pdf/2002-4.pdf),
printed page 4. The CSV field `kobayashi_basic_scope` checks only these
necessary numerical conditions and good reduction. A positive value is
not a certificate for a main-conjecture equality or the full comparison
transport used in this repository.

This does not establish that the five rows cannot be covered by richer
inputs. Sprung's
[generalized signed construction](https://arxiv.org/pdf/0903.3419)
allows the nonzero-trace and prime-two cases in its local construction;
see Section 2 and Theorem 2.2. That uses sharp/flat Coleman maps and has
its own subsequent hypotheses. Restoring R4a coverage requires specifying
the appropriate signed objects, the particular comparison/control theorem,
and its applicability to each row. A local signed construction alone is
not the characteristic-ideal equality.

The options for the later manuscript phase are to supply these explicit
generalized signed bridges while retaining the recorded counts, or to
reclassify the affected rows as unresolved under the stated import scope.
No R4b classification has been silently changed, and no manuscript has
been edited.
