#!/usr/bin/env python3
"""Reconstruct numerical support-prime rows from pinned curve models.

The recorded R4b flags come from the manuscript. Neither those flags nor
the basic Kobayashi scope screen certify an Iwasawa comparison theorem.
"""

from __future__ import annotations

import argparse
import csv
import io
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MODELS = ROOT / "formalization" / "support_prime_models.json"
ROWS = ROOT / "formalization" / "support_prime_numeric_rows.csv"


def prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, n) if d * d <= n)


def prime_divisors(n: int) -> set[int]:
    n = abs(n)
    result = set()
    d = 2
    while d * d <= n:
        if n % d == 0:
            result.add(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        result.add(n)
    return result


def invariants(a: list[int]) -> tuple[int, int]:
    a1, a2, a3, a4, a6 = a
    b2 = a1 * a1 + 4 * a2
    b4 = a1 * a3 + 2 * a4
    b6 = a3 * a3 + 4 * a6
    b8 = a1 * a1 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 * a3 - a4 * a4
    c4 = b2 * b2 - 24 * b4
    discriminant = -b2 * b2 * b8 - 8 * b4**3 - 27 * b6**2 + 9 * b2 * b4 * b6
    return c4, discriminant


def count_points(a: list[int], p: int) -> int:
    """Exhaustively count the affine equation, plus the point at infinity."""
    a1, a2, a3, a4, a6 = a
    return 1 + sum(
        (y * y + (a1 * x + a3) * y - x**3 - a2 * x * x - a4 * x - a6) % p == 0
        for x in range(p)
        for y in range(p)
    )


def count_points_quadratic(a: list[int], p: int) -> int:
    """Independently count roots by discriminants at odd primes."""
    if p == 2:
        a1, a2, a3, a4, a6 = a
        return 1 + sum(
            int((x + a2 * x + a4 * x + a6) % 2 == 0)
            + int((1 + a1 * x + a3 - x - a2 * x - a4 * x - a6) % 2 == 0)
            for x in (0, 1)
        )
    a1, a2, a3, a4, a6 = a
    total = 1
    for x in range(p):
        rhs = (x**3 + a2 * x * x + a4 * x + a6) % p
        delta = ((a1 * x + a3) ** 2 + 4 * rhs) % p
        total += 1 if delta == 0 else 2 if pow(delta, (p - 1) // 2, p) == 1 else 0
    return total


def build_rows(data: dict) -> list[dict]:
    result = []
    for label in data["atlas_curves"]:
        model = data["models"][label]
        c4, delta = invariants(model["a_invariants"])
        assert delta != 0, label
        assert prime_divisors(delta) == prime_divisors(model["conductor"]), label
        recorded_bad = set(data["paper_supplied_r4b_primes"][label])
        assert recorded_bad == prime_divisors(model["conductor"]), label
        primes = [p for p in range(2, 50) if prime(p)]
        # Complete this independently reconstructed grid with the one bad
        # prime outside the below-50 window. This is not the missing old atlas.
        primes += sorted(recorded_bad - set(primes))
        for p in primes:
            points = count_points(model["a_invariants"], p)
            assert points == count_points_quadratic(model["a_invariants"], p), (label, p)
            ap = p + 1 - points
            reduction = "good" if delta % p else "multiplicative" if c4 % p else "additive"
            assert (reduction == "good") == (model["conductor"] % p != 0), (label, p)
            if reduction == "good":
                assert ap * ap <= 4 * p, (label, p)
                local_type = "ordinary" if ap % p else "supersingular"
            else:
                assert ap in (-1, 0, 1), (label, p)
                local_type = "not_a_good_reduction_row"
            basic_scope = reduction == "good" and p % 2 == 1 and ap == 0
            result.append({
                "curve": label, "p": p, "below_50": int(p < 50),
                "point_count": points, "a_p": ap, "reduction": reduction,
                "good_reduction_type": local_type,
                "paper_r4b_flag": int(p in recorded_bad),
                "kobayashi_basic_scope": int(basic_scope),
                "supersingular_outside_kobayashi_basic_scope": int(
                    local_type == "supersingular" and not basic_scope
                ),
            })
    assert len(result) == 76
    assert len({(r["curve"], r["p"]) for r in result}) == 76
    assert sum(r["below_50"] for r in result) == 75
    assert sum(r["paper_r4b_flag"] for r in result) == 7
    assert sum(r["paper_r4b_flag"] * r["below_50"] for r in result) == 6
    return result


def render(rows: list[dict]) -> str:
    out = io.StringIO(newline="")
    writer = csv.DictWriter(out, fieldnames=list(rows[0]), lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    return out.getvalue()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rows = build_rows(json.loads(MODELS.read_text()))
    expected = render(rows)
    if args.write:
        ROWS.write_text(expected)
    elif not ROWS.exists() or ROWS.read_text() != expected:
        parser.exit(1, "support-prime numeric rows are missing or stale\n")
    gaps = [(r["curve"], r["p"], r["a_p"]) for r in rows
            if r["supersingular_outside_kobayashi_basic_scope"]]
    print(f"support-prime numeric {'write' if args.write else 'check'} passed: "
          f"{len(rows)} rows, two point-count methods agree; scope gaps={gaps}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
