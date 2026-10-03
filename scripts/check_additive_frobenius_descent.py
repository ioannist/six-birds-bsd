#!/usr/bin/env python3
"""Recompute common-cover equations, good fibers and optional Hecke checks.

Offline checks use exact rational quotient-polynomial arithmetic and two
independent finite-field point counts. Arithmetic modular-symbol computations
are independently reproduced with --gp. This does not compute an eta value.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import gcd
from pathlib import Path
import subprocess

from check_support_prime_data import count_points, count_points_quadratic, invariants, prime


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "formalization" / "additive_frobenius_descent.json"


def check(gp: str | None) -> None:
    data = json.loads(FIXTURE.read_text())
    originals = json.loads((ROOT / "formalization" / data["arithmetic_input"]).read_text())
    p, degree = data["common_cover"]["prime"], data["common_cover"]["degree"]
    assert (p, degree) == (11, 12) and prime(p) and gcd(p, degree) == 1
    assert data["common_cover"]["residue_degree"] == 1
    assert set(data["models"]) == {"121a1", "121b1"}

    def monomial(k: int, a: Fraction = Fraction(1)) -> tuple[Fraction, ...]:
        return tuple(a * p**(k // degree) if i == k % degree else Fraction(0)
                     for i in range(degree))

    def mul(a: tuple, b: tuple) -> tuple[Fraction, ...]:
        result = [Fraction(0)] * degree
        for i, ai in enumerate(a):
            for j, bj in enumerate(b):
                result[(i + j) % degree] += ai * bj * p**((i + j) // degree)
        return tuple(result)

    def terms(rows: list[list[int]]) -> tuple[Fraction, ...]:
        result = [Fraction(0)] * degree
        for k, n, d in rows:
            assert 0 <= k < degree and d > 0 and d % p != 0
            result[k] += Fraction(n, d)
        return tuple(result)

    def residue(a: tuple[Fraction, ...]) -> int:
        assert all(x.denominator % p for x in a)
        return a[0].numerator * pow(a[0].denominator, -1, p) % p

    for label, model in data["models"].items():
        original = originals["models"][label]
        c4, delta = invariants(original["a_invariants"])
        a1, a2, a3, a4, a6 = original["a_invariants"]
        b2, b4, b6 = a1*a1+4*a2, a1*a3+2*a4, a3*a3+4*a6
        c6 = -b2**3 + 36*b2*b4 - 216*b6
        assert (c4, c6, delta) == (original["c4"], original["c6"], original["discriminant"])
        assert c4**3 - c6**2 == 1728 * delta
        a, b = terms(model["cover_A_terms"]), terms(model["cover_B_terms"])
        s = model["scale_power"]
        assert s > 0
        weights = [(-2*s) % degree, (-3*s) % degree]
        assert weights == model["tame_coordinate_weights_mod_12"]
        assert (weights[0] - weights[1]) % degree == s
        order = next(n for n in range(1, degree+1)
                     if all(n*w % degree == 0 for w in weights))
        assert order == model["tame_action_order"]
        assert mul(monomial(4*s), a) == monomial(0, Fraction(-c4, 48))
        assert mul(monomial(6*s), b) == monomial(0, Fraction(-c6, 864))
        a3, b2 = mul(mul(a, a), a), mul(b, b)
        transformed_delta = tuple(-16 * (4*x + 27*y) for x, y in zip(a3, b2))
        assert transformed_delta == monomial(0, Fraction(-1))
        assert mul(monomial(12*s), transformed_delta) == monomial(0, Fraction(delta))
        fiber = [0, 0, 0, residue(a), residue(b)]
        assert fiber == model["good_fiber"]
        assert invariants(fiber)[1] % p == p-1
        count = count_points(fiber, p)
        assert count == count_points_quadratic(fiber, p) == model["point_count"]
        assert [p+1-count, p] == model["frobenius_trace_determinant"]
        assert model["original_U11"] == 0
        assert model["original_plus_eigenline_dimension"] == 1
        # Weight-two Sturm bound at level 11^2: index 11*(11+1)=132.
        assert model["qexpansion_bound_checked"] == 2 * p * (p+1) // 12 == 22

    assert data["models"]["121a1"]["frobenius_trace_determinant"] == \
        data["models"]["121b1"]["frobenius_trace_determinant"]
    assert originals["models"]["121a1"]["pari_localred"][3] == 1
    assert originals["models"]["121b1"]["pari_localred"][3] == 2
    # Reject a nonsingular fiber with a different point count.
    control = [0, 0, 0, 1, 1]
    assert invariants(control)[1] % p != 0
    assert count_points(control, p) == count_points_quadratic(control, p) != 12
    if gp:
        labels = list(data["models"])
        equations = [originals["models"][label]["a_invariants"] for label in labels]
        fibers = [data["models"][label]["good_fiber"] for label in labels]
        expression = (
            f"curves={json.dumps(equations)};fibers={json.dumps(fibers)};"
            "m=msinit(121,2,1);"
            "for(i=1,2,e=ellinit(curves[i]);"
            "h=msfromhecke(m,vector(3,j,[prime(j),ellap(e,prime(j))]));"
            "print([e[1..5],e.c4,e.c6,e.disc,ellglobalred(e)[1],"
            "elllocalred(e,11),ellap(e,11),#h,mshecke(m,11)*h==0*h,"
            "msqexpansion(m,h[,1],22)==ellan(e,22),"
            "ellcard(ellinit(fibers[i],11)),ellap(ellinit(fibers[i],11),11)]));\nquit\n"
        )
        result = subprocess.run([gp, "-q", "-f", "-s", "128000000"],
                                input=expression, text=True, capture_output=True, check=True)
        assert not result.stderr.strip(), result.stderr
        rows = [json.loads(row) for row in result.stdout.splitlines() if row.strip()]
        assert len(rows) == 2, result.stdout
        for label, row in zip(labels, rows):
            original = originals["models"][label]
            assert row == [original["a_invariants"], original["c4"], original["c6"],
                           original["discriminant"], 121, original["pari_localred"],
                           0, 1, 1, 1, 12, 0], (label, row)
    print("additive Frobenius descent: common-cover identities, unit discriminants, "
          "dual point counts, exact tame-character orders and false control passed"
          + ("; PARI U11 eigenlines and 22 coefficients reproduced" if gp else
             "; modular-symbol arithmetic not rerun"))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check the fixture (default)")
    parser.add_argument("--gp", help="optional PARI/GP executable for arithmetic reproduction")
    args = parser.parse_args()
    check(args.gp)


if __name__ == "__main__":
    main()
