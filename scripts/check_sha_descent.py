#!/usr/bin/env python3
"""Check 571a1 quartic descent data; optionally rerun certified PARI descent.

Offline checks do not prove completeness of the Selmer basis or the pairing
rank. These are recomputed only by the optional external PARI/GP step.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import subprocess

from check_support_prime_data import invariants, prime_divisors


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "formalization" / "sha_descent_571a1.json"


def add(a: list[int], b: list[int]) -> list[int]:
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
            for i in range(max(len(a), len(b)))]


def scale(a: list[int], c: int) -> list[int]:
    return [c * x for x in a]


def mul(a: list[int], b: list[int]) -> list[int]:
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return result


def evaluate(coeff: list[int], x: Fraction | int) -> Fraction | int:
    value = 0
    for c in coeff:
        value = value * x + c
    return value


def check(gp: str | None) -> None:
    data = json.loads(FIXTURE.read_text())
    models = json.loads((ROOT / "formalization/support_prime_models.json").read_text())
    a = models["models"][data["curve"]]["a_invariants"]
    assert a == [0, -1, 1, -929, -10595]
    c4, delta = invariants(a)
    assert (c4, delta) == (44608, -571)
    for cover in data["quartics"]:
        aa, b, c, d, e = cover["coefficients_descending"]
        i = 12*aa*e - 3*b*d + c*c
        j = 72*aa*c*e + 9*b*c*d - 27*aa*d*d - 27*b*b*e - 2*c**3
        assert (i, j) == (data["quartic_I"], data["quartic_J"])
        assert (4*i**3 - j*j) == 27*data["ordinary_quartic_discriminant"]
        assert data["ordinary_quartic_discriminant"] == 256*delta
        assert data["fisher_binary_discriminant"] == 16*data["ordinary_quartic_discriminant"]
        assert prime_divisors(data["ordinary_quartic_discriminant"]) == {2, 571}
        q = list(reversed(cover["coefficients_descending"]))
        n = list(reversed(cover["x_numerator_descending"]))
        yn = list(reversed(cover["twice_shifted_y_numerator_descending"]))
        rhs = add(add(scale(mul(mul(n, n), n), 4), scale(mul(mul(n, n), q), -4)),
                  add(scale(mul(n, mul(q, q)), -3716), scale(mul(mul(q, q), q), -42379)))
        assert all(x == 0 for x in add(mul(yn, yn), scale(rhs, -1)))
        real_x = Fraction(*cover["real_x"])
        value = evaluate(cover["coefficients_descending"], real_x)
        assert value == Fraction(*cover["real_value"]) and value > 0
        assert evaluate(cover["coefficients_descending"], cover["two_adic_x"]) % 8 == 1
        xp, yp = cover["odd_bad_point"]
        assert (yp*yp - evaluate(cover["coefficients_descending"], xp)) % 571 == 0
        assert (2*yp) % 571 != 0
    # Pairing-rank and Selmer-rank deductions use the certified arithmetic
    # algorithm and its stated interpretation, not these metadata checks.
    r, upper, s, points = data["ellrank_output"]
    assert (r, upper, s, points) == (0, 0, 2, [])
    assert data["rational_torsion_order"] == 1
    assert data["bnf_certification"] == [1]
    if gp:
        expression = (
            f"setrand({data['random_seed']});e=ellinit({json.dumps(a)});"
            "rk=ellrankinit(e);bc=vector(#rk[3],i,bnfcertify(rk[3][i]));"
            "c=ell2cover(rk);"
            "print([bc,elltors(e)[1],ellrank(rk),vector(#c,i,Vec(c[i][1])),"
            "vector(#c,i,poldisc(c[i][1]))]);quit\n"
        )
        result = subprocess.run([gp, "-q", "-f"], input=expression,
                                text=True, capture_output=True, check=True)
        assert not result.stderr.strip(), result.stderr
        assert json.loads(result.stdout) == [
            data["bnf_certification"], data["rational_torsion_order"],
            data["ellrank_output"],
            [q["coefficients_descending"] for q in data["quartics"]],
            [data["ordinary_quartic_discriminant"]] * len(data["quartics"]),
        ], result.stdout
    print("Sha descent: exact quartic maps, invariants and local inputs passed; "
          + ("certified PARI arithmetic descent reproduced" if gp else
             "arithmetic completeness and pairing rank remain external"))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check the committed fixture (default)")
    parser.add_argument("--gp", help="optional PARI/GP executable for certified arithmetic reproduction")
    args = parser.parse_args()
    check(args.gp)


if __name__ == "__main__":
    main()
