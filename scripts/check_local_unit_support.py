#!/usr/bin/env python3
"""Check equation-derived local-unit witnesses; optionally rerun PARI/GP.

The offline branch checks numerical Tate inputs, not Neron component groups.
PARI supplies an independent arithmetic computation when --gp is provided.
Recorded analytic BSD columns are retained only as source provenance.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import subprocess

from check_support_prime_data import invariants, prime, prime_divisors


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "formalization" / "local_unit_support_models.json"


def exact_valuation(z: int, p: int, k: int) -> bool:
    return z % p**k == 0 and z % p**(k + 1) != 0


def shallow_branch(a: list[int], p: int) -> tuple[int, int, int] | None:
    c4, delta = invariants(a)
    if not prime(p) or p < 5 or c4 % p:
        return None
    if exact_valuation(delta, p, 2):
        return (2, 2, 1)
    if exact_valuation(delta, p, 3):
        return (2, 3, 2)
    return None


def unit_at(r: Fraction, p: int) -> bool:
    return r.numerator % p != 0 and r.denominator % p != 0


def check(gp: str | None) -> None:
    data = json.loads(FIXTURE.read_text())
    assert set(data["models"]) == {"121a1", "121b1"}
    for label, m in data["models"].items():
        a = m["a_invariants"]
        assert len(a) == 5 and all(type(x) is int for x in a)
        row = m["allcurves_row"].split()
        assert row[0] + row[1] + row[2] == label
        assert json.loads(row[3]) == a
        assert int(row[0]) == m["conductor"]
        bsd_row = m["allbsd_row"].split()
        assert row[:6] == bsd_row[:6]
        assert int(bsd_row[6]) == m["finite_tamagawa_product"]
        c4, delta = invariants(a)
        a1, a2, a3, a4, a6 = a
        b2, b4, b6 = a1 * a1 + 4 * a2, a1 * a3 + 2 * a4, a3 * a3 + 4 * a6
        c6 = -b2**3 + 36 * b2 * b4 - 216 * b6
        assert (c4, c6, delta) == (m["c4"], m["c6"], m["discriminant"])
        assert c4**3 - c6**2 == 1728 * delta
        p = m["prime"]
        assert prime_divisors(delta) == prime_divisors(m["conductor"]) == {p}
        f, kod, change, c = m["pari_localred"]
        assert change == [1, 0, 0, 0]
        assert shallow_branch(a, p) == (f, kod, c)
        assert p**f == m["conductor"] and c == m["finite_tamagawa_product"]
        assert prime_divisors(c) - {p} == ({2} if c == 2 else set())
        assert unit_at(Fraction(c), p)
        assert (1 if unit_at(Fraction(c), 2) else 2) == c
        # The selector must reject nonminimal scaling, good reduction,
        # unsupported small primes, and composite indices.
        scaled = [x * p**weight for x, weight in zip(a, [1, 2, 3, 4, 6])]
        assert shallow_branch(scaled, p) is None
        assert shallow_branch(a, 5) is None
        assert shallow_branch(a, 2) is None
        assert shallow_branch(a, 9) is None
        assert not exact_valuation(0, p, 2)
        if gp:
            expression = (
                f"e=ellinit({json.dumps(a)});"
                f"print([e.c4,e.c6,e.disc,elllocalred(e,{p}),"
                "ellglobalred(e)[1],ellglobalred(e)[3]]);quit\n"
            )
            result = subprocess.run([gp, "-q", "-f"], input=expression,
                                    text=True, capture_output=True, check=True)
            assert not result.stderr.strip(), result.stderr
            assert json.loads(result.stdout) == [
                c4, c6, delta, m["pari_localred"],
                m["conductor"], m["finite_tamagawa_product"],
            ], (label, result.stdout)
    assert unit_at(Fraction(1, 2), 11) and Fraction(1, 2) * 2 == 1
    assert unit_at(Fraction(2), 11) and not unit_at(Fraction(2), 2)
    assert unit_at(Fraction(2), 2) == unit_at(Fraction(4), 2)
    print("local-unit support: 2 equation-derived witnesses and negative controls passed"
          + ("; PARI arithmetic outputs reproduced" if gp else "; numerical branch only"))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check the committed fixture (default)")
    parser.add_argument("--gp", help="optional PARI/GP executable for arithmetic reproduction")
    args = parser.parse_args()
    check(args.gp)


if __name__ == "__main__":
    main()
