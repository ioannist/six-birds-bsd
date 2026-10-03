#!/usr/bin/env python3
"""Check exact native tame/cyclotomic transition and source-audit inputs."""
from __future__ import annotations

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from math import comb, gcd
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / "formalization" / "signed_tame_transition.json"


def multiply(a: list[int], b: list[int]) -> list[int]:
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i+j] += x*y
    return result


def check(gp: str | None, source_pdf: str | None) -> None:
    data = json.loads(RECORD.read_text())
    native = json.loads((ROOT / "formalization" / data["curve_record"]).read_text())
    assert native["a_invariants"] == [0,0,0,385,1225]
    assert [row for row in native["cover_frobenius"] if row[0] == 7] == [
        [7,[0,0,0,6,0],8,0,1]]
    assert data["prime"] == 7 and data["quartic_parameter"] == -7
    assert data["inertia_order"] == 4
    assert data["cyclotomic_overlap_degree"] == data["residual_tame_degree"] == 2

    # Actual F_49 arithmetic; X^2+1 is irreducible over F_7.
    assert all((x*x+1)%7 for x in range(7))
    elements = [(a,b) for a in range(7) for b in range(7)]
    def mul49(x: tuple[int,int], y: tuple[int,int]) -> tuple[int,int]:
        return ((x[0]*y[0]-x[1]*y[1])%7,(x[0]*y[1]+x[1]*y[0])%7)
    assert mul49((2,2),(2,2)) == (0,1)
    assert mul49((0,1),(0,1)) == (6,0)
    squares = [mul49(y,y) for y in elements]
    fiber = data["unramified_good_fiber"]
    assert (fiber["A"],fiber["B"],fiber["cardinality"]) == (1,0,49)
    points = 1
    for x in elements:
        cube = mul49(mul49(x,x),x)
        points += squares.count(((cube[0]+x[0])%7,(cube[1]+x[1])%7))
    assert points == fiber["points"] == 64
    assert 50-points == fiber["trace"] == -14 and fiber["determinant"] == 49

    # Independent polynomial multiplication of the quadratic Gauss identity.
    lhs = multiply(data["gauss7_ascending"], data["gauss7_ascending"])
    lhs[0] += 7
    rhs = multiply(data["phi7_ascending"], data["gauss_quotient_ascending"])
    assert lhs == rhs
    assert data["phi7_ascending"] == [1]*7
    assert data["gauss7_ascending"] == [0,1,1,-1,1,-1,-1]

    transition = [0]*15
    for k in range(1,8):
        transition[2*k] = (-1)**(k+1)*comb(7,k)
    assert transition == data["transition_ascending"]
    unit = [Fraction(transition[2*k+2],7) for k in range(7)]
    assert unit == [Fraction(x) for x in data["unit_polynomial_in_square_coordinate"]]
    roots = [Fraction(1)]
    for k in range(1,len(unit)):
        roots.append((unit[k]-sum(roots[i]*roots[k-i] for i in range(1,k)))/2)
    assert roots == [Fraction(x) for x in data["square_root_in_square_coordinate"]]
    last = data["negative_coefficient_valuation"]
    assert roots[-1] == Fraction(last["numerator"],last["denominator"])
    assert last["degree"] == 13 and last["denominator"] == 7*1024
    assert gcd(last["numerator"],7) == gcd(1024,7) == 1
    assert Fraction(*last["v7_slope"])-1 == Fraction(*last["v7_coefficient"])

    # Controls only: the written argument proves these degree and valuation
    # statements at every level, rather than extrapolating from this sample.
    for n in range(1,9):
        assert gcd(4,6*7**(n-1)) == 2
        if n >= 2:
            assert Fraction(1,7**(n-1))-1 < 0

    if source_pdf:
        assert sha256(Path(source_pdf).read_bytes()).hexdigest() == data["candidate_source"]["sha256"]
    if gp:
        expression = (
            "z=Mod(x,polcyclo(7));g=z+z^2+z^4-z^3-z^5-z^6;print(lift(g^2));"
            "s=sqrt(1-3*x^2+5*x^4-5*x^6+3*x^8-x^10+x^12/7+O(x^14));"
            "print(vector(7,j,polcoeff(s,2*(j-1))));"
            "a=ffgen(Mod(1,7)*(x^2+1));e=ellinit([0,0,0,1,0],a);"
            "print([ellcard(e),ellap(e)]);quit\n"
        )
        result = subprocess.run([gp,"-q","-f"],input=expression,text=True,
                                capture_output=True,check=True)
        assert not result.stderr.strip(), result.stderr
        lines = result.stdout.strip().splitlines()
        assert len(lines) == 3 and int(lines[0]) == -7
        assert lines[1].startswith("[") and lines[1].endswith("]")
        assert [Fraction(x.strip()) for x in lines[1][1:-1].split(",")] == roots
        assert json.loads(lines[2]) == [64,-14]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true",help="check without modifying records")
    parser.add_argument("--gp",help="optional PARI executable for independent reproduction")
    parser.add_argument("--source-pdf",help="optional local candidate PDF for provenance hash")
    args = parser.parse_args()
    check(args.gp,args.source_pdf)
    print("signed tame transition: Gauss overlap, native polynomial, forced coefficients and scope controls passed"
          + ("; PARI reproduction passed" if args.gp else ""))


if __name__ == "__main__":
    main()
