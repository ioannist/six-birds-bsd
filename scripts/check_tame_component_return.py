#!/usr/bin/env python3
"""Recompute tame determinants, integral controls and a three-isogeny pair.

The offline branch derives integral and finite-field evidence. --gp additionally
reproduces the arithmetic Tate outputs and isogeny target. The component-group
theorem, Galois representations and Tate-module isomorphism are written proofs.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import subprocess

from check_local_unit_support import exact_valuation, shallow_branch, unit_at
from check_support_prime_data import count_points, count_points_quadratic, invariants


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "formalization" / "tame_component_return.json"


def multiply(a: list, b: list) -> list:
    return [[sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def determinant(a: list) -> int:
    return a[0][0]*a[1][1]-a[0][1]*a[1][0]


def check(gp: str | None) -> None:
    data = json.loads(FIXTURE.read_text())
    eye = [[1,0],[0,1]]
    returns = {}
    for order, matrix in data["companion_matrices"].items():
        order = int(order)
        assert determinant(matrix) == 1
        trace = matrix[0][0]+matrix[1][1]
        step = [[eye[i][j]-matrix[i][j] for j in range(2)] for i in range(2)]
        returns[order] = determinant(step)
        assert returns[order] == 2-trace
        power = eye
        for n in range(1, order+1):
            power = multiply(power, matrix)
            assert (power == eye) == (n == order)
        for n in range(1, 6):
            modulus = 2**n
            image = {(sum(step[0][j]*x[j] for j in range(2)) % modulus,
                      sum(step[1][j]*x[j] for j in range(2)) % modulus)
                     for x in ((a,b) for a in range(modulus) for b in range(modulus))}
            assert modulus**2 // len(image) == (2 if order == 4 else 1)
    assert returns == {6:1, 4:2, 3:3}
    assert multiply([[1,1],[-1,0]], data["companion_matrices"]["6"]) == eye
    shallow = json.loads((ROOT / "formalization/local_unit_support_models.json").read_text())
    cover = json.loads((ROOT / "formalization/additive_frobenius_descent.json").read_text())
    for label, model in shallow["models"].items():
        order = cover["models"][label]["tame_action_order"]
        assert order in {4,6}
        assert returns[order] == model["pari_localred"][3]
        assert unit_at(Fraction(returns[order]), 11)

    # Symbolic two-variable integer-polynomial identity for the actual map.
    def add(a: dict, b: dict) -> dict:
        keys = a.keys() | b.keys()
        return {k: a.get(k,0)+b.get(k,0) for k in keys if a.get(k,0)+b.get(k,0)}

    def scale(c: int, a: dict) -> dict:
        return {k:c*v for k,v in a.items() if c*v}

    def mul(a: dict, b: dict) -> dict:
        result = {}
        for (i,j), ai in a.items():
            for (k,l), bj in b.items():
                key = (i+k,j+l)
                result[key] = result.get(key,0)+ai*bj
        return {k:v for k,v in result.items() if v}

    def power(a: dict, n: int) -> dict:
        result = {(0,0):1}
        for _ in range(n):
            result = mul(result,a)
        return result

    def total(*polynomials: dict) -> dict:
        result = {}
        for polynomial in polynomials:
            result = add(result,polynomial)
        return result

    x, y, one = {(1,0):1}, {(0,1):1}, {(0,0):1}
    f = total(power(x,3),scale(121,x),scale(121,one))
    g = total(mul(y,power(x,3)),scale(-1331,power(x,2)),scale(-121,mul(x,y)),
              scale(-2662,x),scale(-242,y),scale(-1331,one))
    lhs = total(power(g,2),scale(11,mul(mul(f,g),x)),scale(11,mul(g,power(x,3))),
                scale(-1,power(f,3)),scale(605,mul(f,power(x,4))),scale(15488,power(x,6)))
    rhs = mul(power(total(power(x,3),scale(-121,x),scale(-242,one)),2),
              total(power(y,2),scale(11,mul(x,y)),scale(11,y),scale(-1,power(x,3))))
    assert lhs == rhs
    assert add(lhs,scale(-30976,power(x,6))) != rhs
    control = data["isogeny_control"]
    p = control["prime"]
    assert (p, control["degree"]) == (11,3) and p % 3 and 3 % p
    models = control["models"]
    # Controls of the written uniform digit lift, not evidence for a limit
    # by a finite profile alone. Every root is compatible with the previous.
    modulus, root = 11, 5
    for _ in range(8):
        assert root*root % modulus == 3 and root % 11 == 5
        defect = (root*root-3)//modulus
        digit = (-defect*pow(2*root,-1,11)) % 11
        next_root = root+modulus*digit
        assert next_root % modulus == root and 0 <= next_root < 11*modulus
        root,modulus = next_root,11*modulus
    assert root*root % modulus == 3
    assert not any(r*r % 11 == 2 for r in range(11))
    a1, _, a3, _, _ = models["source"]["a_invariants"]
    assert models["target"]["a_invariants"] == [a1,0,a3,-5*a1*a3,-a3*(a1**3+7*a3)]
    for label, model in models.items():
        equation = model["a_invariants"]
        c4, delta = invariants(equation)
        a1,a2,a3,a4,a6 = equation
        b2,b4,b6 = a1*a1+4*a2, a1*a3+2*a4, a3*a3+4*a6
        c6 = -b2**3+36*b2*b4-216*b6
        assert (c4,c6,delta) == (model["c4"],model["c6"],model["discriminant"])
        assert c4**3 % delta != 0  # Nonintegral j proves non-CM.
        assert exact_valuation(delta, p, 4) and shallow_branch(equation, p) is None
        assert c4 % p**2 == c6 % p**2 == 0
        ac, bc = Fraction(-c4,48*p**2), Fraction(-c6,864*p**2)
        assert -16*(4*ac**3*p**2+27*bc**2) == Fraction(delta,p**4)
        assert ac.denominator % p and bc.denominator % p
        residue_b = bc.numerator * pow(bc.denominator,-1,p) % p
        fiber = [0,0,0,0,residue_b]
        assert fiber == model["good_fiber"] and invariants(fiber)[1] % p != 0
        assert count_points(fiber,p) == count_points_quadratic(fiber,p) == 12
        # This is the numerical type-IV split test; arithmetic is independently
        # computed with GP. It is not a full Neron-model implementation.
        split = pow(residue_b, (p-1)//2, p) == 1
        c = 3 if split else 1
        assert model["pari_localred"] == [2,4,[1,0,0,0],c]
        if gp:
            expression = (
                f"e=ellinit({json.dumps(equation)});"
                f"print([e.c4,e.c6,e.disc,elllocalred(e,{p})]);quit\n"
            )
            result = subprocess.run([gp,"-q","-f"], input=expression, text=True,
                                    capture_output=True, check=True)
            assert not result.stderr.strip(), result.stderr
            assert json.loads(result.stdout) == [c4,c6,delta,model["pari_localred"]]
    if gp:
        expression = (
            "e=ellinit([11,0,11,0,0]);z=ellisogeny(e,x);"
            "print([z[1],z[2][1]==x^3+121*x+121,"
            "z[2][2]==y*x^3-1331*x^2-121*x*y-2662*x-242*y-1331,"
            "z[2][3]==x]);quit\n"
        )
        result = subprocess.run([gp,"-q","-f"], input=expression, text=True,
                                capture_output=True, check=True)
        assert not result.stderr.strip(), result.stderr
        assert json.loads(result.stdout) == [models["target"]["a_invariants"],1,1,1]
    print("tame component return: intrinsic determinants, finite coefficient controls, "
          "symbolic 3-isogeny and type-IV boundary pair passed"
          + ("; PARI arithmetic reproduced" if gp else "; arithmetic outputs not rerun"))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check the fixture (default)")
    parser.add_argument("--gp", help="optional PARI/GP executable")
    args = parser.parse_args()
    check(args.gp)


if __name__ == "__main__":
    main()
