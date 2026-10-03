#!/usr/bin/env python3
"""Check a native inertia product; --gp independently repeats Tate and rank outputs.

Offline checks cover equations, support, cover scaling and determinant algebra.
They do not implement Neron models, Galois cohomology or arithmetic descent.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import prod
from pathlib import Path
import subprocess

from check_local_unit_support import exact_valuation, shallow_branch, unit_at
from check_support_prime_data import count_points, count_points_quadratic, invariants, prime, prime_divisors
from check_tame_component_return import determinant

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "formalization/global_tame_product.json"


def check(gp: str | None) -> None:
    data = json.loads(FIXTURE.read_text())
    a = data["a_invariants"]
    assert a == [0,0,0,385,1225]
    c4, delta = invariants(a)
    c6 = -864*a[4]
    assert (c4,c6,delta) == (data["c4"],data["c6"],data["discriminant"])
    assert c4**3-c6**2 == 1728*delta
    j = Fraction(c4**3,delta)
    assert j == Fraction(*data["j"]) and j.denominator != 1
    factors = data["discriminant_factorization"]
    assert all(prime(p) for p,k in factors)
    assert prod(p**k for p,k in factors) == abs(delta)
    assert prime_divisors(delta) == {p for p,k in factors}
    rows = data["local_outputs"]
    assert len({row[0] for row in rows}) == len(rows)
    assert {row[0] for row in rows} == prime_divisors(delta)
    assert prod(p**f for p,f,local in rows) == data["conductor"]
    assert all(f == local[0] and local[2] == [1,0,0,0] for p,f,local in rows)
    native = []
    shallow_primes = set()
    for cover in data["tame_covers"]:
        p, e = cover["prime"], cover["ramification_degree"]
        assert prime(p) and p >= 5 and e == 4 and p % e
        assert p not in shallow_primes
        shallow_primes.add(p)
        A, B = cover["A_over_p"], cover["B_over_p_squared"]
        assert a[3] == p*A and a[4] == p*p*B
        assert exact_valuation(delta,p,3) and A % p != 0
        # pi^4=p, u=pi: A'=A, B'=B*pi^2, Delta'=Delta/p^3.
        assert -16*(4*A**3+27*B**2*p) == delta//p**3
        assert shallow_branch(a,p) == (2,3,2)
        matrix = cover["inertia_matrix"]
        assert matrix == [[0,-1],[1,0]]
        native.append(determinant([[1-matrix[0][0],-matrix[0][1]],
                                   [-matrix[1][0],1-matrix[1][1]]]))
    assert shallow_primes == {5,7} and native == [2,2]
    assert all(local[3] == 1 for p,f,local in rows if p not in shallow_primes)
    total = prod(native)
    assert total == prod(local[3] for p,f,local in rows) == data["finite_tamagawa_product"] == 4
    assert all(prod(native[:i]+native[i+1:]) != total for i in range(len(native)))
    assert shallow_branch(a,2) is None and shallow_branch(a,9) is None
    scaled = [value*5**weight for value,weight in zip(a,[1,2,3,4,6])]
    assert shallow_branch(scaled,5) is None
    assert all(unit_at(Fraction(total),p) for p in shallow_primes)
    assert not unit_at(Fraction(total),2) and prime_divisors(total) == {2}
    for point in data["rank_points"]:
        x,y = (Fraction(*coord) for coord in point)
        assert y*y == x**3+a[3]*x+a[4]
    assert data["mordell_weil_rank_bounds"] == [2,2]
    # Cover Frobenius is independent of the native inertia determinant.
    fiber_outputs = data["cover_frobenius"]
    assert len(fiber_outputs) == 2
    for p,fiber,points,trace,supersingular in fiber_outputs:
        assert fiber == [0,0,0,(a[3]//p) % p,0]
        assert invariants(fiber)[1] % p != 0
        assert count_points(fiber,p) == count_points_quadratic(fiber,p) == points
        assert trace == p+1-points
        # Compute the Hasse coefficient independently, not via a point count.
        coefficients = [1]
        cubic = [0,fiber[3],0,1]
        for _ in range((p-1)//2):
            product = [0]*(len(coefficients)+3)
            for left_index,left in enumerate(coefficients):
                for right_index,right in enumerate(cubic):
                    product[left_index+right_index] += left*right
            coefficients = product
        hasse = coefficients[p-1] % p
        assert supersingular == int(hasse == 0) == int(trace % p == 0)
    assert [(p,trace) for p,fiber,points,trace,ss in fiber_outputs] == [(5,4),(7,0)]
    refinement = data["five_adic_refinement"]
    roots = []
    modulus,root = 5,refinement["square_root_residue"]
    for n in range(1,11):
        assert root*root % modulus == modulus-1 and root % 5 == 2
        assert 0 <= root < modulus
        roots.append(root)
        unit_beta,other_beta = (2+root) % modulus,(2-root) % modulus
        assert unit_beta % 5 == 4 and other_beta % 5 == 0
        assert (unit_beta**2-4*unit_beta+5) % modulus == 0
        assert (other_beta**2-4*other_beta+5) % modulus == 0
        if n >= 2:
            assert exact_valuation(other_beta,5,1)
            assert (unit_beta**2+5) % modulus != 0
            assert (other_beta**2+5) % modulus != 0
        defect = (root*root+1)//modulus
        digit = (-4*defect) % 5
        next_root = root+modulus*digit
        assert next_root % modulus == root
        root,modulus = next_root,5*modulus
    assert roots[:6] == refinement["initial_square_roots"]
    for n in range(1,9):
        modulus,root = 5**n,roots[n-1]
        # Division by 25 costs two coefficient levels. Retaining this shift
        # prevents an incorrect inversion based on a truncated root alone.
        lifted = roots[n+1]
        assert (3-4*lifted) % 25 == 0
        assert ((3-4*lifted)//25) % modulus == pow((2+root) % modulus,-2,modulus)
    prev,trace = 2,4
    trace_controls = []
    for _ in range(20):
        assert trace % 5 in {1,4}
        trace_controls.append(trace)
        prev,trace = trace,4*trace-5*prev
    assert trace_controls[:8] == refinement["positive_degree_trace_controls"]
    if gp:
        expression = (
            f"setrand({data['pari_seed']});e=ellinit({json.dumps(a)});"
            "g=ellglobalred(e);r=ellrank(e);"
            "print([e.c4,e.c6,e.disc,numerator(e.j),denominator(e.j),"
            "g[1],g[2],g[3],r[1],r[2],r[3]]);"
            "for(i=1,matsize(g[4])[1],p=g[4][i,1];"
            "print([p,g[4][i,2],elllocalred(e,p)]));quit\n"
        )
        result = subprocess.run([gp,"-q","-f"], input=expression, text=True,
                                capture_output=True, check=True)
        assert not result.stderr.strip(), result.stderr
        actual = [json.loads(line) for line in result.stdout.splitlines()]
        expected = [c4,c6,delta,j.numerator,j.denominator,data["conductor"],
                    data["minimal_model_change"],total,
                    *data["mordell_weil_rank_bounds"],data["ellrank_third_output"]]
        assert actual == [expected,*rows], actual
        expression = ""
        for p,fiber,points,trace,ss in fiber_outputs:
            expression += (f"e=ellinit({json.dumps(fiber)},{p});"
                           f"print([{p},ellcard(e),ellap(e),ellissupersingular(e)]);")
        result = subprocess.run([gp,"-q","-f"], input=expression+"quit\n", text=True,
                                capture_output=True, check=True)
        assert not result.stderr.strip(), result.stderr
        assert [json.loads(line) for line in result.stdout.splitlines()] == [
            [p,points,trace,ss] for p,fiber,points,trace,ss in fiber_outputs]
    print("global tame product: equation support, native factors, ordinary/supersingular fibers, "
          "compatible root and refinement controls passed"
          + ("; PARI Tate/rank outputs reproduced" if gp else "; arithmetic imports not rerun"))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check fixture (default)")
    parser.add_argument("--gp", help="optional PARI/GP executable")
    args = parser.parse_args()
    check(args.gp)


if __name__ == "__main__":
    main()
