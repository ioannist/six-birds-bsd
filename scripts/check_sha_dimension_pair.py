#!/usr/bin/env python3
"""Check the arithmetic Sha dimension pair; optionally reproduce PARI evidence.

Offline checks validate integral invariants and consistency of the recorded
inputs. Only --gp recomputes descent completeness, pairing ranks and exact
modular-symbol calculations. Neither mode implements the arithmetic theorems
or proves the 1309a1 two-primary order is exactly sixteen.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess

from check_support_prime_data import invariants, prime_divisors


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "formalization" / "sha_dimension_arithmetic_pair.json"


def c6(a: list[int]) -> int:
    a1, a2, a3, a4, a6 = a
    b2 = a1*a1 + 4*a2
    b4 = a1*a3 + 2*a4
    b6 = a3*a3 + 4*a6
    return -b2**3 + 36*b2*b4 - 216*b6


def check(gp: str | None) -> None:
    data = json.loads(FIXTURE.read_text())
    first = data["models"]["571a1"]
    second = data["models"]["1309a1"]
    prior = json.loads((ROOT / "formalization" / first["quartic_fixture"]).read_text())
    prior_model = json.loads((ROOT / "formalization/support_prime_models.json").read_text())
    assert first["a_invariants"] == prior_model["models"]["571a1"]["a_invariants"]
    for key in ("ellrank_output", "rational_torsion_order", "bnf_certification"):
        assert first[key] == prior[key]
    assert second["a_invariants"] == [0, 0, 1, -406957, -99924251]
    for model in (first, second):
        a = model["a_invariants"]
        c4, delta = invariants(a)
        assert (c4, c6(a), delta) == (model["c4"], model["c6"], model["discriminant"])
        assert delta != 0
        assert model["bnf_certification"] == [1]
        assert model["rational_torsion_order"] == 1
        # C = T + rank_upper + s is the documented descent contract.
        assert model["number_of_selmer_covers"] == sum(model["ellrank_output"][1:3]) == 2
        parts = model["allcurves_row"].split()
        assert json.loads(parts[3]) == a
        assert int(parts[0]) == model["conductor"]
    assert first["ellrank_output"] == [0, 0, 2, []]
    assert second["ellrank_output"] == [0, 2, 0, []]
    for aa, b, c, d, e in second["quartic_coefficients_descending"]:
        i = 12*aa*e - 3*b*d + c*c
        j = 72*aa*c*e + 9*b*c*d - 27*aa*d*d - 27*b*b*e - 2*c**3
        assert i == second["c4"] and j == 2*second["c6"]
        assert 4*i**3 - j*j == 27*256*second["discriminant"]
    assert second["c4"]**3 % second["discriminant"] != 0  # nonintegral j; excludes CM
    symbol = second["modular_symbol"]
    assert (symbol["sign"], symbol["level"], symbol["weight"]) == (1, 1309, 2)
    assert symbol["path"] == ["oo", 0] and symbol["divisor"] == "[0]-[oo]"
    assert symbol["value"] == 64 and symbol["reverse_path_value"] == -64
    # Squarefree level: [SL_2(Z):Gamma_0(N)] = product(p+1).
    primes = prime_divisors(second["conductor"])
    assert primes == {7, 11, 17}
    index = 1
    for p in primes:
        index *= p + 1
    assert symbol["gamma0_index"] == index == 1728
    assert symbol["sturm_bound"] == symbol["weight"] * index // 12 == 288
    assert symbol["msissymbol"] == symbol["generator_relations_pass"] == 1
    assert symbol["q_expansion_matches_curve_through_bound"] == 1
    if gp:
        for model in (first, second):
            a = json.dumps(model["a_invariants"])
            expression = (
                f"setrand({data['random_seed']});e=ellinit({a});rk=ellrankinit(e);"
                "bc=vector(#rk[3],i,bnfcertify(rk[3][i]));cv=ell2cover(rk);"
                "print([bc,elltors(e)[1],ellrank(rk),#cv,e.c4,e.c6,e.disc,"
                "ellglobalred(e)[1],vector(#cv,i,Vec(cv[i][1]))]);quit\n"
            )
            covers = (second["quartic_coefficients_descending"] if model is second else
                      [q["coefficients_descending"] for q in prior["quartics"]])
            expected = [model["bnf_certification"], model["rational_torsion_order"],
                        model["ellrank_output"], model["number_of_selmer_covers"],
                        model["c4"], model["c6"], model["discriminant"],
                        model["conductor"], covers]
            assert run_gp(gp, data["gp_stack_bytes"], expression) == expected
        expression = (
            f"e=ellinit({json.dumps(second['a_invariants'])});[m,sy]=msfromell(e,1);"
            f"q=msqexpansion(m,sy,{symbol['sturm_bound']});"
            "print([msissymbol(m,sy),msissymbol(m,mseval(m,sy)),"
            "mseval(m,sy,[oo,0]),mseval(m,sy,[0,oo]),msgetlevel(m),msgetweight(m),"
            f"#q,q==ellan(e,{symbol['sturm_bound']}),vector(20,i,q[i])]);quit\n"
        )
        assert run_gp(gp, data["gp_stack_bytes"], expression) == [
            1, 1, 64, -64, 1309, 2, 288, 1, symbol["first_twenty_coefficients"]]
    print("Arithmetic Sha pair: exact model and quartic invariants passed; "
          + ("certified descents and 1309a1 modular symbol reproduced" if gp else
             "descent and modular-symbol correctness remain external"))


def run_gp(gp: str, stack: int, expression: str) -> list:
    result = subprocess.run([gp, "-s", str(stack), "-q", "-f"], input=expression,
                            text=True, capture_output=True, check=True, timeout=60)
    assert not result.stderr.strip(), result.stderr
    return json.loads(result.stdout)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check the committed fixture (default)")
    parser.add_argument("--gp", help="optional PARI/GP executable for arithmetic reproduction")
    args = parser.parse_args()
    check(args.gp)


if __name__ == "__main__":
    main()
