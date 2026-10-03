#!/usr/bin/env python3
"""Check eight-descent applicability data and optionally recompute with PARI.

The actual eight-descent is imported from Miller's published proof; neither
offline validation nor --gp reruns it. --gp verifies model minimality, the
isogeny-class size, local factors, and the new partner's two-descent. Exact
Hecke eigensymbols independently check the period ratios: their scale is
derived from the optimal integral lattice and the semistable Manin theorem,
not from msfromell's period calibration. These arithmetic imports are not
Lean proofs; the generic finite group and pairing returns are Lean proofs.
"""

from __future__ import annotations

import argparse
import json
from math import prod
from pathlib import Path

from check_sha_dimension_pair import c6, run_gp
from check_support_prime_data import invariants, prime_divisors


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "formalization/sha_four_normalization.json"


def check_exact_period_normalization(data: dict, prior: dict, gp: str | None) -> None:
    """Check the finite inputs to the integral-lattice argument in the audit.

    For these optimal, squarefree-conductor curves with trivial rational
    torsion and negative discriminant, real projections of all cusp-path
    integrals generate (Omega^+/2) Z. The primitive integral plus eigensymbol
    therefore has twice the absolute period-normalized values. Establishing
    that lattice identification uses the cited arithmetic theorems.
    """
    normalization = data["exact_period_normalization"]
    assert set(normalization["curves"]) == {"571a1", "1309a1", "2045b1"}
    assert normalization["primitive_to_absolute_period_ratio_divisor"] == 2
    for label, record in normalization["curves"].items():
        model = prior["models"][label] if label != "2045b1" else data["models"][label]
        a = model["a_invariants"]
        _, delta = invariants(a)
        level = model["conductor"]
        assert delta < 0 and model["rational_torsion_order"] == 1
        assert level == record["level"] and level == prod(prime_divisors(level))
        assert record["rational_isogeny_class_size"] == 1
        assert record["eigenspace_dimension"] == record["generator_value_content"] == 1
        assert record["primitive_path_value_absolute"] == 2 * record["absolute_period_ratio"]
        index = prod(p + 1 for p in prime_divisors(level))
        assert record["sturm_bound"] == 2 * index // 12
        if gp:
            expression = (
                f"e=ellinit({json.dumps(a)});ps=[2,3,5];"
                f"m=msinit({level},2,1);hp=vector(#ps,i,[ps[i],ellap(e,ps[i])]);"
                "h=msfromhecke(m,hp);if(#h!=1,error(\"eigenspace dimension\"));"
                "v=h[,1];pa=mspathgens(m)[1];"
                "ev=vector(#pa,i,mseval(m,v,pa[i]));v=v/content(ev);"
                "ev=vector(#pa,i,mseval(m,v,pa[i]));"
                f"q=msqexpansion(m,v,{record['sturm_bound']});"
                "print([ellminimalmodel(e)[1..5],#ellisomat(e)[1],elltors(e)[1],"
                "ellglobalred(e)[1],hp,#h,#v,#pa,content(ev),"
                "msissymbol(m,ev),msstar(m)*v==v,abs(mseval(m,v,[oo,0])),"
                f"q==ellan(e,{record['sturm_bound']})]);quit\n"
            )
            assert run_gp(gp, data["gp_stack_bytes"], expression) == [
                a, 1, 1, level, record["hecke_prime_eigenvalues"], 1,
                record["coordinate_column_length"], record["path_generator_count"],
                1, 1, 1, record["primitive_path_value_absolute"], 1]


def check(gp: str | None) -> None:
    data = json.loads(FIXTURE.read_text())
    prior = json.loads((ROOT / "formalization/sha_dimension_arithmetic_pair.json").read_text())
    model1309 = prior["models"]["1309a1"]
    assert set(data["models"]) == {"1309a1", "2045b1"}
    assert data["sources"]["miller_pdf_sha256"] == (
        "52cbe68361e6eb07f94e13197a88eb5295c3f92e339a65d1488324d5489055ae")
    assert data["sources"]["manin_pdf_sha256"] == (
        "61cde659ac3089225539b58bfdf0082cb63ce39d1ca8bd7f8952b424e7132b6c")
    check_exact_period_normalization(data, prior, gp)
    for label, model in data["models"].items():
        a = model["a_invariants"]
        c4, delta = invariants(a)
        reference = model1309 if label == "1309a1" else model
        assert (c4, c6(a), delta) == (reference["c4"], reference["c6"], reference["discriminant"])
        assert a == model["minimal_a_invariants"]
        assert delta < 0 and model["real_components"] == 1
        assert c4**3 % delta != 0  # nonintegral j, so ellisomat's non-CM algorithm applies
        assert model["conductor"] < 5000
        assert model["rational_isogeny_class_size"] == 1
        assert prime_divisors(delta) == set(model["bad_primes"])
        product = 1
        for p, exponent, red in zip(model["bad_primes"], model["discriminant_exponents"],
                                    model["local_reduction"], strict=True):
            assert c4 % p != 0  # multiplicative, primitive at every bad place
            assert red[0] == 1 and red[1] == 4 + exponent
            assert red[2] == [1, 0, 0, 0]
            product *= red[3]
        assert product == model["finite_tamagawa_product"]
        discriminant_product = 1
        for p, exponent in zip(model["bad_primes"], model["discriminant_exponents"], strict=True):
            discriminant_product *= p**exponent
        assert -discriminant_product == delta
        # This computes the analytic candidate used to select Miller's branch.
        # It does not identify that candidate with the arithmetic Sha order.
        value = (model["normalized_modular_symbol_value"] if label == "1309a1" else
                 model["modular_symbol"]["value"])
        assert value == data["exact_period_normalization"]["curves"][label]["absolute_period_ratio"]
        assert value == 16 * product
        if gp:
            expression = (
                f"e=ellinit({json.dumps(a)});ps={json.dumps(model['bad_primes'])};"
                "print([ellminimalmodel(e)[1..5],#ellisomat(e)[1],"
                "ellglobalred(e)[1],ellglobalred(e)[3],"
                "vector(#ps,i,elllocalred(e,ps[i]))]);quit\n"
            )
            assert run_gp(gp, data["gp_stack_bytes"], expression) == [
                a, 1, model["conductor"], product, model["local_reduction"]]
    partner = data["models"]["2045b1"]
    assert partner["a_invariants"] == [1, -1, 0, -5470, -862675]
    assert json.loads(partner["allcurves_row"].split()[3]) == partner["a_invariants"]
    assert partner["ellrank_output"] == [0, 2, 0, []]
    assert partner["rational_torsion_order"] == 1 and partner["bnf_certification"] == [1]
    for aa, b, c, d, e in partner["quartic_coefficients_descending"]:
        i = 12*aa*e - 3*b*d + c*c
        j = 72*aa*c*e + 9*b*c*d - 27*aa*d*d - 27*b*b*e - 2*c**3
        assert (i, j) == (partner["c4"], 2*partner["c6"])
        assert 4*i**3 - j*j == 27*256*partner["discriminant"]
    symbol = partner["modular_symbol"]
    assert (symbol["sign"], symbol["level"], symbol["weight"]) == (1, 2045, 2)
    assert symbol["value"] == 16 and symbol["path"] == ["oo", 0]
    assert symbol["sturm_bound"] == 2*(5+1)*(409+1)//12 == 410
    first = data["first_curve"]
    assert (first["finite_tamagawa_product"], first["rational_torsion_order"]) == (1, 1)
    assert first["local_reduction"] == [1, 5, [1, 0, 0, 0], 1]
    if gp:
        expression = (
            f"e=ellinit({json.dumps(prior['models']['571a1']['a_invariants'])});"
            "[m,sy]=msfromell(e,1);pa=mspathgens(m)[1];"
            "ev=vector(#pa,i,mseval(m,sy,pa[i]));q=msqexpansion(m,sy,96);"
            "print([ellglobalred(e)[3],elltors(e)[1],elllocalred(e,571),"
            "#sy,#pa,msissymbol(m,ev),mseval(m,sy,[oo,0]),q==ellan(e,96)]);quit\n"
        )
        assert run_gp(gp, data["gp_stack_bytes"], expression) == [
            1, 1, first["local_reduction"], 95, 97, 1, 4, 1]
        expression = (
            f"setrand({data['random_seed']});e=ellinit({json.dumps(partner['a_invariants'])});"
            "rk=ellrankinit(e);bc=vector(#rk[3],i,bnfcertify(rk[3][i]));cv=ell2cover(rk);"
            "print([bc,elltors(e)[1],ellrank(rk),vector(#cv,i,Vec(cv[i][1]))]);quit\n"
        )
        assert run_gp(gp, data["gp_stack_bytes"], expression) == [
            [1], 1, [0, 2, 0, []], partner["quartic_coefficients_descending"]]
        expression = (
            f"e=ellinit({json.dumps(partner['a_invariants'])});[m,sy]=msfromell(e,1);"
            "pa=mspathgens(m)[1];ev=vector(#pa,i,mseval(m,sy,pa[i]));"
            "q=msqexpansion(m,sy,410);print([#sy,#pa,msissymbol(m,sy),"
            "msissymbol(m,ev),mseval(m,sy,[oo,0]),#q,q==ellan(e,410)]);quit\n"
        )
        assert run_gp(gp, data["gp_stack_bytes"], expression) == [409, 413, 0, 1, 16, 410, 1]
    print("Sha four-normalization applicability: exact model/local inputs passed; "
          + ("exact Hecke symbols, lattice-normalization inputs and 2045b1 descent reproduced; " if gp else "")
          + "published eight-descent remains an external import")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check the committed fixture (default)")
    parser.add_argument("--gp", help="optional PARI/GP executable for applicability reproduction")
    args = parser.parse_args()
    check(args.gp)


if __name__ == "__main__":
    main()
