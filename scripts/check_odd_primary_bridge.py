#!/usr/bin/env python3
"""Check the exact inputs to the 1913b1 ordinary three-primary bridge.

Optional PARI reproduction checks local data and an exact primitive Hecke
eigensymbol. It does not rerun Miller's three-descent/Iwasawa upper bound,
prove Galois/derived-category imports, or construct Stark core vertices.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path

from check_sha_dimension_pair import c6, run_gp
from check_support_prime_data import count_points, count_points_quadratic, invariants


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "formalization/odd_primary_selmer_bridge.json"


def check(gp: str | None) -> None:
    data = json.loads(FIXTURE.read_text())
    model = data["model"]
    a = model["a_invariants"]
    c4, delta = invariants(a)
    assert a == [1, 1, 0, -34, -135] == model["minimal_a_invariants"]
    assert json.loads(model["allcurves_row"].split()[3]) == a
    assert (c4, c6(a), delta) == (1657, 104275, -1913**2)
    assert (c4, c6(a), delta) == (model["c4"], model["c6"], model["discriminant"])
    assert c4 % 1913 and c4**3 % delta and delta % 3 and delta % 5
    assert model["conductor"] == 1913 < 5000
    assert model["rational_torsion_order"] == model["finite_tamagawa_product"] == 2
    assert model["local_reduction"] == [1, 6, [1, 0, 0, 0], 2]
    assert model["isogeny_degree_matrix"] == [[1, 2], [2, 1]]
    for p in (3, 5):
        expected = model["point_counts"][str(p)]
        assert count_points(a, p) == count_points_quadratic(a, p) == expected
        assert p + 1 - expected == model["a_p"][str(p)]
    assert model["a_p"]["3"] % 3 != 0
    assert model["rational_torsion_order"] * model["finite_tamagawa_product"] * 2 % 3 != 0
    # x^2 - a_5*x + 5 is irreducible over F_3 and its roots have order eight.
    assert all((t*t - 2*t + 2) % 3 for t in range(3))
    symbol = model["modular_symbol"]
    assert (symbol["sign"], symbol["level"], symbol["weight"]) == (1, 1913, 2)
    assert symbol["eigenspace_dimension"] == symbol["generator_value_content"] == 1
    assert symbol["primitive_path_value_absolute"] == 9
    assert symbol["sturm_bound"] == 2*(1913+1)//12 == 319
    ratio = Fraction(*symbol["absolute_period_ratio"])
    assert ratio == Fraction(symbol["primitive_path_value_absolute"], 2)
    candidate = ratio * model["rational_torsion_order"]**2 / model["finite_tamagawa_product"]
    assert candidate == symbol["analytic_candidate"] == 9 == 3**2
    partner = json.loads((ROOT / "formalization/sha_four_normalization.json").read_text())
    anomalous = data["matched_partner_at_two"]
    aa = partner["models"]["2045b1"]["a_invariants"]
    assert count_points(aa, 2) == count_points_quadratic(aa, 2) == anomalous["point_count"] == 2
    assert anomalous["a_p"] == 1 and anomalous["ordinary"] and not anomalous["non_anomalous"]
    assert anomalous["unit_root_polynomial_coefficients"] == [1, -1, 2]
    assert anomalous["discrete_ordinary_quotient_invariant_order"] == 2
    # Finite-level controls; the limiting order uses the written unit-root argument.
    for k in range(1, 8):
        modulus = 2**k
        roots = [r for r in range(modulus) if r % 2 and (r*r-r+2) % modulus == 0]
        assert len(roots) == 1
        fixed = [x for x in range(modulus) if (roots[0]-1)*x % modulus == 0]
        assert fixed == [0, 2**(k-1)]
    # Finite controls for the separate written arithmetic core-vertex return.
    # These do not prove Galois-image closedness or the existence of auxiliary primes.
    core = json.loads((ROOT / "formalization/stark_core_vertex_construction.json").read_text())
    controls = core["finite_controls"]
    assert controls["bad_prime"] == model["conductor"] == 1913
    assert controls["minimal_discriminant_valuation"] == 2
    assert delta % 1913**2 == 0 and delta % 1913**3 != 0
    assert c4 % 1913 != 0
    modulus = controls["coefficient_modulus"]
    unit = controls["inertia_upper_right"]
    inverse = controls["inverse_of_two"]
    assert (modulus, unit, inverse) == (27, 2, 14)
    assert unit * inverse % modulus == 1
    images = {(3*y % modulus, -3*x % modulus)
              for x in range(modulus) for y in range(modulus)}
    kernel = [(x, y) for x in range(modulus) for y in range(modulus)
              if 3*x % modulus == 3*y % modulus == 0]
    assert len(kernel) == controls["localisation_kernel_size"] == 9
    assert len(images) == controls["localisation_image_size"] == 81
    assert controls["fitting_generators"] == [9, 3, 1]
    assert controls["unit_scaled_generators"] == [18, 6, 2]
    for generator, scaled in zip(controls["fitting_generators"], controls["unit_scaled_generators"]):
        assert scaled == unit*generator
        assert {generator*x % modulus for x in range(modulus)} == {
            scaled*x % modulus for x in range(modulus)}
    assert controls["basis_unit_coefficients"] == [1, 2]
    squares = {x*x % modulus for x in range(modulus)}
    assert 1 in squares and 2 not in squares
    if gp:
        expression = (
            f"e=ellinit({json.dumps(a)});im=ellisomat(e)[2];"
            "print([ellminimalmodel(e)[1..5],elltors(e)[1],ellglobalred(e)[1],"
            "ellglobalred(e)[3],elllocalred(e,1913),"
            "vector(2,i,vector(2,j,im[i,j])),vector(3,i,ellap(e,prime(i)))]);quit\n"
        )
        assert run_gp(gp, data["gp_stack_bytes"], expression) == [
            a, 2, 1913, 2, model["local_reduction"], [[1, 2], [2, 1]], [1, 2, 2]]
        expression = (
            f"e=ellinit({json.dumps(a)});m=msinit(1913,2,1);ps=[2,3,5];"
            "hp=vector(#ps,i,[ps[i],ellap(e,ps[i])]);h=msfromhecke(m,hp);"
            "if(#h!=1,error(\"eigenspace dimension\"));v=h[,1];pa=mspathgens(m)[1];"
            "ev=vector(#pa,i,mseval(m,v,pa[i]));v=v/content(ev);"
            "ev=vector(#pa,i,mseval(m,v,pa[i]));q=msqexpansion(m,v,319);"
            "print([hp,#h,#v,#pa,content(ev),msissymbol(m,ev),msstar(m)*v==v,"
            "abs(mseval(m,v,[oo,0])),q==ellan(e,319)]);quit\n"
        )
        assert run_gp(gp, data["gp_stack_bytes"], expression) == [
            symbol["hecke_prime_eigenvalues"], 1, 160, 321, 1, 1, 1, 9, 1]
    print("Odd-primary bridge: exact equation, local/ordinary, anomaly and finite Stark controls passed; "
          + ("PARI model and exact Hecke symbol reproduced; " if gp else "")
          + "published three-primary upper bound and arithmetic transports remain external")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check the committed fixture (default)")
    parser.add_argument("--gp", help="optional PARI/GP executable for exact input reproduction")
    args = parser.parse_args()
    check(args.gp)


if __name__ == "__main__":
    main()
