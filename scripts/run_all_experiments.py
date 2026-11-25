"""Generate all 16 canonical STRASSEN-94-CERT-1.0 certificates and 4 exact-Q studies
for Paper 57 (OpenAI, Oct. 2, 2026, omega <= 9/4 Strassen spectral profile).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable, Dict, List

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from src.strassen_certifier import SCHEMA_VERSION, verify_certificate
from src.strassen_exact import (
    audit_lemma41_filtration,
    audit_lemma42_three_sectors,
    audit_prop31_separation,
    format_exact_rat,
)

CERT_DIR = ROOT / "certificates"
RES_DIR = ROOT / "results"


def _make_mode1(cid: str, M: int) -> Dict[str, Any]:
    res = audit_prop31_separation(M)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "prop31_fourier_separation_cert",
        "cert_id": cid,
        "M": M,
        "claimed_L": res["L"],
        "claimed_max_abs_phase": res["max_abs_phase"],
        "claimed_surviving_count": res["surviving_count"],
        "claimed_weight_zero_count": res["weight_zero_count"],
        "claimed_actual_max_weight": res["actual_max_weight"],
        "claimed_paper_degree_bound": res["paper_degree_bound"],
    }


def _make_mode2(cid: str, a: int, b: int) -> Dict[str, Any]:
    res = audit_lemma41_filtration(a, b)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "lemma41_determinant_filtration_cert",
        "cert_id": cid,
        "a": a,
        "b": b,
        "claimed_in_dim": res["in_dim"],
        "claimed_out_dim": res["out_dim"],
        "claimed_quot_in_dim": res["quot_in_dim"],
        "claimed_ker_in_dim": res["ker_in_dim"],
        "claimed_upper_right_nnz": res["upper_right_nnz"],
        "claimed_cross_block_nnz": res["cross_block_nnz"],
        "claimed_diag_plus_nnz": res["diag_plus_nnz"],
        "claimed_diag_minus_nnz": res["diag_minus_nnz"],
    }


def _make_mode3(cid: str, a: int, h: int) -> Dict[str, Any]:
    res = audit_lemma42_three_sectors(a, h)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "lemma42_three_sector_tripling_cert",
        "cert_id": cid,
        "a": a,
        "h": h,
        "claimed_B": res["B"],
        "claimed_total_terms": res["total_terms"],
        "claimed_w0_left": res["w0_left"],
        "claimed_w0_mid": res["w0_mid"],
        "claimed_w0_right": res["w0_right"],
        "claimed_dropped_w1": res["dropped_w1"],
        "claimed_neg_count": res["neg_count"],
    }


def _make_mode4(
    cid: str,
    a_max: int,
    b_max: int,
    fn: Callable[[int, int], Fraction],
    refute_t: Fraction,
    refute_a: int,
) -> Dict[str, Any]:
    table = [[fn(a, b) for b in range(1, b_max + 1)] for a in range(1, a_max + 1)]
    strict_concave = 0
    for a in range(1, a_max + 1):
        for b in range(2, b_max):
            if Fraction(2, 1) * table[a - 1][b - 1] > table[a - 1][b] + table[a - 1][b - 2]:
                strict_concave += 1
    triplings = 0
    for a in range(1, a_max + 1):
        h = 1
        while 3 * h + a - 1 <= b_max:
            triplings += 1
            h += 1
    D_last = table[a_max - 1][a_max - 1]
    H_last = (Fraction(2, 1) * D_last) / Fraction(3 * a_max - 1, 1)
    ratio = (D_last ** 3) / Fraction(a_max ** 4, 1)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "lemma51_spectral_profile_cert",
        "cert_id": cid,
        "a_max": a_max,
        "b_max": b_max,
        "P_table": [[format_exact_rat(q) for q in row] for row in table],
        "refute_t": format_exact_rat(refute_t),
        "refute_a": refute_a,
        "claimed_D_amax": format_exact_rat(D_last),
        "claimed_H_amax": format_exact_rat(H_last),
        "claimed_D_amax_cube_over_a4": format_exact_rat(ratio),
        "claimed_tripling_checks": triplings,
        "claimed_strict_concave_count": strict_concave,
    }


def build_all_16_certificates() -> List[Dict[str, Any]]:
    certs: List[Dict[str, Any]] = [
        # Mode 1: Proposition 3.1 exact 5M -> M separation (4 certs)
        _make_mode1("prop31_fourier_M2_base", 2),
        _make_mode1("prop31_fourier_M4_quartic", 4),
        _make_mode1("prop31_fourier_M6_hex", 6),
        _make_mode1("prop31_fourier_M8_octal", 8),
        # Mode 2: Lemma 4.1 exact determinant filtration matrix factorization (4 certs)
        _make_mode2("lem41_filtration_C2_2_paper_ex", 2, 2),
        _make_mode2("lem41_filtration_C3_4_asym", 3, 4),
        _make_mode2("lem41_filtration_C4_5_mid", 4, 5),
        _make_mode2("lem41_filtration_C6_6_square", 6, 6),
        # Mode 3: Lemma 4.2 exact three-sector shifted tripling (4 certs)
        _make_mode3("lem42_sectors_C2_4_fig1", 2, 1),
        _make_mode3("lem42_sectors_C3_8_tripled", 3, 2),
        _make_mode3("lem42_sectors_C5_16_mid", 5, 4),
        _make_mode3("lem42_sectors_C8_31_diag", 8, 8),
        # Mode 4: Lemma 5.1 exact rational Strassen spectral profiles (4 certs)
        # 13. Zero-slack tight alpha=1/3 profile: P(a,b) = a + b - 1 + (1/3)(a-1)(b-1), refuting t=1 (omega=3) at a=8
        _make_mode4(
            "lem51_profile_tight_alpha1_3",
            6, 23,
            lambda a, b: Fraction(a + b - 1, 1) + Fraction((a - 1) * (b - 1), 3),
            Fraction(1, 1), 8,
        ),
        # 14. Strictly concave rational profile: alpha=1/2, beta=1/5 (3*alpha-1=1/2 > 2/5=2*beta), refuting t=5/6 at a=1000
        _make_mode4(
            "lem51_profile_strict_concave_1_2",
            6, 23,
            lambda a, b: Fraction(a + b - 1, 1) + Fraction((a - 1) * (b - 1), 2) + Fraction((a - 1) * (b - 1), 5 * (a + b + 1)),
            Fraction(5, 6), 1000,
        ),
        # 15. Product rank-1 profile P(a,b) = a*b (t=1/2 extreme), refuting t=4/5 (omega=12/5=2.40) at a=50000
        _make_mode4(
            "lem51_profile_product_ab_amax8",
            8, 31,
            lambda a, b: Fraction(a * b, 1),
            Fraction(4, 5), 50000,
        ),
        # 16. Strictly concave profile at a_max=7: alpha=2/5, beta=1/12 (3*alpha-1=1/5 > 1/6=2*beta), refuting t=9/11 (omega=27/11) at a=2048
        _make_mode4(
            "lem51_profile_concave_tight_amax7",
            7, 27,
            lambda a, b: Fraction(a + b - 1, 1) + Fraction(2 * (a - 1) * (b - 1), 5) + Fraction((a - 1) * (b - 1), 12 * (a + b + 2)),
            Fraction(9, 11), 2048,
        ),
    ]
    assert len(certs) == 16
    return certs


def main() -> None:
    CERT_DIR.mkdir(parents=True, exist_ok=True)
    RES_DIR.mkdir(parents=True, exist_ok=True)

    # 1. Generate and time all 16 canonical certificates
    certs = build_all_16_certificates()
    atlas_rows: List[Dict[str, Any]] = []
    for cert in certs:
        out_path = CERT_DIR / f"{cert['cert_id']}.cert.json"
        out_path.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        summary = verify_certificate(cert)
        t0 = time.perf_counter()
        reps = 7
        for _ in range(reps):
            verify_certificate(cert)
        mean_ms = round(((time.perf_counter() - t0) * 1000.0) / reps, 3)
        atlas_rows.append({
            "cert_id": cert["cert_id"],
            "mode": cert["mode"],
            "mean_ms": mean_ms,
            "summary": summary,
        })
    (RES_DIR / "exp1_certificate_atlas.json").write_text(
        json.dumps({"count": len(atlas_rows), "certificates": atlas_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # 2. Experiment 2: Exact Lemma 5.1 diagonal growth comparison across a=1..20
    # Compare exact lower envelope H_lb(a) = prod_{m=1}^{a-1} (1 + 1/(3m)) and D_lb(a) = ((3a-1)/2) * H_lb(a)
    # against a^{4/3}, the tight rational profile P_{1/3}(a,a), and the interpolation ceiling (2a-1)^{4/3}.
    growth_rows = []
    H_lb = Fraction(1, 1)
    for a in range(1, 21):
        if a >= 2:
            H_lb *= Fraction(3 * (a - 1) + 1, 3 * (a - 1))
        D_lb = (Fraction(3 * a - 1, 2)) * H_lb
        P_tight = Fraction(2 * a - 1, 1) + Fraction((a - 1) * (a - 1), 3)
        H_lb_cu_over_a = (H_lb ** 3) / Fraction(a, 1)
        D_lb_cu_over_a4 = (D_lb ** 3) / Fraction(a ** 4, 1)
        assert H_lb_cu_over_a >= 1 and D_lb_cu_over_a4 >= 1
        growth_rows.append({
            "a": a,
            "H_lb_val": round(H_lb.numerator / H_lb.denominator, 6),
            "D_lb_val": round(D_lb.numerator / D_lb.denominator, 6),
            "a_4_3_val": round(a ** (4.0 / 3.0), 6),
            "P_tight_val": round(P_tight.numerator / P_tight.denominator, 6),
            "upper_9_4_val": round((2 * a - 1) ** (4.0 / 3.0), 6),
            "H_lb_cube_over_a_val": round(H_lb_cu_over_a.numerator / H_lb_cu_over_a.denominator, 6),
            "D_lb_cube_over_a4_val": round(D_lb_cu_over_a4.numerator / D_lb_cu_over_a4.denominator, 6),
        })
    (RES_DIR / "exp2_lemma51_diagonal_growth.json").write_text(
        json.dumps({"rows": growth_rows}, indent=2) + "\n", encoding="utf-8"
    )

    # 3. Experiment 3: Proposition 3.1 exact mismatch degree tightening ((M-1)//2)^2 vs (M-1)^2 (M=1..10)
    # and Lemma 4.2 three-sector survival efficiency 3ah / (a*(3h+a-1))
    prop31_rows = []
    for M in range(1, 10):
        r = audit_prop31_separation(M)
        prop31_rows.append({
            "M": M,
            "L": r["L"],
            "surviving_count": r["surviving_count"],
            "weight_zero_count": r["weight_zero_count"],
            "actual_max_weight": r["actual_max_weight"],
            "paper_degree_bound": r["paper_degree_bound"],
        })
    lem42_rows = []
    for a in (2, 3, 4, 6, 8, 12):
        r = audit_lemma42_three_sectors(a, a)
        eff = Fraction(3 * a * a, r["total_terms"])
        lem42_rows.append({
            "a": a,
            "B": r["B"],
            "total_terms": r["total_terms"],
            "w0_total": 3 * a * a,
            "dropped_w1": r["dropped_w1"],
            "survival_ratio_rat": format_exact_rat(eff),
            "survival_ratio_val": round(eff.numerator / eff.denominator, 6),
        })
    (RES_DIR / "exp3_prop31_and_lem42_scaling.json").write_text(
        json.dumps({"prop31": prop31_rows, "lem42": lem42_rows}, indent=2) + "\n", encoding="utf-8"
    )

    # 4. Experiment 4: Exact finite refutation threshold a*(t) where a^{4p} > (2a-1)^{3q} for t = p/q > 3/4
    refute_targets = [
        ("1", Fraction(1, 1), "3"),
        ("9/10", Fraction(9, 10), "27/10"),
        ("5/6", Fraction(5, 6), "5/2"),
        ("9/11", Fraction(9, 11), "27/11"),
        ("4/5", Fraction(4, 5), "12/5"),
    ]
    refute_rows = []
    for lbl, tq, om_lbl in refute_targets:
        p_n, q_d = tq.numerator, tq.denominator
        # Find exact minimal integer a >= 2 with a^(4p) > (2a - 1)^(3q) by binary search
        lo, hi = 2, 2
        while not (hi ** (4 * p_n) > (2 * hi - 1) ** (3 * q_d)):
            hi *= 2
        while lo < hi:
            mid = (lo + hi) // 2
            if mid ** (4 * p_n) > (2 * mid - 1) ** (3 * q_d):
                hi = mid
            else:
                lo = mid + 1
        assert lo ** (4 * p_n) > (2 * lo - 1) ** (3 * q_d)
        assert (lo - 1) ** (4 * p_n) <= (2 * (lo - 1) - 1) ** (3 * q_d)
        refute_rows.append({
            "t_rat": lbl,
            "omega_rat": om_lbl,
            "omega_val": round((Fraction(3, 1) * tq).numerator / (Fraction(3, 1) * tq).denominator, 5),
            "min_refute_a": lo,
        })
    (RES_DIR / "exp4_exponent_refutation_thresholds.json").write_text(
        json.dumps({"rows": refute_rows}, indent=2) + "\n", encoding="utf-8"
    )

    print(f"[PASS] Generated {len(atlas_rows)} canonical {SCHEMA_VERSION} certificates and 4 exact-Q studies.")
    for r in atlas_rows:
        print(f"  {r['cert_id']:36s} {r['mean_ms']:6.3f} ms  ({r['mode']})")
    print("[PASS] Exact minimal refutation thresholds a*(t):")
    for rr in refute_rows:
        print(f"  t={rr['t_rat']:5s} (omega={rr['omega_rat']:5s}) -> min a* = {rr['min_refute_a']}")


if __name__ == "__main__":
    main()
