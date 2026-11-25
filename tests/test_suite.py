"""64-check pytest suite (16 canonical certs + 60 live adversarial forgery attacks + 3 raw JSON checks)
for Paper 57 (STRASSEN-94-CERT-1.0).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any, Callable, Dict, List, Tuple

import pytest

from src.strassen_certifier import (
    CertificateError,
    verify_certificate,
    verify_certificate_file,
    verify_certificate_json_text,
)

ROOT = Path(__file__).resolve().parent.parent
CERT_DIR = ROOT / "certificates"


def _load(stem: str) -> Dict[str, Any]:
    return json.loads((CERT_DIR / f"{stem}.cert.json").read_text(encoding="utf-8"))


def test_all_16_canonical_certificates_pass() -> None:
    paths = sorted(CERT_DIR.glob("*.cert.json"))
    assert len(paths) == 16
    for p in paths:
        res = verify_certificate_file(p)
        assert res["verified"] is True


def test_raw_json_rejects_ieee754_float_token() -> None:
    raw = json.dumps(_load("lem51_profile_tight_alpha1_3")).replace('"10/3"', "3.3333", 1)
    with pytest.raises(CertificateError):
        verify_certificate_json_text(raw)


def test_raw_json_rejects_nan_infinity() -> None:
    raw = '{"schema": "STRASSEN-94-CERT-1.0", "mode": "prop31_fourier_separation_cert", "cert_id": "x", "M": NaN}'
    with pytest.raises(CertificateError):
        verify_certificate_json_text(raw)


def test_raw_json_rejects_duplicate_keys() -> None:
    raw = '{"schema": "STRASSEN-94-CERT-1.0", "schema": "STRASSEN-94-CERT-1.0", "mode": "prop31_fourier_separation_cert", "cert_id": "x"}'
    with pytest.raises(CertificateError):
        verify_certificate_json_text(raw)


def _build_60_attacks() -> List[Tuple[str, Callable[[], Dict[str, Any]]]]:
    m1 = _load("prop31_fourier_M6_hex")
    m2 = _load("lem41_filtration_C3_4_asym")
    m3 = _load("lem42_sectors_C3_8_tripled")
    m4_t = _load("lem51_profile_tight_alpha1_3")
    m4_c = _load("lem51_profile_strict_concave_1_2")

    def mod(base: Dict[str, Any], fn: Callable[[Dict[str, Any]], None]) -> Callable[[], Dict[str, Any]]:
        def _run() -> Dict[str, Any]:
            c = copy.deepcopy(base)
            fn(c)
            return c
        return _run

    attacks: List[Tuple[str, Callable[[], Dict[str, Any]]]] = [
        # --- 12 Schema / Parser / AST Attacks ---
        ("S01_wrong_schema", mod(m1, lambda c: c.__setitem__("schema", "STRASSEN-94-CERT-0.9"))),
        ("S02_unknown_mode", mod(m1, lambda c: c.__setitem__("mode", "bogus_mode"))),
        ("S03_empty_cert_id", mod(m1, lambda c: c.__setitem__("cert_id", "  "))),
        ("S04_non_reduced_rat", mod(m4_t, lambda c: c.__setitem__("refute_t", "2/2"))),
        ("S05_leading_zero_rat", mod(m4_t, lambda c: c.__setitem__("refute_t", "01"))),
        ("S06_negative_zero_rat", mod(m4_t, lambda c: c["P_table"][0].__setitem__(0, "-0"))),
        ("S07_plus_sign_rat", mod(m4_t, lambda c: c.__setitem__("refute_t", "+1"))),
        ("S08_unicode_digit_rat", mod(m4_t, lambda c: c.__setitem__("refute_t", "١"))),
        ("S09_int_in_rat_field", mod(m4_t, lambda c: c.__setitem__("refute_t", 1))),
        ("S10_bool_in_int_field", mod(m1, lambda c: c.__setitem__("M", True))),
        ("S11_oversized_rat_str", mod(m4_t, lambda c: c.__setitem__("refute_t", "1" + "0" * 2005))),
        ("S12_denom_one_rat", mod(m4_t, lambda c: c.__setitem__("refute_t", "5/1"))),

        # --- 10 Mode 1 (Prop. 3.1 Fourier Separation) Forgeries ---
        ("M1_01_M_zero", mod(m1, lambda c: c.__setitem__("M", 0))),
        ("M1_02_M_negative", mod(m1, lambda c: c.__setitem__("M", -2))),
        ("M1_03_M_above_cap", mod(m1, lambda c: c.__setitem__("M", 13))),
        ("M1_04_forged_L", mod(m1, lambda c: c.__setitem__("claimed_L", 29))),
        ("M1_05_forged_max_phase", mod(m1, lambda c: c.__setitem__("claimed_max_abs_phase", 14))),
        ("M1_06_forged_surviving", mod(m1, lambda c: c.__setitem__("claimed_surviving_count", 36))),
        ("M1_07_forged_w0_count", mod(m1, lambda c: c.__setitem__("claimed_weight_zero_count", 35))),
        ("M1_08_forged_actual_max_w", mod(m1, lambda c: c.__setitem__("claimed_actual_max_weight", 25))),
        ("M1_09_forged_paper_deg", mod(m1, lambda c: c.__setitem__("claimed_paper_degree_bound", 24))),
        ("M1_10_missing_claimed_L", mod(m1, lambda c: c.pop("claimed_L"))),

        # --- 12 Mode 2 (Lem. 4.1 Determinant Filtration) Forgeries ---
        ("M2_01_a_zero", mod(m2, lambda c: c.__setitem__("a", 0))),
        ("M2_02_b_one", mod(m2, lambda c: c.__setitem__("b", 1))),
        ("M2_03_a_above_cap", mod(m2, lambda c: c.__setitem__("a", 11))),
        ("M2_04_b_above_cap", mod(m2, lambda c: c.__setitem__("b", 11))),
        ("M2_05_forged_in_dim", mod(m2, lambda c: c.__setitem__("claimed_in_dim", 7))),
        ("M2_06_forged_out_dim", mod(m2, lambda c: c.__setitem__("claimed_out_dim", 11))),
        ("M2_07_forged_quot_in", mod(m2, lambda c: c.__setitem__("claimed_quot_in_dim", 4))),
        ("M2_08_forged_ker_in", mod(m2, lambda c: c.__setitem__("claimed_ker_in_dim", 4))),
        ("M2_09_forged_ur_nnz", mod(m2, lambda c: c.__setitem__("claimed_upper_right_nnz", 1))),
        ("M2_10_forged_cross_nnz", mod(m2, lambda c: c.__setitem__("claimed_cross_block_nnz", 0))),
        ("M2_11_forged_plus_nnz", mod(m2, lambda c: c.__setitem__("claimed_diag_plus_nnz", 10))),
        ("M2_12_forged_minus_nnz", mod(m2, lambda c: c.__setitem__("claimed_diag_minus_nnz", 10))),

        # --- 10 Mode 3 (Lem. 4.2 Three-Sector Tripling) Forgeries ---
        ("M3_01_a_zero", mod(m3, lambda c: c.__setitem__("a", 0))),
        ("M3_02_h_zero", mod(m3, lambda c: c.__setitem__("h", 0))),
        ("M3_03_a_above_cap", mod(m3, lambda c: c.__setitem__("a", 26))),
        ("M3_04_forged_B", mod(m3, lambda c: c.__setitem__("claimed_B", 9))),
        ("M3_05_forged_total_terms", mod(m3, lambda c: c.__setitem__("claimed_total_terms", 25))),
        ("M3_06_forged_w0_left", mod(m3, lambda c: c.__setitem__("claimed_w0_left", 5))),
        ("M3_07_forged_w0_mid", mod(m3, lambda c: c.__setitem__("claimed_w0_mid", 7))),
        ("M3_08_forged_w0_right", mod(m3, lambda c: c.__setitem__("claimed_w0_right", 5))),
        ("M3_09_forged_dropped_w1", mod(m3, lambda c: c.__setitem__("claimed_dropped_w1", 5))),
        ("M3_10_forged_neg_count", mod(m3, lambda c: c.__setitem__("claimed_neg_count", 1))),

        # --- 16 Mode 4 (Lem. 5.1 Spectral Profile & 9/4 Refutation) Forgeries ---
        ("M4_01_amax_too_small", mod(m4_t, lambda c: c.__setitem__("a_max", 1))),
        ("M4_02_bmax_too_small", mod(m4_t, lambda c: c.__setitem__("b_max", 20))),
        ("M4_03_ragged_table", mod(m4_t, lambda c: c["P_table"][0].pop())),
        ("M4_04_nonpositive_entry", mod(m4_t, lambda c: c["P_table"][1].__setitem__(1, "0"))),
        ("M4_05_base_P1b_violated", mod(m4_t, lambda c: c["P_table"][0].__setitem__(2, "4"))),
        ("M4_06_symmetry_violated", mod(m4_t, lambda c: c["P_table"][1].__setitem__(2, "100"))),
        ("M4_07_concavity_violated", mod(m4_t, lambda c: c["P_table"][1].__setitem__(10, "1"))),
        ("M4_08_tripling_violated", mod(m4_t, lambda c: c.__setitem__(
            "P_table",
            [[str(a + b - 1) for b in range(1, c["b_max"] + 1)] for a in range(1, c["a_max"] + 1)],
        ))),
        ("M4_09_refute_t_le_3_4", mod(m4_t, lambda c: c.__setitem__("refute_t", "3/4"))),
        ("M4_10_refute_a_too_small", mod(m4_t, lambda c: c.__setitem__("refute_a", 6))),
        ("M4_11_refute_a_oob", mod(m4_t, lambda c: c.__setitem__("refute_a", 1))),
        ("M4_12_forged_D_amax", mod(m4_t, lambda c: c.__setitem__("claimed_D_amax", "20"))),
        ("M4_13_forged_H_amax", mod(m4_t, lambda c: c.__setitem__("claimed_H_amax", "2"))),
        ("M4_14_forged_ratio_a4", mod(m4_t, lambda c: c.__setitem__("claimed_D_amax_cube_over_a4", "1"))),
        ("M4_15_forged_tripling_cnt", mod(m4_t, lambda c: c.__setitem__("claimed_tripling_checks", 10))),
        ("M4_16_forged_strict_conc", mod(m4_c, lambda c: c.__setitem__("claimed_strict_concave_count", 0))),
    ]
    assert len(attacks) == 60
    return attacks


@pytest.mark.parametrize("name,builder", _build_60_attacks(), ids=[a[0] for a in _build_60_attacks()])
def test_live_adversarial_forgery_rejected(name: str, builder: Callable[[], Dict[str, Any]]) -> None:
    forged = builder()
    with pytest.raises(CertificateError) as exc_info:
        verify_certificate(forged)
    if name == "M4_08_tripling_violated":
        assert "Shifted tripling violated" in str(exc_info.value)
