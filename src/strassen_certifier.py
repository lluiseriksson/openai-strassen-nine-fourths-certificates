"""Pure-stdlib, zero-floating-point exact-Q certificate auditor for Paper 57:
STRASSEN-94-CERT-1.0 (OpenAI, Oct. 2, 2026, omega <= 9/4 Strassen spectral profile).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Tuple

from .strassen_exact import (
    audit_lemma41_filtration,
    audit_lemma42_three_sectors,
    audit_prop31_separation,
    format_exact_rat,
    parse_exact_rat,
)

SCHEMA_VERSION = "STRASSEN-94-CERT-1.0"
MAX_NESTING_DEPTH = 20


class CertificateError(ValueError):
    """Raised whenever a STRASSEN-94-CERT-1.0 certificate fails exact validation."""


def _guard_json_ast(obj: Any, depth: int = 0) -> None:
    if depth > MAX_NESTING_DEPTH:
        raise CertificateError(f"Nesting depth exceeded {MAX_NESTING_DEPTH}")
    if obj is None or type(obj) in (bool, int, str):
        return
    if type(obj) is list:
        for item in obj:
            _guard_json_ast(item, depth + 1)
        return
    if type(obj) is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise CertificateError("All JSON object keys must be strings")
            _guard_json_ast(v, depth + 1)
        return
    raise CertificateError(f"Unsupported or non-exact JSON type: {type(obj).__name__}")


def _strict_int(val: Any, label: str) -> int:
    if isinstance(val, bool) or not isinstance(val, int):
        raise CertificateError(f"{label}: expected strict integer")
    return val


def _parse_rat(val: Any, label: str) -> Fraction:
    try:
        return parse_exact_rat(val, label)
    except ValueError as exc:
        raise CertificateError(str(exc)) from exc


def _check_claimed_int(payload: Dict[str, Any], key: str, actual: int) -> None:
    if key not in payload:
        raise CertificateError(f"Missing required field '{key}'")
    claimed = _strict_int(payload[key], key)
    if claimed != actual:
        raise CertificateError(f"Claimed {key}={claimed} != exact {actual}")


def _check_claimed_rat(payload: Dict[str, Any], key: str, actual: Fraction) -> None:
    if key not in payload:
        raise CertificateError(f"Missing required field '{key}'")
    claimed = _parse_rat(payload[key], key)
    if claimed != actual:
        raise CertificateError(
            f"Claimed {key}={format_exact_rat(claimed)} != exact {format_exact_rat(actual)}"
        )


def _verify_mode1(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 1: Proposition 3.1 exact 5M -> M Fourier separation & squared-mismatch audit."""
    M = _strict_int(payload.get("M"), "M")
    if not (1 <= M <= 12):
        raise CertificateError(f"M must satisfy 1 <= M <= 12 for exhaustive M^4 audit, got {M}")
    res = audit_prop31_separation(M)
    if res["weight_zero_count"] != M * M:
        raise CertificateError("Weight-zero survival count != M^2")
    if res["actual_max_weight"] != ((M - 1) // 2) ** 2:
        raise CertificateError("Tight mismatch degree mismatch")
    if res["actual_max_weight"] > res["paper_degree_bound"]:
        raise CertificateError("Actual max weight exceeded (M-1)^2")
    _check_claimed_int(payload, "claimed_L", res["L"])
    _check_claimed_int(payload, "claimed_max_abs_phase", res["max_abs_phase"])
    _check_claimed_int(payload, "claimed_surviving_count", res["surviving_count"])
    _check_claimed_int(payload, "claimed_weight_zero_count", res["weight_zero_count"])
    _check_claimed_int(payload, "claimed_actual_max_weight", res["actual_max_weight"])
    _check_claimed_int(payload, "claimed_paper_degree_bound", res["paper_degree_bound"])
    return {
        "verified": True,
        "mode": payload["mode"],
        "cert_id": payload["cert_id"],
        "M": M,
        "L": res["L"],
        "surviving_count": res["surviving_count"],
        "weight_zero_count": res["weight_zero_count"],
        "actual_max_weight": res["actual_max_weight"],
        "paper_degree_bound": res["paper_degree_bound"],
    }


def _verify_mode2(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 2: Lemma 4.1 exact determinant-filtration block-triangular matrix audit."""
    a = _strict_int(payload.get("a"), "a")
    b = _strict_int(payload.get("b"), "b")
    if not (1 <= a <= 10 and 2 <= b <= 10):
        raise CertificateError(f"Dimensions must satisfy 1 <= a <= 10, 2 <= b <= 10; got ({a}, {b})")
    try:
        res = audit_lemma41_filtration(a, b)
    except ValueError as exc:
        raise CertificateError(str(exc)) from exc
    _check_claimed_int(payload, "claimed_in_dim", res["in_dim"])
    _check_claimed_int(payload, "claimed_out_dim", res["out_dim"])
    _check_claimed_int(payload, "claimed_quot_in_dim", res["quot_in_dim"])
    _check_claimed_int(payload, "claimed_ker_in_dim", res["ker_in_dim"])
    _check_claimed_int(payload, "claimed_upper_right_nnz", res["upper_right_nnz"])
    _check_claimed_int(payload, "claimed_cross_block_nnz", res["cross_block_nnz"])
    _check_claimed_int(payload, "claimed_diag_plus_nnz", res["diag_plus_nnz"])
    _check_claimed_int(payload, "claimed_diag_minus_nnz", res["diag_minus_nnz"])
    return {
        "verified": True,
        "mode": payload["mode"],
        "cert_id": payload["cert_id"],
        "a": a,
        "b": b,
        "in_dim": res["in_dim"],
        "out_dim": res["out_dim"],
        "upper_right_nnz": res["upper_right_nnz"],
        "cross_block_nnz": res["cross_block_nnz"],
        "diag_plus_nnz": res["diag_plus_nnz"],
        "diag_minus_nnz": res["diag_minus_nnz"],
    }


def _verify_mode3(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 3: Lemma 4.2 exact three-sector shifted-tripling C(a, 3h + a - 1) audit."""
    a = _strict_int(payload.get("a"), "a")
    h = _strict_int(payload.get("h"), "h")
    if not (1 <= a <= 25 and 1 <= h <= 25):
        raise CertificateError(f"Parameters must satisfy 1 <= a, h <= 25; got ({a}, {h})")
    try:
        res = audit_lemma42_three_sectors(a, h)
    except ValueError as exc:
        raise CertificateError(str(exc)) from exc
    if res["neg_count"] != 0:
        raise CertificateError("Negative weight term encountered in Lemma 4.2")
    if not (res["w0_left"] == res["w0_mid"] == res["w0_right"] == a * h):
        raise CertificateError("Three matched sectors did not each have exact size a * h")
    if res["dropped_w1"] != a * (a - 1):
        raise CertificateError("Weight +1 dropped term count != a*(a-1)")
    _check_claimed_int(payload, "claimed_B", res["B"])
    _check_claimed_int(payload, "claimed_total_terms", res["total_terms"])
    _check_claimed_int(payload, "claimed_w0_left", res["w0_left"])
    _check_claimed_int(payload, "claimed_w0_mid", res["w0_mid"])
    _check_claimed_int(payload, "claimed_w0_right", res["w0_right"])
    _check_claimed_int(payload, "claimed_dropped_w1", res["dropped_w1"])
    _check_claimed_int(payload, "claimed_neg_count", res["neg_count"])
    return {
        "verified": True,
        "mode": payload["mode"],
        "cert_id": payload["cert_id"],
        "a": a,
        "h": h,
        "B": res["B"],
        "sector_size": a * h,
        "dropped_w1": res["dropped_w1"],
    }


def _verify_mode4(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Mode 4: Lemma 5.1 exact rational spectral profile & t <= 3/4 (omega <= 9/4) audit."""
    a_max = _strict_int(payload.get("a_max"), "a_max")
    b_max = _strict_int(payload.get("b_max"), "b_max")
    if not (2 <= a_max <= 12 and b_max >= 4 * a_max - 1 and b_max <= 60):
        raise CertificateError(f"Invalid table bounds a_max={a_max}, b_max={b_max}")
    raw_table = payload.get("P_table")
    if not isinstance(raw_table, list) or len(raw_table) != a_max:
        raise CertificateError(f"P_table must have {a_max} rows")
    P: List[List[Fraction]] = []
    for i, row in enumerate(raw_table):
        if not isinstance(row, list) or len(row) != b_max:
            raise CertificateError(f"P_table[{i}] must have length {b_max}")
        parsed = [_parse_rat(v, f"P[{i+1},{j+1}]") for j, v in enumerate(row)]
        if any(q <= 0 for q in parsed):
            raise CertificateError(f"P_table[{i}] contains non-positive entry")
        P.append(parsed)

    def getP(a: int, b: int) -> Fraction:
        return P[a - 1][b - 1]

    # 1. Base condition P(1, b) == b
    for b in range(1, b_max + 1):
        if getP(1, b) != Fraction(b, 1):
            raise CertificateError(f"Base condition failed at P(1, {b})={getP(1, b)}")

    # 2. Symmetry P(a, b) == P(b, a) on [1..a_max]^2
    for a in range(1, a_max + 1):
        for b in range(1, a_max + 1):
            if getP(a, b) != getP(b, a):
                raise CertificateError(f"Symmetry failed at ({a}, {b})")

    # 3. Discrete concavity 2 P(a, b) >= P(a, b+1) + P(a, b-1)
    strict_concave_count = 0
    for a in range(1, a_max + 1):
        for b in range(2, b_max):
            lhs = Fraction(2, 1) * getP(a, b)
            rhs = getP(a, b + 1) + getP(a, b - 1)
            if lhs < rhs:
                raise CertificateError(f"Discrete concavity violated at a={a}, b={b}")
            if lhs > rhs:
                strict_concave_count += 1

    # 4. Shifted tripling P(a, 3h + a - 1) >= 3 P(a, h)
    tripling_checks = 0
    zero_slack_triplings = 0
    for a in range(1, a_max + 1):
        h = 1
        while 3 * h + a - 1 <= b_max:
            lhs = getP(a, 3 * h + a - 1)
            rhs = Fraction(3, 1) * getP(a, h)
            if lhs < rhs:
                raise CertificateError(f"Shifted tripling violated at a={a}, h={h}")
            tripling_checks += 1
            if lhs == rhs:
                zero_slack_triplings += 1
            h += 1

    # 5. Lemma 5.1 exact diagonal growth sequence H_a, H_a^3 >= a, D_a^3 >= a^4
    H_seq: List[Fraction] = []
    for a in range(1, a_max + 1):
        Da = getP(a, a)
        Ha = (Fraction(2, 1) * Da) / Fraction(3 * a - 1, 1)
        H_seq.append(Ha)
        if a >= 2:
            if Ha * Fraction(3 * a - 3, 1) < H_seq[a - 2] * Fraction(3 * a - 2, 1):
                raise CertificateError(f"Eq. (5.2) recurrence violated at a={a}")
        if Ha ** 3 < Fraction(a, 1):
            raise CertificateError(f"H_a^3 < a at a={a}")
        if Da ** 3 < Fraction(a ** 4, 1):
            raise CertificateError(f"P(a,a)^3 < a^4 at a={a}")

    # 6. Refutation of supercritical t_refute = p/q > 3/4 at integer witness refute_a >= 2:
    #    a^{4/3} <= (2a - 1)^{1/t} <=> a^{4p} <= (2a - 1)^{3q}, violated when a^{4p} > (2a - 1)^{3q}!
    t_refute = _parse_rat(payload.get("refute_t"), "refute_t")
    if t_refute <= Fraction(3, 4):
        raise CertificateError(f"refute_t must exceed 3/4 to certify finite contradiction, got {t_refute}")
    refute_a = _strict_int(payload.get("refute_a"), "refute_a")
    if refute_a < 2 or refute_a > 1000000:
        raise CertificateError("refute_a out of range [2, 10^6]")
    p_num, q_den = t_refute.numerator, t_refute.denominator
    if q_den > 20 or p_num > 40:
        raise CertificateError("refute_t denominator/numerator exceeds bounded integer power limit")
    if not (refute_a ** (4 * p_num) > (2 * refute_a - 1) ** (3 * q_den)):
        raise CertificateError(f"refute_a={refute_a} does not refute t={t_refute} (a^(4p) <= (2a-1)^(3q))")

    D_last = getP(a_max, a_max)
    H_last = H_seq[-1]
    _check_claimed_rat(payload, "claimed_D_amax", D_last)
    _check_claimed_rat(payload, "claimed_H_amax", H_last)
    _check_claimed_rat(payload, "claimed_D_amax_cube_over_a4", (D_last ** 3) / Fraction(a_max ** 4, 1))
    _check_claimed_int(payload, "claimed_tripling_checks", tripling_checks)
    _check_claimed_int(payload, "claimed_strict_concave_count", strict_concave_count)

    return {
        "verified": True,
        "mode": payload["mode"],
        "cert_id": payload["cert_id"],
        "a_max": a_max,
        "b_max": b_max,
        "D_amax": format_exact_rat(D_last),
        "H_amax": format_exact_rat(H_last),
        "D_amax_cube_over_a4": format_exact_rat((D_last ** 3) / Fraction(a_max ** 4, 1)),
        "tripling_checks": tripling_checks,
        "strict_concave_count": strict_concave_count,
        "refute_t": format_exact_rat(t_refute),
        "refute_a": refute_a,
    }


def verify_certificate(payload: Dict[str, Any]) -> Dict[str, Any]:
    """Verify a parsed STRASSEN-94-CERT-1.0 certificate using exact rational arithmetic."""
    _guard_json_ast(payload)
    if type(payload) is not dict:
        raise CertificateError("Certificate payload must be a JSON object")
    if payload.get("schema") != SCHEMA_VERSION:
        raise CertificateError(f"Invalid schema: expected {SCHEMA_VERSION}")
    cert_id = payload.get("cert_id")
    if type(cert_id) is not str or not cert_id.strip():
        raise CertificateError("cert_id must be a non-empty string")
    mode = payload.get("mode")
    if mode == "prop31_fourier_separation_cert":
        return _verify_mode1(payload)
    if mode == "lemma41_determinant_filtration_cert":
        return _verify_mode2(payload)
    if mode == "lemma42_three_sector_tripling_cert":
        return _verify_mode3(payload)
    if mode == "lemma51_spectral_profile_cert":
        return _verify_mode4(payload)
    raise CertificateError(f"Unknown verification mode: {mode!r}")


def _reject_raw_decimal(token: str) -> Any:
    raise CertificateError(f"IEEE-754 decimal token forbidden: {token}")


def _reject_raw_constant(token: str) -> Any:
    raise CertificateError(f"Non-finite JSON constant forbidden: {token}")


def _reject_dup_keys(pairs: List[Tuple[str, Any]]) -> Dict[str, Any]:
    out: Dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise CertificateError(f"Duplicate JSON object key forbidden: {k!r}")
        out[k] = v
    return out


def verify_certificate_json_text(text: str) -> Dict[str, Any]:
    """Parse raw JSON rejecting all IEEE-754 tokens, NaN/Infinity, and duplicate keys."""
    try:
        payload = json.loads(
            text,
            parse_float=_reject_raw_decimal,
            parse_constant=_reject_raw_constant,
            object_pairs_hook=_reject_dup_keys,
        )
    except CertificateError:
        raise
    except Exception as exc:
        raise CertificateError(f"Malformed JSON: {exc}") from exc
    return verify_certificate(payload)


def verify_certificate_file(path: Path) -> Dict[str, Any]:
    """Read and verify a certificate JSON file from disk."""
    return verify_certificate_json_text(path.read_text(encoding="utf-8"))
