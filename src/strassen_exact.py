"""Pure-stdlib exact integer/rational engine for Paper 57 (OpenAI, Oct. 2, 2026,
"An Upper Bound of 9/4 for the Matrix Multiplication Exponent"): STRASSEN-94-CERT-1.0.

Zero floating-point arithmetic: uses Python int and fractions.Fraction exclusively.

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

MAX_RAT_LEN = 2000


def parse_exact_rat(val: object, label: str = "rational") -> Fraction:
    """Parse a canonical ASCII integer or reduced 'p/q' rational string (zero floats)."""
    if isinstance(val, bool) or isinstance(val, int) or not isinstance(val, str):
        raise ValueError(f"{label}: expected canonical rational string, got {type(val).__name__}")
    s = val
    if not s or len(s) > MAX_RAT_LEN or s != s.strip():
        raise ValueError(f"{label}: invalid rational length or whitespace")
    if s in ("-0", "+0") or s.startswith("+"):
        raise ValueError(f"{label}: non-canonical sign in '{s}'")
    neg = s.startswith("-")
    body = s[1:] if neg else s
    if "/" in body:
        parts = body.split("/")
        if len(parts) != 2:
            raise ValueError(f"{label}: multiple '/' in '{s}'")
        num_s, den_s = parts
        if not (num_s and num_s.isascii() and num_s.isdigit()):
            raise ValueError(f"{label}: non-ASCII/non-digit numerator in '{s}'")
        if not (den_s and den_s.isascii() and den_s.isdigit()):
            raise ValueError(f"{label}: non-ASCII/non-digit denominator in '{s}'")
        if (len(num_s) > 1 and num_s.startswith("0")) or den_s.startswith("0"):
            raise ValueError(f"{label}: leading zero in '{s}'")
        num = int(num_s)
        den = int(den_s)
        if den <= 1:
            raise ValueError(f"{label}: denominator must be >= 2 in fraction '{s}'")
        if num == 0:
            raise ValueError(f"{label}: zero must be formatted as '0', got '{s}'")
        frac = Fraction(-num if neg else num, den)
        if frac.denominator != den:
            raise ValueError(f"{label}: fraction '{s}' is not in lowest terms")
        return frac
    if not (body and body.isascii() and body.isdigit()):
        raise ValueError(f"{label}: non-ASCII/non-digit integer in '{s}'")
    if len(body) > 1 and body.startswith("0"):
        raise ValueError(f"{label}: leading zero in '{s}'")
    num = int(body)
    if num == 0 and neg:
        raise ValueError(f"{label}: negative zero forbidden")
    return Fraction(-num if neg else num, 1)


def format_exact_rat(q: Fraction) -> str:
    """Format a Fraction as a canonical integer or lowest-terms 'p/q' string."""
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


# --- Mode 1: Proposition 3.1 (5M -> M Fourier separation & squared mismatch) ---


def audit_prop31_separation(M: int) -> Dict[str, int]:
    """Exhaustively audit all M^4 tuples (g, h, u, v) in [1..M]^4 for Prop. 3.1."""
    L = 5 * M
    max_abs_phase = 0
    surviving_count = 0
    weight_zero_count = 0
    actual_max_weight = 0
    for g in range(1, M + 1):
        for h in range(1, M + 1):
            for u in range(1, M + 1):
                for v in range(1, M + 1):
                    phase = u - v + 2 * (g - h)
                    ap = abs(phase)
                    if ap > max_abs_phase:
                        max_abs_phase = ap
                    if not (ap <= 3 * (M - 1) < L):
                        raise ValueError("Prop. 3.1 modulus no-wrap violated")
                    if phase % L == 0:
                        if phase != 0:
                            raise ValueError("Nonzero phase wrapped mod 5M")
                        surviving_count += 1
                        w = g * g + (h * u - h * h) + (-h * v)
                        if w != (g - h) * (g - h) or w < 0:
                            raise ValueError("Prop. 3.1 squared-mismatch weight identity failed")
                        if w > actual_max_weight:
                            actual_max_weight = w
                        if w == 0:
                            if not (g == h and u == v):
                                raise ValueError("Weight-zero term outside diagonal g=h, u=v")
                            weight_zero_count += 1
                        elif g == h and u == v:
                            raise ValueError("Diagonal term had nonzero weight")
    return {
        "L": L,
        "max_abs_phase": max_abs_phase,
        "surviving_count": surviving_count,
        "weight_zero_count": weight_zero_count,
        "actual_max_weight": actual_max_weight,
        "paper_degree_bound": (M - 1) * (M - 1),
    }


# --- Mode 2: Lemma 4.1 Determinant Filtration exact matrix factorization ---


def _filtration_basis_matrix(e: int) -> List[List[Fraction]]:
    """Return 2(e+1) x 2(e+1) change-of-basis matrix B_e expressing Lemma 4.1 basis
    (quotient lifts q_0..q_{e+1}, kernel k_0..k_{e-1}) in the standard monomial basis
    [u^e s, u^{e-1} v s, ..., v^e s, u^e w, u^{e-1} v w, ..., v^e w].
    Columns are the Lemma 4.1 basis vectors.
    """
    dim = 2 * (e + 1)
    B = [[Fraction(0, 1) for _ in range(dim)] for _ in range(dim)]
    # Quotient lifts:
    # col i (0 <= i <= e): u^{e-i} v^i s -> row i
    for i in range(e + 1):
        B[i][i] = Fraction(1, 1)
    # col e+1: v^e w -> row (e+1) + e = 2e + 1
    B[2 * e + 1][e + 1] = Fraction(1, 1)
    # Kernel basis: col (e + 2) + j (0 <= j < e): D u^{e-1-j} v^j = (uw - vs) u^{e-1-j} v^j
    # = u^{e-j} v^j w (row (e+1) + j) - u^{e-1-j} v^{j+1} s (row j + 1)
    for j in range(e):
        col = (e + 2) + j
        B[(e + 1) + j][col] = Fraction(1, 1)
        B[j + 1][col] = Fraction(-1, 1)
    return B


def _invert_exact_matrix(A: Sequence[Sequence[Fraction]]) -> List[List[Fraction]]:
    """Exact Gauss-Jordan matrix inversion over Q."""
    n = len(A)
    aug = [list(A[i]) + [Fraction(1 if i == j else 0, 1) for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if aug[r][col] != 0:
                piv = r
                break
        if piv is None:
            raise ValueError("Singular matrix in exact Q inversion")
        aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        aug[col] = [x / pv for x in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != 0:
                fac = aug[r][col]
                aug[r] = [aug[r][c] - fac * aug[col][c] for c in range(2 * n)]
    return [row[n:] for row in aug]


def _mat_mul(A: Sequence[Sequence[Fraction]], B: Sequence[Sequence[Fraction]]) -> List[List[Fraction]]:
    m, k, n = len(A), len(B), len(B[0])
    out = [[Fraction(0, 1) for _ in range(n)] for _ in range(m)]
    for i in range(m):
        for j in range(n):
            s = Fraction(0, 1)
            for t in range(k):
                if A[i][t] != 0 and B[t][j] != 0:
                    s += A[i][t] * B[t][j]
            out[i][j] = s
    return out


def audit_lemma41_filtration(a: int, b: int) -> Dict[str, int]:
    """Construct exact Lemma 4.1 multiplication slices for C(a, b) (x) B_X(2) over Q
    and verify block-lower-triangular form [[M_f^+, 0], [*, M_f^-]] for all f in V_{a-1}.
    """
    e_in = b - 1
    e_out = a + b - 2
    B_in = _filtration_basis_matrix(e_in)
    B_out = _filtration_basis_matrix(e_out)
    B_out_inv = _invert_exact_matrix(B_out)

    dim_in = 2 * (e_in + 1)
    dim_out = 2 * (e_out + 1)
    q_in = e_in + 2
    k_in = e_in
    q_out = e_out + 2
    k_out = e_out

    upper_right_nnz = 0
    cross_block_nnz = 0
    diag_plus_nnz = 0
    diag_minus_nnz = 0

    # For each monomial f_r = u^{a-1-r} v^r (0 <= r < a) in V_{a-1}:
    for r in range(a):
        # Standard basis multiplication matrix S_r: maps u^{e_in - i} v^i s -> u^{e_out - (i+r)} v^{i+r} s
        # and u^{e_in - i} v^i w -> u^{e_out - (i+r)} v^{i+r} w
        S_r = [[Fraction(0, 1) for _ in range(dim_in)] for _ in range(dim_out)]
        for i in range(e_in + 1):
            S_r[i + r][i] = Fraction(1, 1)
            S_r[(e_out + 1) + (i + r)][(e_in + 1) + i] = Fraction(1, 1)
        # Transform to Lemma 4.1 basis: M_r = B_out^{-1} S_r B_in
        M_r = _mat_mul(B_out_inv, _mat_mul(S_r, B_in))

        # 1. Verify upper-right block [0..q_out-1][q_in..dim_in-1] is identically zero
        for i in range(q_out):
            for j in range(q_in, dim_in):
                if M_r[i][j] != 0:
                    upper_right_nnz += 1
                    raise ValueError(f"Nonzero entry in upper-right block at r={r}, ({i},{j})")

        # 2. Verify upper-left block M_f^+ equals C(a, b+1) multiplication V_b -> V_{a+b-1}
        for i in range(q_out):
            for j in range(q_in):
                expected = Fraction(1, 1) if i == j + r else Fraction(0, 1)
                if M_r[i][j] != expected:
                    raise ValueError(f"Upper-left block M_f^+ mismatch at r={r}, ({i},{j})")
                if expected != 0:
                    diag_plus_nnz += 1

        # 3. Verify lower-right block M_f^- equals C(a, b-1) multiplication V_{b-2} -> V_{a+b-3}
        for i in range(k_out):
            for j in range(k_in):
                expected = Fraction(1, 1) if i == j + r else Fraction(0, 1)
                if M_r[q_out + i][q_in + j] != expected:
                    raise ValueError(f"Lower-right block M_f^- mismatch at r={r}, ({i},{j})")
                if expected != 0:
                    diag_minus_nnz += 1

        # 4. Count lower-left cross block '*' (weight +1 terms eliminated by degeneration)
        for i in range(k_out):
            for j in range(q_in):
                if M_r[q_out + i][j] != 0:
                    cross_block_nnz += 1

    return {
        "in_dim": dim_in,
        "out_dim": dim_out,
        "quot_in_dim": q_in,
        "ker_in_dim": k_in,
        "quot_out_dim": q_out,
        "ker_out_dim": k_out,
        "upper_right_nnz": upper_right_nnz,
        "cross_block_nnz": cross_block_nnz,
        "diag_plus_nnz": diag_plus_nnz,
        "diag_minus_nnz": diag_minus_nnz,
    }


# --- Mode 3: Lemma 4.2 Three-Sector Shifted Tripling ---


def audit_lemma42_three_sectors(a: int, h: int) -> Dict[str, int]:
    """Exhaustively audit all a*(3h + a - 1) supported terms of C(a, 3h + a - 1)."""
    B = 3 * h + a - 1
    w0_left = 0
    w0_mid = 0
    w0_right = 0
    dropped_w1 = 0
    neg_count = 0
    mid_terms = set()

    for x in range(a):
        for y in range(B):
            z = x + y
            wy = 1 if (h <= y <= 2 * h + a - 2) else 0
            wz = -1 if (h + a - 1 <= z <= 2 * h + a - 2) else 0
            w = wy + wz
            if w < 0:
                neg_count += 1
            elif w == 0:
                if y <= h - 1 and z <= h + a - 2:
                    w0_left += 1
                elif h <= y <= 2 * h + a - 2 and h + a - 1 <= z <= 2 * h + a - 2:
                    w0_mid += 1
                    mid_terms.add((x, y, z))
                elif y >= 2 * h + a - 1 and z >= 2 * h + a - 1:
                    w0_right += 1
                else:
                    raise ValueError(f"Weight-0 term ({x},{y},{z}) outside three matched sectors")
            elif w == 1:
                dropped_w1 += 1
            else:
                raise ValueError(f"Unexpected weight {w}")

    # Verify exact middle-branch reversal bijection: (u, r) -> (a-1-u, h+u+r, h+a-1+r)
    bijection_terms = set()
    for u in range(a):
        for r in range(h):
            bijection_terms.add((a - 1 - u, h + u + r, h + a - 1 + r))
    if bijection_terms != mid_terms:
        raise ValueError("Middle-branch reversal bijection mismatch")

    return {
        "B": B,
        "total_terms": a * B,
        "w0_left": w0_left,
        "w0_mid": w0_mid,
        "w0_right": w0_right,
        "dropped_w1": dropped_w1,
        "neg_count": neg_count,
    }
