# Constructive Lean 4 Formalization and Exact-Rational Certificates for OpenAI's omega <= 9/4 Strassen Spectral Profile Proof

Independent, zero-dependency, zero-floating-point formalization and certificate verification stack for OpenAI's October 2, 2026 preprint *"An Upper Bound of 9/4 for the Matrix Multiplication Exponent"*.

- **Author:** Lluis Eriksson
- **Code, Lean 4 proofs & certificates license:** MIT
- **Manuscript & figures license:** CC-BY-4.0
- **Repository:** https://github.com/lluiseriksson/openai-strassen-nine-fourths-certificates

## Highlights

- **Constructive Lean 4.35.0 Kernel (`lean/StrassenNineFourths.lean`):** 18 standalone theorems, 0 `sorry`, 0 `axiom`, 0 `Classical.choice`, 0 warnings (`1` zero-axiom + `17` `[propext, Quot.sound]`), including the **complete universal inductive proof of Lemma 5.1** ($P(a,a)^3 \ge a^4$ for all $a \ge 1$) over a self-contained exact-rational structure `QRat`.
- **Exact-$\mathbb{Q}$ Auditor (`STRASSEN-94-CERT-1.0`):** Pure-stdlib Python `int` + `fractions.Fraction` across 4 modes (`prop31_fourier_separation_cert`, `lemma41_determinant_filtration_cert`, `lemma42_three_sector_tripling_cert`, `lemma51_spectral_profile_cert`), zero floats, strict AST & duplicate-key rejection.
- **Quantitative Tightening:** Proves a $4\times$ tightening of Proposition 3.1's surviving degeneration degree from $(M-1)^2$ to $\lfloor(M-1)/2\rfloor^2$ (degree $0$ at $M=2$) and exact minimal contradiction witnesses $a^*(t)$ ruling out supercritical exponents $\omega = 3t > 9/4$.
- **Canonical Atlas & Red-Team Suite:** 16 canonical certificates (`0.008`–`13.686 ms`), 64/64 pytest checks (16 canonical certs + 60 live adversarial forgeries + 3 raw JSON checks), and 40-file SHA-256 manifest enforcement.

## One-Command Verification

```bash
python scripts/verify_all.py
```
