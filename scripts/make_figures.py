"""Generate 3 publication-quality 300-DPI figures for Paper 57 (STRASSEN-94-CERT-1.0).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
RES_DIR = ROOT / "results"
FIG_DIR = ROOT / "paper" / "figures"

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 8.5,
    "axes.titlesize": 9.0,
    "axes.labelsize": 8.5,
    "xtick.labelsize": 7.8,
    "ytick.labelsize": 7.8,
    "legend.fontsize": 7.0,
    "axes.spines.top": False,
    "axes.spines.right": False,
})


def make_fig1() -> None:
    d2 = json.loads((RES_DIR / "exp2_lemma51_diagonal_growth.json").read_text(encoding="utf-8"))
    d4 = json.loads((RES_DIR / "exp4_exponent_refutation_thresholds.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.2, 2.75), dpi=300)

    rows = d2["rows"]
    as_ = [r["a"] for r in rows]
    ax1.loglog(as_, [r["upper_9_4_val"] for r in rows], "--", color="#c0392b", lw=1.5, label=r"Interp. ceiling $(2a{-}1)^{4/3}$ ($t{=}3/4$)")
    ax1.loglog(as_, [r["D_lb_val"] for r in rows], "o-", color="#1b4f72", lw=1.7, ms=3.5, label=r"Lem. 5.1 exact floor $D_{\mathrm{lb}}(a)$")
    ax1.loglog(as_, [r["a_4_3_val"] for r in rows], ":", color="#117864", lw=1.6, label=r"Asymptotic $a^{4/3}$ ($\omega \leq 9/4$)")
    ax1.set_xlabel(r"Diagonal degree parameter $a$")
    ax1.set_ylabel(r"Spectral profile $P(a,a)$ (log)")
    ax1.set_title(r"(a) Universal Lem. 5.1 Growth $a^{4/3} \leq P(a,a)$")
    ax1.grid(True, which="both", alpha=0.22)
    ax1.legend(loc="upper left", frameon=True, framealpha=0.94, fontsize=6.5)

    r4 = d4["rows"]
    oms = [r["omega_val"] for r in r4]
    mins = [r["min_refute_a"] for r in r4]
    ax2.semilogy(oms, mins, "s-", color="#7d3c98", lw=1.8, ms=5.0, label=r"Exact minimal witness $a^*(t)$")
    ax2.axvline(2.25, color="#c0392b", ls="-.", lw=1.3, label=r"Asymptotic barrier $\omega = 9/4$")
    for om, mn, rr in zip(oms, mins, r4):
        ax2.annotate(f"{mn:,}", xy=(om, mn), xytext=(om + 0.02, mn * 1.35), fontsize=6.6, color="#4a235a")
    ax2.set_xlim(2.20, 3.18)
    ax2.set_ylim(4, 2.0e6)
    ax2.set_xlabel(r"Tested supercritical exponent $\omega = 3t > 9/4$")
    ax2.set_ylabel(r"Minimal contradiction $a^*(t)$ (log)")
    ax2.set_title(r"(b) Exact Finite Contradiction $a^{4p} > (2a{-}1)^{3q}$")
    ax2.grid(True, which="both", alpha=0.22)
    ax2.legend(loc="upper right", frameon=True, framealpha=0.94, fontsize=6.6)

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig1_lemma51_growth_and_refutation.png", dpi=300)
    plt.close(fig)


def make_fig2() -> None:
    d3 = json.loads((RES_DIR / "exp3_prop31_and_lem42_scaling.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.2, 2.75), dpi=300)

    p31 = d3["prop31"]
    Ms = [r["M"] for r in p31]
    ax1.plot(Ms, [r["paper_degree_bound"] for r in p31], "s--", color="#c0392b", lw=1.5, ms=4.2, label=r"Preprint bound $(M{-}1)^2$")
    ax1.plot(Ms, [r["actual_max_weight"] for r in p31], "o-", color="#1b4f72", lw=1.8, ms=4.5, label=r"Exact tight degree $\lfloor(M{-}1)/2\rfloor^2$")
    ax1.fill_between(Ms, [r["actual_max_weight"] for r in p31], [r["paper_degree_bound"] for r in p31], color="#aed6f1", alpha=0.35, label=r"$4\times$ degree tightening")
    ax1.set_xlabel(r"Block multiplicity $M$ ($L = 5M$)")
    ax1.set_ylabel("Max surviving degeneration degree")
    ax1.set_title(r"(a) Prop. 3.1 Exact Mismatch Degree Tightening")
    ax1.grid(True, alpha=0.25)
    ax1.legend(loc="upper left", frameon=True, framealpha=0.94, fontsize=6.8)

    l42 = d3["lem42"]
    as_ = [r["a"] for r in l42]
    effs = [r["survival_ratio_val"] for r in l42]
    ax2.plot(as_, effs, "o-", color="#117864", lw=1.8, ms=4.8, label=r"Diagonal $3a^2 / [a(4a{-}1)]$")
    ax2.axhline(0.75, color="#c0392b", ls="--", lw=1.3, label=r"Asymptotic limit $3/4 = 0.75$")
    ax2.set_ylim(0.73, 0.87)
    ax2.set_xlabel(r"Diagonal parameter $a = h$ ($B = 4a - 1$)")
    ax2.set_ylabel("Weight-0 surviving fraction")
    ax2.set_title(r"(b) Lem. 4.2 Three-Sector Survival Efficiency")
    ax2.grid(True, alpha=0.25)
    ax2.legend(loc="upper right", frameon=True, framealpha=0.94, fontsize=6.8)

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig2_prop31_and_lem42.png", dpi=300)
    plt.close(fig)


def make_fig3() -> None:
    d1 = json.loads((RES_DIR / "exp1_certificate_atlas.json").read_text(encoding="utf-8"))
    d2 = json.loads((RES_DIR / "exp2_lemma51_diagonal_growth.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.2, 2.75), dpi=300)

    rows = d1["certificates"]
    mode_map = {
        "prop31_fourier_separation_cert": ("M1: Prop. 3.1", "#1b4f72"),
        "lemma41_determinant_filtration_cert": ("M2: Lem. 4.1", "#117864"),
        "lemma42_three_sector_tripling_cert": ("M3: Lem. 4.2", "#b9770e"),
        "lemma51_spectral_profile_cert": ("M4: Lem. 5.1", "#7d3c98"),
    }
    xs = np.arange(len(rows))
    ms = [r["mean_ms"] for r in rows]
    cols = [mode_map[r["mode"]][1] for r in rows]
    ax1.bar(xs, ms, color=cols, edgecolor="#1c2833", lw=0.5, width=0.68)
    ax1.set_yscale("log")
    ax1.set_xticks(xs)
    ax1.set_xticklabels([f"{i+1}" for i in range(len(rows))], fontsize=7.0)
    ax1.set_ylim(0.004, max(ms) * 6.0)
    ax1.set_ylabel("Mean verify time (ms, log)")
    ax1.set_xlabel("Canonical certificate index (1–16)")
    ax1.set_title(r"(a) Exact-$\mathbb{Q}$ Auditor Runtime (16 Certs)")
    from matplotlib.patches import Patch
    handles = [Patch(facecolor=c, edgecolor="#1c2833", label=lbl) for lbl, c in mode_map.values()]
    ax1.legend(handles=handles, loc="upper left", ncol=2, frameon=True, framealpha=0.94, fontsize=6.4)
    ax1.grid(True, which="both", axis="y", alpha=0.25)

    r2 = d2["rows"]
    as_ = [r["a"] for r in r2]
    ax2.plot(as_, [r["H_lb_cube_over_a_val"] for r in r2], "o-", color="#1b4f72", lw=1.7, ms=3.6, label=r"$H_{\mathrm{lb}}(a)^3 / a \geq 1$")
    ax2.plot(as_, [r["D_lb_cube_over_a4_val"] for r in r2], "s--", color="#117864", lw=1.5, ms=3.4, label=r"$D_{\mathrm{lb}}(a)^3 / a^4 \geq 1$")
    ax2.axhline(1.0, color="#c0392b", ls=":", lw=1.2, label="Lean Thm. 16–17 lower bound 1")
    ax2.set_xticks([1, 5, 10, 15, 20])
    ax2.set_xlabel(r"Diagonal index $a \in \{1,\dots,20\}$")
    ax2.set_ylabel("Exact rational overshoot ratio")
    ax2.set_title(r"(b) Exact Margin Above $H_a^3 \geq a$ and $D_a^3 \geq a^4$")
    ax2.grid(True, alpha=0.25)
    ax2.legend(loc="center right", bbox_to_anchor=(0.98, 0.44), frameon=True, framealpha=0.94, fontsize=6.5)

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig3_atlas_and_margins.png", dpi=300)
    plt.close(fig)


def main() -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    make_fig1()
    make_fig2()
    make_fig3()
    print("[PASS] Generated 3 publication-quality 300-DPI figures in paper/figures/.")


if __name__ == "__main__":
    main()
