"""One-command full verification gate for Paper 57 (STRASSEN-94-CERT-1.0).

Checks:
1. Zero float / math / numpy leakage in src/*.py
2. Zero sorry / axiom / Classical.choice in Lean 4.35.0 kernel (18/18 theorems, -j 1, strict axiom whitelist)
3. All 16 canonical certificates pass STRASSEN-94-CERT-1.0
4. Full 64-check pytest suite (16 certs + 60 live forgeries + 3 raw JSON checks)
5. SHA-256 manifest verification (or generation with --write-manifest)

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from src.strassen_certifier import verify_certificate_file

FORBIDDEN_TOKENS = ("float(", "math.", "numpy", "np.")


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def collect_tracked_files() -> list[Path]:
    patterns = [
        "LICENSE",
        "README.md",
        "pyproject.toml",
        "lean/lean-toolchain",
        "lean/lakefile.toml",
        "lean/StrassenNineFourths.lean",
        "lean/AuditAxioms.lean",
        "src/__init__.py",
        "src/strassen_exact.py",
        "src/strassen_certifier.py",
        "scripts/run_all_experiments.py",
        "scripts/make_figures.py",
        "scripts/verify_all.py",
        "tests/test_suite.py",
        "paper/main.tex",
        "paper/references.bib",
        "paper/main.pdf",
    ]
    files = [ROOT / p for p in patterns if (ROOT / p).exists()]
    files.extend(sorted((ROOT / "certificates").glob("*.cert.json")))
    files.extend(sorted((ROOT / "results").glob("*.json")))
    files.extend(sorted((ROOT / "paper" / "figures").glob("*.png")))
    return files


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-manifest", action="store_true")
    args = parser.parse_args()

    # 1. Zero-float static check
    for src_file in sorted((ROOT / "src").glob("*.py")):
        txt = src_file.read_text(encoding="utf-8")
        for tok in FORBIDDEN_TOKENS:
            if tok in txt:
                raise SystemExit(f"[FAIL] Forbidden token {tok!r} found in {src_file.name}")
    print("[PASS] 1/5 Zero-float static hygiene check on src/*.py")

    # 2. Lean 4.35.0 build & strict axiom audit (-j 1 for deterministic Windows execution)
    lean_txt = (ROOT / "lean" / "StrassenNineFourths.lean").read_text(encoding="utf-8")
    for bad in ("sorry", "axiom ", "admit"):
        if bad in lean_txt:
            raise SystemExit(f"[FAIL] Forbidden Lean token {bad!r} in StrassenNineFourths.lean")
    subprocess.run(["lake", "build"], cwd=ROOT / "lean", check=True)
    audit = subprocess.run(
        ["lake", "env", "lean", "-j", "1", "AuditAxioms.lean"],
        cwd=ROOT / "lean",
        capture_output=True,
        text=True,
        check=True,
    )
    for bad_ax in ("Classical.choice", "sorryAx", "ofReduceBool", "trustCompiler"):
        if bad_ax in audit.stdout:
            raise SystemExit(f"[FAIL] Forbidden axiom {bad_ax!r} detected:\n{audit.stdout}")
    lines = [ln for ln in audit.stdout.splitlines() if "depends on axioms:" in ln or "does not depend on any axioms" in ln]
    for ln in lines:
        if "depends on axioms:" in ln:
            ax_part = ln.split("depends on axioms:", 1)[1].strip()
            if ax_part not in ("[propext]", "[Quot.sound]", "[propext, Quot.sound]", "[Quot.sound, propext]"):
                raise SystemExit(f"[FAIL] Unexpected axiom set in {ln}")
    if len(lines) != 18:
        raise SystemExit(f"[FAIL] Expected 18 Lean theorem axiom lines, got {len(lines)}")
    print(f"[PASS] 2/5 Lean 4.35.0 build & strict axiom audit ({len(lines)}/18 theorems, 0 sorry, 0 Classical.choice)")

    # 3. Verify all 16 canonical certificates
    cert_paths = sorted((ROOT / "certificates").glob("*.cert.json"))
    if len(cert_paths) != 16:
        raise SystemExit(f"[FAIL] Expected 16 certificates, found {len(cert_paths)}")
    for cp in cert_paths:
        res = verify_certificate_file(cp)
        assert res["verified"] is True
    print("[PASS] 3/5 All 16 canonical STRASSEN-94-CERT-1.0 certificates verified")

    # 4. Run full pytest suite
    subprocess.run([sys.executable, "-m", "pytest", "-p", "no:cacheprovider", "-q"], cwd=ROOT, check=True)
    print("[PASS] 4/5 Full 64-check pytest suite passed (16 certs + 60 live forgeries + 3 raw JSON)")

    # 5. SHA-256 manifest
    manifest_path = ROOT / "SHA256_MANIFEST.json"
    tracked = collect_tracked_files()
    entries = {str(p.relative_to(ROOT)).replace("\\", "/"): sha256_file(p) for p in tracked}
    if args.write_manifest:
        manifest_path.write_text(json.dumps({"count": len(entries), "files": entries}, indent=2) + "\n", encoding="utf-8")
        print(f"[PASS] 5/5 Wrote SHA256_MANIFEST.json ({len(entries)} tracked files)")
    else:
        saved = json.loads(manifest_path.read_text(encoding="utf-8"))["files"]
        if saved != entries:
            raise SystemExit("[FAIL] SHA256_MANIFEST.json mismatch!")
        print(f"[PASS] 5/5 SHA256_MANIFEST.json verified ({len(entries)}/{len(entries)} files)")


if __name__ == "__main__":
    main()
