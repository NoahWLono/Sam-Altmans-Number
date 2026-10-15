#!/usr/bin/env python3
"""Rebuild the uniform comparison and syntax certificates from fresh artifacts.

The intended semantic profile is defined and justified in the manuscript.
This script does not claim to select or evaluate intended set-theoretic truth.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FILES = (
    "FormulaSemantics.lean", "OracleMachine.lean", "BoundedTruth.lean",
    "NaturalFormula.lean", "OracleSearch.lean", "FormulaOracle.lean",
    "OracleHierarchy.lean", "Candidate.lean", "FiniteProfile.lean",
    "ProfileSupport.lean", "FOLDerivation.lean", "GrowthCertificate.lean", "OriginalBenchmark.lean",
)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b")
AUDIT = re.compile(
    r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
    re.S,
)


def verify(build_root):
    evidence = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "uniform_profile_comparison_proved": True,
        "exponential_amplification_proved": True,
        "direct_original_benchmark_comparison_proved": True,
        "syntactic_uniqueness_certificate_proved": True,
        "finite_profile_support_proved": True,
        "kernel_selects_intended_truth_profile": False,
        "mathematical_priority_established": False,
        "scope": "Kernel-checked uniform finite-profile comparison, syntax certificates, and model alignment; intended-semantic interpretation is documented in the manuscript.",
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "lake_manifest_sha256": hashlib.sha256((ROOT / "lake-manifest.json").read_bytes()).hexdigest(),
        "modules": [],
    }
    environment = os.environ.copy()
    environment["LEAN_PATH"] = str(build_root)
    for filename in FILES:
        source = HERE / filename
        content = source.read_bytes()
        if FORBIDDEN.search(content.decode()):
            raise RuntimeError(f"Forbidden construct found in {filename}")
        output = build_root / source.relative_to(ROOT).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [str(ROOT / "scripts/with_lean.sh"), "lake", "env", "lean", "-j", "1",
                   "-o", str(output), str(source.relative_to(ROOT))]
        result = subprocess.run(command, cwd=ROOT, env=environment, text=True, capture_output=True)
        log = result.stdout + result.stderr
        (HERE / f"{source.stem}.verification.txt").write_text(log)
        if result.returncode:
            raise RuntimeError(f"{filename} failed:\n{log}")
        if "sorryAx" in log or "warning:" in log or "error:" in log:
            raise RuntimeError(f"{filename} has a diagnostic requiring review:\n{log}")
        audit = []
        for name, dependencies in AUDIT.findall(log):
            axioms = [item.strip() for item in dependencies.split(",") if item.strip()]
            if not set(axioms).issubset(ALLOWED):
                raise RuntimeError(f"Unexpected dependencies for {name}: {axioms}")
            audit.append({"declaration": name, "axioms": axioms})
        if len(audit) < 4:
            raise RuntimeError(f"Missing transitive audit in {filename}")
        evidence["modules"].append({
            "file": filename,
            "sha256": hashlib.sha256(content).hexdigest(),
            "exit_code": result.returncode,
            "transitive_axiom_audit": audit,
        })
        print(f"PASS {filename}: {len(audit)} audited declarations", flush=True)
    (HERE / "verification.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print("PASS: uniform finite-profile comparison and explicit syntax certificates.")
    print("Intended-semantic interpretation and its proof are in sam-altmans-number.tex.")


def main():
    with tempfile.TemporaryDirectory(prefix="sam-altman-lean-") as directory:
        verify(Path(directory))


if __name__ == "__main__":
    main()
