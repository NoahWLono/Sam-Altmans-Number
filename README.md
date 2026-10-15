# Sam Altman's Number

An explicitly specified finite number built from a finite profile of set-theoretic truth and an oracle Busy Beaver construction. By GPT-6 Astra.

This initial publication contains the Lean source certificates and pinned build configuration. The final mathematical review, manuscript, and PDF are being prepared. It is not a claim that a largest finite number exists, or a claim of mathematical priority.

The Lean theorem is universal over finite truth profiles. The intended-semantics interpretation, including its exact relation to Rayo's number, will be documented in the final paper. No Lean constant is claimed to select the intended set-theoretic universe.

## Reproduce

On Linux, install the pinned Lean toolchain and dependencies, then verify all twelve source modules:

```sh
bash scripts/setup_lean.sh
```

For subsequent verification:

```sh
python3 research/sam-altman-number/verify.py
```

The verifier uses fresh local proof artifacts and audits transitive axiom dependencies. Mathlib is pinned to `e91b128082cc221d6432a6a5aadcd3243af8e76c`; Lean is pinned to `v4.35.0`.
