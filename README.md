# Sam Altman's Number

An explicitly specified finite natural number $S$ satisfying

$$
2^R<S,
$$

where $R$ is Rayo's original number under the intended interpretation of set
theory used in his definition. Author: **GPT-6 Astra**.

Read the [paper](research/sam-altman-number/sam-altmans-number.pdf), its
[LaTeX source](research/sam-altman-number/sam-altmans-number.tex), or the
[detailed package guide](research/sam-altman-number/README.md). The
[twelve Lean modules](research/sam-altman-number/) contain the syntax,
oracle-machine definitions, and proof certificates.

The construction fixes $G=10^{100}$ and a finite family of set-theoretic
formulas with fewer than $G$ symbols, together with their explicit
unique-naming formulas. Their intended truth on natural parameters supplies
an oracle with ordinary truth channels and a cutoff channel. Take the tagged
join of all finite self-halting iterates of that oracle. Then $S$ is one
plus the maximum blank-input output among programs with numerical code below
$2^G$ in the specified oracle language.

A concrete search program, with code `1851571349958786726 < 2^61`, returns
the finite naming boundary $B$. An explicitly coded exponentiation program
amplifies its output to $2^B$ and still has code below `2^2048`. Since every
original Rayo description is covered, $R\leq B$, and the strict output bound
gives $2^R\leq2^B<S$. The hierarchy also has a checked noncollapse property:
no finite stage computes the whole join in this program language.

**Exact formalization scope.** Lean certifies the exponential comparison
for **every** small profile, with no truth or coherence assumption. It also
checks finite support, token-preserving normalization, explicit logical
uniqueness, program evaluation, and the witness code bounds. The paper
constructs the intended profile using finitely many Separation instances,
one for each fixed formula, and proves the intended-semantics application.
Lean does not choose the intended universe or supply a closed term selecting
its truth profile. No identification of that universe with Mathlib's `ZFSet`
model is used.

The strongest arithmetic declaration is
[`SamAltmanResearch.GrowthCertificate.exponential_boundary_lt_samAltman`](research/sam-altman-number/GrowthCertificate.lean).
The [finite-support certificate](research/sam-altman-number/ProfileSupport.lean)
proves that only the stated finite family matters. The
[review record](research/sam-altman-number/REVIEW.md) and
[prior-art assessment](research/sam-altman-number/PRIOR-ART.md) explain the
scope of the result and its relation to earlier work.

From a clone of this repository on Linux, with Bash, Git, curl, and Python 3
available, install the pinned Lean toolchain, fetch the Mathlib cache, and
verify all twelve modules:

```sh
bash scripts/setup_lean.sh
```

For later verification runs:

```sh
python3 research/sam-altman-number/verify.py
```

The verifier rebuilds the package's Lean artifacts in a fresh temporary
directory and audits the principal declarations' transitive axiom dependencies
against `propext`, `Classical.choice`, and `Quot.sound`. It rejects proof
placeholders, custom axioms, and `native_decide`. It does not evaluate the
intended truth profile or compute the digits of $S$.

To rebuild the paper on Linux x86_64:

```sh
bash scripts/setup_tex.sh
.tools/tectonic/tectonic --keep-logs --outdir research/sam-altman-number research/sam-altman-number/sam-altmans-number.tex
```

The dependency pins are Lean **4.35.0**, Mathlib
`e91b128082cc221d6432a6a5aadcd3243af8e76c`, and Tectonic **0.17.0**.
The [provenance record](research/sam-altman-number/provenance.json) and
[publication checksums](research/sam-altman-number/SHA256SUMS) identify the
sources and exported artifacts. From the repository root, check the published
files with `sha256sum -c research/sam-altman-number/SHA256SUMS`. Run that check
before rebuilding, since verification timestamps and PDF metadata can change.
TeX package resolution can also change PDF bytes, so byte-identical PDF
rebuilding is not claimed.

This particular definition and its proof package combine established
methods from logic and computability. They carry no claim of mathematical
priority, a world record, or a largest finite number.
