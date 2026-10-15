# Sam Altman's Number

This package specifies a finite natural number using a fixed profile of
set-theoretic formulas, a hierarchy of oracle computations, and a Busy Beaver
output bound. The [paper](sam-altmans-number.pdf), with
[LaTeX source](sam-altmans-number.tex), gives the intended-semantics
construction and proves the comparison

$$
2^R \leq 2^B < S,
$$

where $R$ is Rayo's original benchmark, $B$ is the least strict bound
for the finite scoped naming collection, and $S$ is Sam Altman's Number.
The concrete search witness has code `1851571349958786726 < 2^61`. A second
program computes two to the power of its output and has code below `2^2048`.

**Formalization boundary.** Lean proves the comparison uniformly for every
profile of the required small type, including profiles that do not represent
truth. Its strongest arithmetic certificate is $2^B<S$ for every such
profile. It also checks formula normalization, finite support, and an explicit
first-order derivation of uniqueness. The paper supplies the intended profile
by finitely many Separation instances, one for each fixed formula, using the
intended interpretation assumed in
[Rayo's own account](https://web.mit.edu/arayo/www/bignums.html). It then proves
the application of the uniform theorem to that profile. Lean does not select
the intended universe $V$, and the package contains no closed Lean term
asserted to select this intended profile. The `ZFSet` instance checks the
definitions in a concrete model; no equality or identification of $V$
with `ZFSet` is assumed.

This distinction is part of the result's specification. The mathematical
construction uses intended truth directly. Its Lean certificate is a
universal theorem that can be applied to the finitely supported intended
profile, rather than a choice of a model to stand in for that interpretation.

The definition fixes $G=10^{100}$. Let $D_G$ be the finite collection
of scoped formulas with one available variable and fewer than $G$ symbols.
For each formula $p$, `unique p` asserts that the supplied object satisfies
$p$ and is its only satisfying object among all sets. The required support
is exactly

$$
F_G=D_G\cup\{\operatorname{unique}(p):p\in D_G\}.
$$

For each fixed $q\in F_G$, Separation forms the subset of standard
naturals whose finite von Neumann ordinals satisfy that literal formula in
the intended universe. The finite tagged collection of these rows is the
profile. Values outside the support can be set to false without changing
either $B$ or $S$. No uniform truth predicate for arbitrary
set-theoretic formulas is required by this finite construction.

The base oracle has a cutoff channel and ordinary truth channels. Channel
zero answers whether every admitted named natural lies below the queried
candidate; the other valid channels answer the individual formulas in the
fixed ordered description list. Those truth channels retain ordinary
satisfaction, including formulas that name no unique object. For arbitrary
profiles, admission explicitly requires a unique true natural entry for
`unique p`; the syntactic uniqueness proof makes that guard automatic for
the intended profile. The oracle definition receives the profile and the
fixed budget, not a numerical Rayo value.

Starting with this base, take its self-halting oracle, then the self-halting
oracle of that oracle, and continue through every finite stage. The tagged
join contains them all, with stage zero equal to the base. The checked
diagonal theorem proves that no finite stage computes the whole join in the
specified program language. No equivalence with an external Turing-machine
model or standard jump notation is asserted.

Finally, $S$ is one plus the maximum output on blank input over all
encoded programs with numerical code below $2^G$, using this join oracle.
Invalid and divergent codes contribute zero only when forming that finite
maximum; their evaluator remains partial. The 61-bit witness searches the
cutoff channel and returns $B$. The amplification program composes this
search with an explicitly coded primitive-recursive program for $n\mapsto2^n$.
Its code is below $2^{2048}$, and $2048\leq G$, so $2^B<S$ at the
already fixed budget. Token-preserving translation covers every original
Rayo description and gives $R\leq B$, hence $2^R\leq2^B<S$. The proof
does not require equality of the raw and scoped naming collections.

The thirteen Lean modules have the following roles, in verification order:

| Module | Content |
|---|---|
| [FormulaSemantics.lean](FormulaSemantics.lean) | Raw and scoped syntax, token-preserving translation, compositional semantics, unique naming, and finite naming bounds. |
| [OracleMachine.lean](OracleMachine.lean) | Encoded oracle programs, decoding, partial evaluation, strict Busy Beaver bounds, and self-halting diagonalization. |
| [BoundedTruth.lean](BoundedTruth.lean) | Explicit logical expansions, the `unique` formula, ordered description enumeration, and literal finite upper-bound formulas. |
| [NaturalFormula.lean](NaturalFormula.lean) | A 150-symbol natural-number formula and its exact characterization of finite von Neumann ordinals in `ZFSet`. |
| [OracleSearch.lean](OracleSearch.lean) | Executable least-witness search programs and their numerical code bounds. |
| [FormulaOracle.lean](FormulaOracle.lean) | Pure formula query selection, cutoff semantics, and a concrete model validation. |
| [OracleHierarchy.lean](OracleHierarchy.lean) | Finite self-halting iteration, its join, and noncomputability of that join in every finite stage. |
| [Candidate.lean](Candidate.lean) | The 61-bit witness, the original raw-language benchmark in arbitrary structures, and a model comparison. |
| [FiniteProfile.lean](FiniteProfile.lean) | Admission, cutoff, base oracle, and comparison uniformly over every profile. |
| [ProfileSupport.lean](ProfileSupport.lean) | Exact finite support, invariance under restriction, and the fixed `samAltman` construction. |
| [FOLDerivation.lean](FOLDerivation.lean) | An explicit first-order proof calculus, soundness, uniqueness, and bound-clause derivations. |
| [GrowthCertificate.lean](GrowthCertificate.lean) | Explicit addition, doubling, and exponentiation programs; an amplification witness below `2^2048`; and the uniform bound $2^B<S$. |
| [OriginalBenchmark.lean](OriginalBenchmark.lean) | Exact original-language benchmark for every profile, its leastness and semantic alignment, and direct strict and exponential comparisons with `samAltman`. |

The principal final declarations are:

- `SamAltmanResearch.OriginalBenchmark.exponential_originalRayo_lt_samAltman`: directly proves `2 ^ originalRayo T googol < samAltman T` for every profile.
- `SamAltmanResearch.OriginalBenchmark.originalRayo_isLeast`: the exact least-strict-bound specification over original surface-language descriptions.
- `SamAltmanResearch.OriginalBenchmark.originalRayo_semanticProfile`: exact equality with the independently defined assignment-based raw benchmark in every injectively represented type-carrier structure.
- `SamAltmanResearch.GrowthCertificate.exponential_boundary_lt_samAltman`:
  the stronger inequality $2^B<S$ for every profile at the fixed googol budget.
- `SamAltmanResearch.FiniteProfile.samAltman_comparison`: the strict comparison
  for every profile after restriction to the fixed support.
- `SamAltmanResearch.FiniteProfile.restrict_number`: restriction to
  `descriptions budget ∪ (descriptions budget).image unique` preserves the number.
- `SamAltmanResearch.FiniteProfile.rawRayo_lt_samAltman`: alignment with the
  raw naming benchmark in every type-carrier structure with an injective
  representation of naturals.
- `SamAltmanResearch.Formula.Derivation.unique_same`: an object-language
  derivation that two objects satisfying `unique p` are equal.

From the repository root on Linux, install the pinned Lean toolchain, fetch
the Mathlib cache, and run verification with:

```sh
bash scripts/setup_lean.sh
```

For subsequent certificate checks, run:

```sh
python3 research/sam-altman-number/verify.py
```

On Linux x86_64, install Tectonic 0.17.0 and compile the paper with:

```sh
bash scripts/setup_tex.sh
.tools/tectonic/tectonic --keep-logs --outdir research/sam-altman-number research/sam-altman-number/sam-altmans-number.tex
```

[verify.py](verify.py) compiles all thirteen modules in dependency order with
one Lean worker. Each run uses a fresh temporary directory for the package's
compiled modules, so verification does not reuse their old `.olean` files.
The script rejects proof placeholders, custom axioms, `native_decide`, and
other prohibited proof bypasses. It checks the printed transitive axiom
dependencies of the audited declarations against `propext`,
`Classical.choice`, and `Quot.sound`, and writes per-module logs plus
[verification.json](verification.json). It does not compute $S$ or
evaluate intended set-theoretic truth.

Lean is pinned to **4.35.0** and Mathlib to
`e91b128082cc221d6432a6a5aadcd3243af8e76c` in the repository toolchain and
manifest. The [repository root README](../../README.md) describes local tooling setup.
[provenance.json](provenance.json) records source and compiler provenance;
[SHA256SUMS](SHA256SUMS) records the publication files.
TeX package resolution can affect PDF bytes, so byte-identical PDF rebuilding
is not claimed. [REVIEW.md](REVIEW.md) records mathematical and statement
alignment review, its scope, and its findings.

The contribution is the explicit specification and accompanying certificates
for this particular construction. Oracle Busy Beaver hierarchies and
extensions of Rayo-style naming have substantial prior art, detailed in
[PRIOR-ART.md](PRIOR-ART.md). No priority claim, world record, comparison with
every other googological number, or solution of an open number theory
problem is claimed.
