# Prior-art assessment for the proposed Sam Altman number

Reviewed 15 October 2026. This is a focused source review of the construction
in `FiniteProfile.lean`, `OracleHierarchy.lean`, and `Candidate.lean`. It does
not establish priority, certify the intended-universe semantic argument, or
compare the resulting number numerically with every published googological
construction.

The reasonable claim is that this project specifies a particular number by
an explicit combination of established methods and supplies machine-checked
certificates for its finite-profile comparison and concrete oracle programs.
The methods have substantial precedents. An assertion that the exact
combination has never appeared before would require more evidence than this
review provides.

The inspected construction fixes a googol description budget and a googol
program-bit budget. Its base oracle contains a cutoff predicate derived from
a finite family of descriptions, together with individual truth channels.
It then takes the tagged join of all finite iterations of its own
self-halting operator and a strict Busy Beaver output bound for the encoded
oracle language. A particular program with code
`1851571349958786726 < 2^61` retrieves the finite-profile boundary. These
encoding choices, the exact formula conventions, and the handling of invalid
codes are parts of this number's definition; changing them can change the
number.

The intended profile uses ordinary truth of the selected literal formulas
on natural-number parameters in the intended universe of sets. The proposed
mathematical justification forms the finitely many needed truth rows by
Separation and combines them as sets. This records the intended reading; the
present review has not independently verified its complete formal bridge.
The source's universal theorem for arbitrary profiles must not be described
as choosing or recognizing intended truth.

The following primary sources are the closest inspected precedents.

1. Agustín Rayo, [Big Number Duel](https://web.mit.edu/arayo/www/bignums.html),
   account of the duel held on 26 January 2007. Rayo gives the exact final
   benchmark using fewer than a googol symbols and unique designation among
   all assignments. He replaces primitive semantic naming vocabulary with
   a second-order satisfaction definition. His final note explicitly adopts
   the standard interpretation and warns that different models can produce
   different values. His contest also asks contestants to go beyond methods
   already introduced instead of making a small arithmetic modification.
   This is the benchmark and the source of the project's semantic issue.
   It does not supply the present encoded oracle program or its proof.

2. Fish, [Googology in Japan: exploring large numbers](https://gyafun.jp/ln/en.html),
   2013, sections "Fish number version 4" and "Fish number version 7." The
   author's version 4 uses a functional that maps an oracle function to a
   Busy Beaver function. Version 7, dated 19 October 2013, adds an oracle
   relation to Rayo's first-order micro-language and iterates the resulting
   naming operation along an ordinal hierarchy. This directly precedes the
   broad idea of combining Rayo-style naming, oracle access, and hierarchy
   iteration. Our fixed finite truth profile, iteration of the concrete
   self-halting operator, and numerical program encoding are different
   specifications. This review does not prove an inequality between the two
   numbers or endorse all of the page's informal magnitude claims.

3. Scott Aaronson, [The Busy Beaver Frontier](https://scottaaronson.com/papers/bb.pdf),
   2020, section 3, "Above and Below Busy Beaver," especially PDF page 7. Aaronson
   describes Busy Beaver functions for machines equipped with a halting or
   Busy Beaver oracle, then repeats this construction through finite stages
   and computable ordinals, including omega. He also explains that exact
   values depend on the oracle access mechanism. This is a clear precedent
   for the oracle-hierarchy method. Our language's diagonal proof and join
   projection are concrete implementations; this project has not proved
   equivalence with Aaronson's Turing-machine conventions. His footnote 16
   expresses a philosophical reservation about number sequences depending
   on set-theoretic truth. That reservation should be distinguished from a
   mathematical refutation of a definition made under Rayo's interpretation.

4. Øystein Linnebo and Agustín Rayo,
   [Hierarchies Ontological and Ideological](https://web.mit.edu/arayo/www/tt-g.pdf),
   *Mind* 121(482), 269–308 (2012), sections 3 and 6 and appendix B.
   The paper studies higher-order languages and semantic theories at higher
   levels, including transfinite type hierarchies. It also distinguishes an
   intended interpretation with unrestricted quantification from a
   set-sized model. It supplies foundational context for semantic ascent
   and for the model-versus-intended-universe distinction. It is not a
   definition of the present finite-profile Busy Beaver value. Publication
   metadata is available from the
   [publisher](https://academic.oup.com/mind/article-abstract/121/482/269/1044515).

5. Kenneth Reidbord,
   [On the Construction of Finite Integers Exceeding Rayo's Number and an Attempted Maximality Program](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6565482),
   written 12 April 2026 and posted 21 April 2026, SSRN 6565482. The accessible
   indexed abstract claims two finite integers exceeding Rayo, using a
   third-order definability construction under full semantics and a bounded
   formula-length argument. It also reports a failed bridge between
   provable and semantic unique existence in a separate maximality program.
   The abstract makes this a relevant prior-art lead for beyond-Rayo and
   AI-assisted constructions. Direct PDF retrieval failed in this review.
   The manuscript's arguments and claimed numerical bounds have not been
   independently checked here; they must be attributed as author claims.

The focused searches included combinations of Rayo with oracle Busy Beaver,
finite truth, self-halting, omega jump, and join, together with the authors'
own sites. None of the inspected primary sources specified the same finite
profile, self-halting join, program encoding, and fixed arguments. This is
a bounded search result. There is no proof that the exact construction is
unpublished, and definitional differences alone do not establish a new
mathematical method or a different numerical value.

For the manuscript, the following claim is appropriately calibrated once
the intended-semantics argument and final verification have passed review:

> We specify Sam Altman's Number by a concrete oracle-program language and
> a fixed finite profile of set-theoretic formulas. Its oracle is the join
> of the finite self-halting iterates of the profile's base oracle. We prove
> that the resulting Busy Beaver value exceeds the original Rayo benchmark,
> with a 61-bit witness for the comparison. The construction combines
> established methods; its contribution here is the explicit specification
> and accompanying Lean certificates.

Until that semantic argument passes review, replace the claimed original
comparison with "the corresponding finite-profile benchmark" and state
separately what remains to connect that benchmark to original Rayo. The
phrase "newly specified" can describe the object introduced in this paper;
"first," "unprecedented," "new method," and "largest named number" are not
supported by this review. No comparison with Fish 7, Reidbord's proposed
numbers, or other beyond-Rayo constructions has been established.

The construction has mathematical content beyond prescribing a small
arithmetic modification of Rayo: it specifies an oracle hierarchy, proves
that no finite stage computes the whole join in the concrete language, and
maximizes over a precisely bounded collection of programs. The magnitude
claim proved by the 61-bit witness is a strict inequality. The hierarchy's
noncomputability does not itself establish a quantitative gap at this one
fixed budget, a growth-rate classification, or a comparison with every
other oracle Busy Beaver convention.

Use "finite number with a non-effective definition" when discussing the
individual integer. Every fixed natural number is the output of some
ordinary constant program; noncomputability properly describes the oracle
or a function varying over inputs. The existing hierarchy proofs concern
total-function computation by the specified language. The paper should
preserve that exact scope.
