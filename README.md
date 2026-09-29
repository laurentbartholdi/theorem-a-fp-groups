# Theorem A: countable groups embed in groups of type FP_n

This Lean 4 project formalizes Theorem A of a manuscript currently identified
as `embedding_fpn (3).pdf`. For every finite integer `n >= 2`, every countable
group embeds in a group of type `FP_n` over the integers.

The claim is stated in [Challenge.lean](Challenge.lean) and proved in
[Solution.lean](Solution.lean). The short Challenge file imports Mathlib only;
the Solution reuses the project's full proof development. Palomar compares the
declaration `TheoremA.palomarStatement` in both files using
[comparator.json](comparator.json).

## Theorem

In Lean, the result says that for every `n : ℕ` with `2 ≤ n` and every
countable group `G`, there exist a group `E` of the same universe, an
`FP_n`-structure on `E`, and an injective group homomorphism `G →* E`.

Here `TheoremA.IsFP n E` means that the trivial integral module has an exact
partial resolution through degree `n` by free left `ℤ[E]`-modules of finite
rank. The statement concerns each finite `n` separately; it does not assert
one overgroup of type `FP_∞`.

The compared claim is Theorem A only. The repository also contains formalized
ingredients and related statements from the manuscript, including the fixed
Fano-system instance of degree raising and the existence assertion of
Theorem 7.3; those are not additional claims in this Palomar Comparator
configuration.

## Proof outline

The proof uses a fixed oriented triple system with 23 indices and 15 triples,
corresponding to Proposition 3.2 of the manuscript. Lean proves that the
triples are well formed and distinct, checks the integral row identity, and
checks girth at least 12 for the associated incidence graph. The finite checks
are evaluated by Lean's kernel, with checker soundness proved in Lean.

The construction combines the geometric injectivity lemma, the homological
degree-raising result, and the relative Leary embedding argument. The formal
diagram lemma is proved with combinatorial defect pictures; it does not rely on
an unformalized CAT(0) developability theorem. The stable-letter convention for
HNN extensions in Mathlib is the inverse of the convention used in the
manuscript. No Python-generated data or external certificate is trusted.

The detailed correspondence between manuscript results and Lean declarations,
as well as the finite-system indexing and audit details, is in
[README_FANO_THEOREM_A.md](README_FANO_THEOREM_A.md).

## Build and audit

The project pins Lean 4.28.0 and Mathlib in [lean-toolchain](lean-toolchain),
[lakefile.toml](lakefile.toml), and [lake-manifest.json](lake-manifest.json).
With Lean and Lake installed, run from the repository root:

```sh
lake exe cache get
lake build RequestProject Challenge Solution
lake env lean scripts/audit_fano.lean
```

The audit script prints the principal statements and fixed finite data for
inspection. [verification.json](verification.json) records an earlier build
and dependency/axiom audit, including the source hashes used for that run; it
is a historical record rather than a certificate for later source edits.
Palomar performs its own Comparator verification and independent kernel
replay; a local build is not a substitute for that check.

## Scope and provenance

The source manuscript is not included in this repository. The current local
record identifies it only as `embedding_fpn (3).pdf` and records a SHA-256
digest in [verification.json](verification.json); its full bibliographic
reference and planned arXiv location remain to be supplied. The formalization
was produced with Aristotle. Its precise model/version and prompt history were
not retained. No independent mathematical review is documented here, so the
metadata reports the review status as unchecked.

Palomar is a registry of machine-checked claims, not peer review, a novelty
certification, or a journal publication. Registration would record an
immutable public GitHub commit. This repository is being prepared locally and
has not been uploaded or submitted.
