# Theorem A with the Fano-plane construction

This source release formalizes Theorem A of **embedding_fpn (3).pdf**, using
the 23-index, 15-triple system in Proposition 3.2 of that manuscript.
It reuses the previously checked geometric, homological and relative Leary
proofs. The finite example in the final proof has been replaced.

## Main statements

`TheoremA.theoremA` retains its original statement:

```lean
theorem theoremA (n : ℕ) (hn : 2 ≤ n)
    (G : Type u) [Group G] [Countable G] :
    ∃ (E : Type u) (_ : Group E),
      IsFP n E ∧ ∃ f : G →* E, Function.Injective f
```

`TheoremA.Fano.theoremA` proves the same statement with the fixed-oracle
argument written out. `TheoremA.Fano.universalFP` supplies the existence
assertion of Theorem 7.3: for each oracle `R` and each `n ≥ 2`, an `FP_n`
member of `ClassCR R` contains every member of that class. The additional
assertion that one may choose a coherent increasing sequence is not a
separate theorem in this file and is not needed for Theorem A.

`IsFP` is unchanged: it asserts an exact finite-rank free partial resolution
of the trivial integral module over the group ring. The conclusion concerns
each finite `n` separately; it does not assert an `FP_∞` overgroup.

## Files and correspondence with the manuscript

| Manuscript | Lean declaration / file |
| --- | --- |
| Proposition 3.2 | `FanoTriples.proposition_3_2`, `RequestProject/FanoTriples.lean` |
| Lemma 2.2 | `TheoremA.comparison`, `TheoremA/Homological/Comparison.lean` |
| Lemma 4.1 | `TheoremA.lemma_3_1`; specialization `TheoremA.Fano.index_injective` |
| Lemma 4.2, relative presentations | `RelPres/Class.lean`, `RelPres/Diagram.lean` |
| Lemma 5.1 | `TheoremA.lemma_4_2`, `Homological/L42/Lemma42.lean` |
| Corollary 5.3, ingredient used in degree raising | `TheoremA.cor43_of_lemma42` |
| Theorem D / Section 6 | `TheoremA.proposition_5_1`, `Homological/Prop51.lean` |
| Corollary 6.1 | `TheoremA.corollary_5_2`; specialization `TheoremA.Fano.degree_raising` |
| Lemma 7.1 | `RelPres/TwoGen.lean` |
| Lemma 7.2 | `TheoremA.Fano.universalFP2` and the proved relative Leary chain |
| Theorem 7.3, existence assertion | `TheoremA.Fano.universalFP` |
| Theorem A | `TheoremA.theoremA` and `TheoremA.Fano.theoremA` |

Paths in this table under `TheoremA/` are relative to `RequestProject/`.
Historical declaration names are retained to preserve compatibility.
The formal proof of the diagram lemma uses combinatorial defect pictures;
it does not invoke an unformalized CAT(0) developability theorem.
Mathlib writes the HNN relation as `t b t⁻¹ = φ(b)`; its stable letter is
the inverse of the stable letter in the manuscript. This convention is
already recorded in `TheoremA/Defs.lean` and changes neither the group nor
the embedding assertion.

## The new finite system

The numbering in `FanoTriples.lean` is:

* distinguished index `0`; `a = 1`; `b = 2`;
* `f_(j,0) = 3+j`, `f_(j,1) = 10+j`, for `0 ≤ j ≤ 6`;
* `f_(j,3) = 16+j`, for `1 ≤ j ≤ 6`.

The removed flag is `f_(0,3)`. The point and line triples are defined by
the exact modular formulas in the manuscript. They are ordered as
`π_0,...,π_6,λ_0,...,λ_6,γ`; `ν` has values
`(+1,+1,+1,+1,+1,+1,+1,-1,-1,-1,-1,-1,-1,-1,+1)`.

The code proves that there are 15 distinct triples, that their three entries
are distinct and less than 23, that the row identity holds, and that the
incidence graph has girth at least 12. The last two facts use finite checks
evaluated by the Lean kernel and previously proved checker soundness. The
girth proof is a finite check of this exact graph, rather than a new general
theorem about subdivisions of projective-plane incidence graphs.

No Python-generated data or external certificate needs to be trusted.
`verification.json` records an earlier audit of the transitive dependencies
and axioms of both final proofs, together with the source hashes used for that
run. It is a historical verification record and does not certify source edits
made after those hashes were recorded. `scripts/audit_fano.lean` prints the
principal declarations and finite data for inspection.

## Reproduction

Use the exact `lean-toolchain` and `lake-manifest.json` in the release
(Lean 4.28.0 and the pinned Mathlib revision). From the extracted directory:

```text
lake exe cache get
lake build RequestProject
lake env lean scripts/audit_fano.lean
```

The archive contains the complete transitive closure of local source imports
for `RequestProject.TheoremA.Fano`, plus the audit script and pinned package
files. Mathlib and other dependency caches are downloaded by Lake, not
included in the archive. The separate, ongoing topological Theorem B work
is outside this Theorem A release.
