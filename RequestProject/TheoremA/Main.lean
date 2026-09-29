module

public import RequestProject.TheoremA.Proved
public import RequestProject.TheoremA.Kernel.FromSeparation
public import RequestProject.TheoremA.Leary.Detection

/-!
# Theorem A

`theoremA` is Theorem A of the revised manuscript `embedding_fpn (3).pdf`.
Its statement is unchanged. The reduction `theoremA_of_ingredients` now uses
`FanoTriples.exists_tripleSystem`: the 23 indices and 15 triples of Proposition 3.2.
The girth and integral row identity are checked by Lean's kernel.

The previously proved general ingredients are reused. Their historical declaration names
are retained: `lemma_3_1` is now Lemma 4.1, `lemma_4_2` is Lemma 5.1,
`proposition_5_1` is Theorem D (Section 6), `corollary_5_2` is Corollary 6.1,
and `proposition_7_1` supplies the induction in Theorem 7.3.

**Status.** `corollary_5_2` (the homological part, §§4–5: Lemma 4.1, Lemma 4.2, Corollary 4.3,
Proposition 5.1) is proved without `sorry`.  `lemma_3_1` is proved without `sorry` (`lemma31`, in
`Lemma31/Geometric.lean`): a nonidentity index element killed in the colimit would give a
nonidentity defect picture, and under `NPC` a least such picture is ruled out by the degree, face
and Euler-characteristic argument of `Lemma31/Picture/DefectCount.lean`.  `universalBases`
(Leary's `FP_2` embedding theorem together with relative recursive presentations, §6) is proved
without `sorry`: `Leary.flagSeparation` (`Leary/Detection.lean`, the detection theorem for the
fixed flag complex, proved combinatorially with a heap model of the right-angled Artin group of
its 1-skeleton) instantiates `universalBases_of_flagSeparation`.  Hence `theoremA` is proved,
and depends only on the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

@[expose] public section

namespace TheoremA

universe u

/-- **Universal bases** (Lemmas 6.1, 6.2, 3.2), proved: the separation statement for the fixed
flag complex (`Leary.flagSeparation`, `Leary/Detection.lean`) feeds the conditional chain
`universalBases_of_flagSeparation` (`Kernel/FromSeparation.lean`). -/
theorem universalBases : UniversalBases.{u} :=
  universalBases_of_flagSeparation Leary.flagSeparation

/-- **Theorem A.**  For every finite `n ≥ 2` and every countable group `G` there is an embedding
`G ↪ E` with `E` of type `FP_n`. -/
theorem theoremA (n : ℕ) (hn : 2 ≤ n) (G : Type u) [Group G] [Countable G] :
    ∃ (E : Type u) (_ : Group E), IsFP n E ∧ ∃ f : G →* E, Function.Injective f :=
  theoremA_of_ingredients lemma_3_1 corollary_5_2 universalBases n hn G

end TheoremA
