module

public import RequestProject.TheoremA.Main

/-!
# The revised proof of Theorem A, with the Fano system made explicit

This file exposes the specializations used in Sections 4, 6 and 7 of
`embedding_fpn (3).pdf`. The general geometric and homological proofs and the
oracle-relative Leary theorem are reused, without adding any hypothesis.

`universalFP` is the existence assertion of Theorem 7.3 for each fixed oracle.
`theoremA` follows from it and the proved input-oracle/two-generator construction.
The original `TheoremA.theoremA` also uses the new Fano system, via `Reduction.lean`.
-/

@[expose] public section

namespace TheoremA.Fano

open RelPres

universe u

/-- The diagram group for the exact 23-index, 15-triple system of Proposition 3.2. -/
abbrev K (G : Type u) [Group G] := diagramGroup 23 FanoTriples.triples G

/-- Lemma 4.1 specialized to the manuscript's fixed system. -/
theorem index_injective (G : Type u) [Group G] (v : Fin 23) :
    Function.Injective (diagramGroup.ι 23 FanoTriples.triples G v) :=
  lemma_3_1 23 FanoTriples.triples FanoTriples.wellFormed FanoTriples.girth G v

/-- Corollary 6.1 with the fifteen relations and their prescribed signs. -/
theorem degree_raising (m : ℕ) (hm : 2 ≤ m) (B : Type u) [Group B]
    (hB : IsFP m B) (α : Fin 23 → B →* B)
    (hα : DiagramRelations 23 FanoTriples.triples α)
    (hinj : Function.Injective (α 0)) :
    IsFP (m + 1) (ascHNN (α 0) hinj) :=
  corollary_5_2 23 FanoTriples.triples FanoTriples.nu (by decide)
    FanoTriples.wellFormed FanoTriples.rowIdentity m hm B hB α hα hinj

/-- Lemma 7.2: an `FP₂` universal base for each fixed oracle, in the same oracle class. -/
theorem universalFP2 (R : Set ℕ) :
    ∃ (B : Type u) (_ : Group B), ClassCR R B ∧ IsFP 2 B ∧
      ∀ (Y : Type u) [Group Y], ClassCR R Y →
        ∃ f : Y →* B, Function.Injective f := by
  obtain ⟨B, _, hBC, hBFP, j, hj⟩ :=
    relativeLeary_of_flagSeparation Leary.flagSeparation R (ULift.{u} (VR R))
      (classCR_ULift_VR R)
  refine ⟨B, inferInstance, hBC, hBFP, ?_⟩
  intro Y _ hY
  obtain ⟨f, hf⟩ := hY.exists_injective_hom_VR
  exact ⟨(j.comp MulEquiv.ulift.symm.toMonoidHom).comp f,
    (hj.comp MulEquiv.ulift.symm.injective).comp hf⟩

/-- Theorem 7.3 (existence assertion): a universal `FP_n` base for each fixed oracle.
The induction uses the Fano system at every degree-raising step. -/
theorem universalFP (R : Set ℕ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (B : Type u) (_ : Group B), ClassCR R B ∧ IsFP n B ∧
      ∀ (Y : Type u) [Group Y], ClassCR R Y →
        ∃ f : Y →* B, Function.Injective f := by
  obtain ⟨B, _, hBC, hBFP, hBU⟩ := universalFP2.{u} R
  obtain ⟨E, _, hEC, hEFP, -, hEU⟩ :=
    proposition_7_1 lemma_3_1 corollary_5_2 23 FanoTriples.triples FanoTriples.nu
      (by decide) FanoTriples.wellFormed FanoTriples.girth FanoTriples.rowIdentity
      B (fun X _ => ClassCR R X)
      ⟨B, inferInstance, hBC, hBFP, ⟨MonoidHom.id B, Function.injective_id⟩, hBU⟩
      (classCR_diagramGroup_closure R 23 FanoTriples.triples)
      (classCR_ascHNN_closure R) n hn
  exact ⟨E, inferInstance, hEC, hEFP, hEU⟩

/-- Theorem A, following the revised manuscript's fixed-oracle proof explicitly. -/
theorem theoremA (n : ℕ) (hn : 2 ≤ n) (G : Type u) [Group G] [Countable G] :
    ∃ (E : Type u) (_ : Group E), IsFP n E ∧ ∃ f : G →* E, Function.Injective f := by
  obtain ⟨R, f, hf⟩ := exists_oracle_injective_hom_VR G
  obtain ⟨B, _, -, hBFP, hBU⟩ := universalFP.{u} R n hn
  obtain ⟨j, hj⟩ := hBU (ULift.{u} (VR R)) (classCR_ULift_VR R)
  exact ⟨B, inferInstance, hBFP,
    (j.comp MulEquiv.ulift.symm.toMonoidHom).comp f,
    (hj.comp MulEquiv.ulift.symm.injective).comp hf⟩

end TheoremA.Fano
