module

public import RequestProject.TheoremA.Lemma31.Witness
public import RequestProject.TheoremA.Lemma31.Picture.DefectCount

/-!
# Lemma 3.1 from the geometric argument

The picture argument of `Lemma31/Picture/` shows that a non-positively curved cone complex of
groups admits no defect picture with nonidentity defect
(`ConeComplex.no_nonidentity_defect_of_npc`); together with the existence of such a defect for
every nonidentity element of an index group that dies in the colimit
(`ConeComplex.exists_defectPicture_of_ι_eq_one`) this gives injectivity at the index vertices
(`ConeComplex.NPC.ι_inl_injective`).

* `TheoremA.coneIndexDevelopable` : every index group of a non-positively curved cone complex of
  groups embeds in the colimit;
* `TheoremA.lemma31` : **Lemma 3.1**, via the isomorphism `K_Σ(G) ≃* colim` and the reduction
  `tripleComplex_npc` from the hypotheses of Lemma 3.1 to `NPC`
  (`lemma31_of_coneIndexDevelopable`);
* `TheoremA.witnessLemma` : the older witness-lemma statement.  Its hypotheses (`NPC` and a
  nonidentity index element killed in the colimit) are contradictory by
  `coneIndexDevelopable`, so it holds by `False.elim`; no picture witness is constructed.  Lemma 3.1
  is **not** routed through it.

* `TheoremA.coneDevelopable` : all local groups (also the triple groups) embed in the colimit
  (`ConeComplex.NPC.ι_injective`); this is proved here as a by-product and is not used for
  Lemma 3.1.

None of these results depends on `universalBases` or on Theorem A, and Lemma 3.1 does not depend
on `coneDevelopable`.
-/

@[expose] public section

namespace TheoremA

universe u w

namespace ConeComplex

variable {V T : Type w} {C : ConeComplex.{u, w} V T}

/-- **Injectivity at every vertex** (index or triple).  A nonidentity element of any local group
that dies in the colimit gives a raw picture for that single letter, hence a least local picture,
hence (by `IsLeast.exists_defectPicture`) a nonidentity defect picture, which `NPC` forbids. -/
theorem NPC.ι_injective (hC : C.NPC) (k : V ⊕ T) : Function.Injective (C.ι k) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  by_contra hne
  have hmem : Monoid.CoprodI.of (i := k) a ∈ Subgroup.normalClosure C.rels :=
    (QuotientGroup.eq_one_iff _).mp ha
  obtain ⟨R⟩ := realizable_of_mem_normalClosure k hmem
  obtain ⟨L, hL⟩ := LocalPicture.exists_isLeast ⟨⟨k, a, hne, R⟩⟩
  obtain ⟨Δ, -⟩ := hL.exists_defectPicture
  exact L.ne_one (no_nonidentity_defect_of_npc hC Δ)

end ConeComplex

/-- **Developability** of non-positively curved cone complexes of groups (proved): every local
group, at an index vertex or at a triple vertex, embeds in the colimit. -/
theorem coneDevelopable : ConeDevelopable.{u, w} :=
  fun _ _ _ hC k => hC.ι_injective k

/-- **Developability at the index vertices** (proved): in a non-positively curved cone complex of
groups every index group embeds in the colimit. -/
theorem coneIndexDevelopable : ConeIndexDevelopable.{u, w} :=
  fun _ _ _ hC v => hC.ι_inl_injective v

/-- **Lemma 3.1** (proved): for a well-formed triple system whose incidence graph has girth at least
`12`, every index group `G` embeds in `K_Σ(G)`. -/
theorem lemma31 : Lemma31.{u} :=
  lemma31_of_coneIndexDevelopable coneIndexDevelopable

/-- **The witness lemma** (proved, vacuously): its hypotheses are contradictory by
`coneIndexDevelopable`.  This is a proof by contradiction, not a construction of a picture
witness. -/
theorem witnessLemma : WitnessLemma.{u, w} := by
  intro V T C hC v a ha h
  exact absurd (coneIndexDevelopable V T C hC v (h.trans (map_one _).symm)) ha

end TheoremA
