module

public import RequestProject.TheoremA.FP2.BoundaryNaturality
public import RequestProject.TheoremA.FP2.PresentationCriterion

/-!
# `FP₂` is preserved under finite relative presentations

For arbitrary relator sets `S ⊆ FreeGroup (Fin n)`, a substitution
`θ : FreeGroup (Fin n) →* FreeGroup (Fin m)` (arbitrary; it may send generators to any word,
including `1`) and a **finite** set `U ⊆ FreeGroup (Fin m)`:

* `presSubstHom θ h : PresentedGroup S →* PresentedGroup S'` whenever `θ` maps `S` into `S'`,
  with `presSubstHom_compat` giving the compatibility (B) on generators. It is not claimed to be
  injective.
* `relatorBoundary_subst_mem_span`: transport of a finite boundary witness along `θ`.
* `isFP_two_presentedGroup_subst_union_finite`:
  `IsFP 2 (PresentedGroup S) → IsFP 2 (PresentedGroup (θ '' S ∪ U))`.
* `isFP_two_presentedGroup_union_finite` (identity substitution) and
  `isFP_two_presentedGroup_castAdd_union_finite` (renaming along `Fin.castAdd k`).
* `isFP_two_presentedGroup_two_sources_union_finite`: two sources.

`S` need not be finite or enumerable, and no injectivity, decidability or Noetherian hypothesis
is used.  Nothing here says that an arbitrary quotient of an `FP₂` group is `FP₂`.
-/

@[expose] public section

namespace TheoremA

variable {n m : ℕ}

/-- The homomorphism `PresentedGroup S →* PresentedGroup S'` induced by a substitution `θ` that
maps every relator of `S` into `S'`. -/
noncomputable def presSubstHom {S : Set (FreeGroup (Fin n))} {S' : Set (FreeGroup (Fin m))}
    (θ : FreeGroup (Fin n) →* FreeGroup (Fin m)) (h : ∀ r ∈ S, θ r ∈ S') :
    PresentedGroup S →* PresentedGroup S' :=
  PresentedGroup.toGroup (f := fun i => PresentedGroup.mk S' (θ (FreeGroup.of i))) (by
    intro r hr
    have : FreeGroup.lift (fun i => PresentedGroup.mk S' (θ (FreeGroup.of i))) =
        (PresentedGroup.mk S').comp θ := by
      ext i; simp
    rw [this, MonoidHom.comp_apply]
    exact PresentedGroup.one_of_mem (h r hr))

/-- Compatibility (B) of `presSubstHom` with the canonical generators. -/
theorem presSubstHom_compat {S : Set (FreeGroup (Fin n))} {S' : Set (FreeGroup (Fin m))}
    (θ : FreeGroup (Fin n) →* FreeGroup (Fin m)) (h : ∀ r ∈ S, θ r ∈ S') (i : Fin n) :
    presSubstHom θ h (presGens S i) = FreeGroup.lift (presGens S') (θ (FreeGroup.of i)) := by
  rw [lift_presGens]
  exact PresentedGroup.toGroup.of _

/-- **Transport of a boundary witness.** If `θ` maps `S` into `S'` and every relator boundary of
`S` lies in the span of the boundaries of `T` (computed in `PresentedGroup S`), then for every
`r ∈ S` the boundary of `θ r` (computed in `PresentedGroup S'`) lies in the span of the boundaries
of `θ '' T`. -/
theorem relatorBoundary_subst_mem_span {S : Set (FreeGroup (Fin n))}
    {S' : Set (FreeGroup (Fin m))} (θ : FreeGroup (Fin n) →* FreeGroup (Fin m))
    (h : ∀ r ∈ S, θ r ∈ S') (T : Set (FreeGroup (Fin n)))
    (hT : ∀ r ∈ S, wordBoundary (presGens S) r ∈
      Submodule.span (ZG (PresentedGroup S)) (wordBoundary (presGens S) '' T))
    {r : FreeGroup (Fin n)} (hr : r ∈ S) :
    wordBoundary (presGens S') (θ r) ∈
      Submodule.span (ZG (PresentedGroup S')) (wordBoundary (presGens S') '' (θ '' T)) :=
  wordBoundary_subst_mem_span (presSubstHom θ h) (presGens S) (presGens S') θ
    (presSubstHom_compat θ h) T (hT r hr)

/-- **FP₂ preservation, one source (A).** For an arbitrary relator set `S`, an arbitrary
substitution `θ` and a finite set `U` of extra relators,
`IsFP 2 (PresentedGroup S) → IsFP 2 (PresentedGroup (θ '' S ∪ U))`. -/
theorem isFP_two_presentedGroup_subst_union_finite (S : Set (FreeGroup (Fin n)))
    (θ : FreeGroup (Fin n) →* FreeGroup (Fin m)) (U : Set (FreeGroup (Fin m)))
    (hU : U.Finite) (hS : IsFP 2 (PresentedGroup S)) :
    IsFP 2 (PresentedGroup (θ '' S ∪ U)) := by
  obtain ⟨T, hTfin, hTS, hT⟩ := (isFP_two_iff_all_relator_boundaries_mem_finite_span S).mp hS
  have hθ : ∀ r ∈ S, θ r ∈ θ '' S ∪ U := fun r hr => Or.inl ⟨r, hr, rfl⟩
  refine (isFP_two_iff_all_relator_boundaries_mem_finite_span _).mpr
    ⟨θ '' T ∪ U, (hTfin.image θ).union hU, Set.union_subset_union (Set.image_mono hTS) le_rfl,
      ?_⟩
  rintro _ (⟨r, hr, rfl⟩ | hu)
  · exact Submodule.span_mono (Set.image_mono Set.subset_union_left)
      (relatorBoundary_subst_mem_span θ hθ T hT hr)
  · exact Submodule.subset_span ⟨_, Or.inr hu, rfl⟩

/-- **Adding finitely many relators** preserves `FP₂`. -/
theorem isFP_two_presentedGroup_union_finite (S U : Set (FreeGroup (Fin n))) (hU : U.Finite)
    (hS : IsFP 2 (PresentedGroup S)) : IsFP 2 (PresentedGroup (S ∪ U)) := by
  have := isFP_two_presentedGroup_subst_union_finite S (MonoidHom.id _) U hU hS
  rwa [MonoidHom.coe_id, Set.image_id] at this

/-- **Adjoining `k` generators and finitely many relators** preserves `FP₂`: the old alphabet is
included in `Fin (n + k)` by `Fin.castAdd k`.  (`n = 0`, `k = 0`, `S = ∅`, `U = ∅` allowed.) -/
theorem isFP_two_presentedGroup_castAdd_union_finite (k : ℕ) (S : Set (FreeGroup (Fin n)))
    (U : Set (FreeGroup (Fin (n + k)))) (hU : U.Finite) (hS : IsFP 2 (PresentedGroup S)) :
    IsFP 2 (PresentedGroup (FreeGroup.map (Fin.castAdd k) '' S ∪ U)) :=
  isFP_two_presentedGroup_subst_union_finite S (FreeGroup.map (Fin.castAdd k)) U hU hS

/-- **FP₂ preservation, two sources (F).** For arbitrary relator sets `S₀`, `S₁` on finite
alphabets, arbitrary substitutions `θ₀`, `θ₁` into a common `FreeGroup (Fin m)` and a finite set
`U`, if both `PresentedGroup S₀` and `PresentedGroup S₁` are `FP₂` then so is
`PresentedGroup (θ₀ '' S₀ ∪ θ₁ '' S₁ ∪ U)`. -/
theorem isFP_two_presentedGroup_two_sources_union_finite {n₀ n₁ : ℕ}
    (S₀ : Set (FreeGroup (Fin n₀))) (S₁ : Set (FreeGroup (Fin n₁)))
    (θ₀ : FreeGroup (Fin n₀) →* FreeGroup (Fin m)) (θ₁ : FreeGroup (Fin n₁) →* FreeGroup (Fin m))
    (U : Set (FreeGroup (Fin m))) (hU : U.Finite)
    (h₀ : IsFP 2 (PresentedGroup S₀)) (h₁ : IsFP 2 (PresentedGroup S₁)) :
    IsFP 2 (PresentedGroup (θ₀ '' S₀ ∪ θ₁ '' S₁ ∪ U)) := by
  obtain ⟨T₀, hT₀fin, hT₀S, hT₀⟩ := (isFP_two_iff_all_relator_boundaries_mem_finite_span S₀).mp h₀
  obtain ⟨T₁, hT₁fin, hT₁S, hT₁⟩ := (isFP_two_iff_all_relator_boundaries_mem_finite_span S₁).mp h₁
  have hθ₀ : ∀ r ∈ S₀, θ₀ r ∈ θ₀ '' S₀ ∪ θ₁ '' S₁ ∪ U :=
    fun r hr => Or.inl (Or.inl ⟨r, hr, rfl⟩)
  have hθ₁ : ∀ r ∈ S₁, θ₁ r ∈ θ₀ '' S₀ ∪ θ₁ '' S₁ ∪ U :=
    fun r hr => Or.inl (Or.inr ⟨r, hr, rfl⟩)
  refine (isFP_two_iff_all_relator_boundaries_mem_finite_span _).mpr
    ⟨θ₀ '' T₀ ∪ θ₁ '' T₁ ∪ U, ((hT₀fin.image θ₀).union (hT₁fin.image θ₁)).union hU,
      Set.union_subset_union
        (Set.union_subset_union (Set.image_mono hT₀S) (Set.image_mono hT₁S)) le_rfl, ?_⟩
  rintro _ ((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | hu)
  · exact Submodule.span_mono
      (Set.image_mono (Set.subset_union_left.trans Set.subset_union_left))
      (relatorBoundary_subst_mem_span θ₀ hθ₀ T₀ hT₀ hr)
  · exact Submodule.span_mono
      (Set.image_mono (Set.subset_union_right.trans Set.subset_union_left))
      (relatorBoundary_subst_mem_span θ₁ hθ₁ T₁ hT₁ hr)
  · exact Submodule.subset_span ⟨_, Or.inr hu, rfl⟩

end TheoremA
