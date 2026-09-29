module

public import RequestProject.TheoremA.FP2.PresentationExactness
public import RequestProject.TheoremA.FP2.FiniteKernel

/-!
# The algebraic presentation criterion for `FP₂`

For an arbitrary set of relators `S ⊆ FreeGroup (Fin n)`, `G = PresentedGroup S` with its
canonical generators `x`, `d = genBoundary x` and word boundaries `D = wordBoundary x` computed
in `G`:

* `isFP_two_iff_finite_relator_boundaries`:
  `IsFP 2 G ↔ ∃ T, T.Finite ∧ T ⊆ S ∧ ker d = span_Λ (D '' T)`;
* `isFP_two_iff_all_relator_boundaries_mem_finite_span`:
  `IsFP 2 G ↔ ∃ T, T.Finite ∧ T ⊆ S ∧ ∀ r ∈ S, D r ∈ span_Λ (D '' T)`;
* `isFP_two_presentedGroup_of_finite`: `S.Finite → IsFP 2 (PresentedGroup S)`.

Neither criterion says that `T` presents `G`; all boundaries are computed over the original `G`.
No recursion-theoretic or decidability hypothesis is used; `n = 0` and `S = ∅` are allowed.
-/

@[expose] public section

namespace TheoremA

/-- If the span of `U` is finitely generated, it is already spanned by a finite subset of `U`. -/
theorem exists_finset_subset_span_eq_of_fg {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {U : Set M} (h : (Submodule.span R U).FG) :
    ∃ U₀ : Finset M, ↑U₀ ⊆ U ∧ Submodule.span R (U₀ : Set M) = Submodule.span R U := by
  classical
  obtain ⟨s, hs⟩ := h
  have key : ∀ y ∈ s, ∃ T : Finset M, ↑T ⊆ U ∧ y ∈ Submodule.span R (T : Set M) :=
    fun y hy => Submodule.mem_span_finite_of_mem_span (hs ▸ Submodule.subset_span hy)
  choose T hTU hyT using key
  have hsub : ∀ y (hy : y ∈ s), (T y hy : Set M) ⊆ ↑(s.attach.biUnion fun z => T z.1 z.2) :=
    fun y hy => by
      intro m hm
      simp only [Finset.coe_biUnion, Finset.coe_attach, Set.mem_univ, Set.iUnion_true,
        Set.mem_iUnion]
      exact ⟨⟨y, hy⟩, hm⟩
  refine ⟨s.attach.biUnion fun z => T z.1 z.2, ?_, le_antisymm (Submodule.span_mono ?_) ?_⟩
  · intro m hm
    simp only [Finset.coe_biUnion, Finset.coe_attach, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion] at hm
    obtain ⟨⟨y, hy⟩, hm⟩ := hm
    exact hTU y hy hm
  · intro m hm
    simp only [Finset.coe_biUnion, Finset.coe_attach, Set.mem_univ, Set.iUnion_true,
      Set.mem_iUnion] at hm
    obtain ⟨⟨y, hy⟩, hm⟩ := hm
    exact hTU y hy hm
  · rw [← hs, Submodule.span_le]
    intro y hy
    exact Submodule.span_mono (hsub y hy) (hyT y hy)

variable {n : ℕ} (S : Set (FreeGroup (Fin n)))

/-- **Finite relator boundaries characterize `FP₂`.** `PresentedGroup S` is `FP₂` iff for some
finite `T ⊆ S` the boundaries of the relators in `T` (computed in `PresentedGroup S`) span
`ker (genBoundary x)`. -/
theorem isFP_two_iff_finite_relator_boundaries :
    IsFP 2 (PresentedGroup S) ↔
      ∃ T : Set (FreeGroup (Fin n)), T.Finite ∧ T ⊆ S ∧
        LinearMap.ker (genBoundary (presGens S)) =
          Submodule.span (ZG (PresentedGroup S)) (wordBoundary (presGens S) '' T) := by
  classical
  rw [isFP_two_iff_fg_ker_genBoundary _ (PresentedGroup.closure_range_of S)]
  constructor
  · intro hfg
    rw [ker_genBoundary_eq_span_relatorBoundary] at hfg ⊢
    obtain ⟨U₀, hU₀, hspan⟩ := exists_finset_subset_span_eq_of_fg hfg
    obtain ⟨T, hTS, rfl⟩ := Finset.subset_set_image_iff.mp hU₀
    exact ⟨T, T.finite_toSet, hTS, by rw [← hspan, Finset.coe_image]⟩
  · rintro ⟨T, hT, -, hker⟩
    rw [hker]
    exact Submodule.fg_span (hT.image _)

/-- **Equivalent form.** `PresentedGroup S` is `FP₂` iff for some finite `T ⊆ S`, the boundary of
every relator in `S` lies in the span of the boundaries of the relators in `T`. -/
theorem isFP_two_iff_all_relator_boundaries_mem_finite_span :
    IsFP 2 (PresentedGroup S) ↔
      ∃ T : Set (FreeGroup (Fin n)), T.Finite ∧ T ⊆ S ∧
        ∀ r ∈ S, wordBoundary (presGens S) r ∈
          Submodule.span (ZG (PresentedGroup S)) (wordBoundary (presGens S) '' T) := by
  rw [isFP_two_iff_finite_relator_boundaries]
  constructor
  · rintro ⟨T, hT, hTS, hker⟩
    refine ⟨T, hT, hTS, fun r hr => ?_⟩
    rw [← hker, ker_genBoundary_eq_span_relatorBoundary]
    exact Submodule.subset_span ⟨r, hr, rfl⟩
  · rintro ⟨T, hT, hTS, hmem⟩
    refine ⟨T, hT, hTS, ?_⟩
    rw [ker_genBoundary_eq_span_relatorBoundary]
    refine le_antisymm ?_ (Submodule.span_mono (Set.image_mono hTS))
    rw [Submodule.span_le]
    rintro _ ⟨r, hr, rfl⟩
    exact hmem r hr

/-- A group with a finite presentation on finitely many generators is `FP₂`. -/
theorem isFP_two_presentedGroup_of_finite (hS : S.Finite) : IsFP 2 (PresentedGroup S) :=
  (isFP_two_iff_finite_relator_boundaries S).mpr
    ⟨S, hS, subset_rfl, ker_genBoundary_eq_span_relatorBoundary S⟩

end TheoremA
