module

public import RequestProject.TheoremA.Groups.HBJoin

/-!
# Benignness of saturated subgroups via towers of ascending HNN extensions

Let `G` be a finitely generated group in `C_R` of type `FP₂`, let `Φ` be a finite list of
injective endomorphisms of `G`, and let `K ≤ G` satisfy, for every `φ ∈ Φ`,

* invariance: `φ(K) ≤ K`;
* saturation: `K ∩ φ(G) ≤ φ(K)`.

Adjoin one stable letter `t_φ` per `φ` with `t_φ x t_φ⁻¹ = φ(x)` for `x` in the (original,
embedded) group `G`.  At each stage the associated subgroups are the images of the original `G`
and of `φ(G)`, both finitely generated, so each stage stays in `C_R` and of type `FP₂`
(`classCR_isFP_two_hnn`).  Britton's lemma (`mem_of_mem_closure_invariant`) gives, at each stage,
`⟨M, t_φ⟩ ∩ E = M`; hence at the top `⟨K, t_φ (φ ∈ Φ)⟩ ∩ G = K` (`exists_tower`).

`hb_of_saturated`: if moreover `K` is the smallest subgroup containing a finite set `k₀ ⊆ K` and
closed under every `φ ∈ Φ`, then `K` is `HB_R` in `G`, with the finitely generated detecting
subgroup `⟨k₀, t_φ (φ ∈ Φ)⟩`.
-/

@[expose] public section

namespace TheoremA.Kernel

open TheoremA.RelPres TheoremA.Britton HNNExtension

universe u

variable {R : Set ℕ}

/-- **One stage of the tower.** -/
theorem hnn_step {G E : Type u} [Group G] [Group E] (hG : Group.FG G) (hE1 : ClassCR R E)
    (hE2 : IsFP 2 E) (ι : G →* E) (hι : Function.Injective ι) (φ : G →* G)
    (hφ : Function.Injective φ) (K : Subgroup G) (hK1 : K.map φ ≤ K)
    (hK2 : K ⊓ φ.range ≤ K.map φ) (M : Subgroup E) (hM : M.comap ι = K) :
    ∃ (E' : Type u) (_ : Group E'), ClassCR R E' ∧ IsFP 2 E' ∧ ∃ j : E →* E',
      Function.Injective j ∧ ∃ τ : E', (∀ g, τ * j (ι g) * τ⁻¹ = j (ι (φ g))) ∧
        (Subgroup.closure (j '' (M : Set E) ∪ {τ})).comap j = M := by
  have hιφ : Function.Injective (ι.comp φ) := hι.comp hφ
  let iso : ι.range ≃* (ι.comp φ).range :=
    (MonoidHom.ofInjective hι).symm.trans (MonoidHom.ofInjective hιφ)
  have iso_apply : ∀ g : G, ((iso ⟨ι g, g, rfl⟩ : (ι.comp φ).range) : E) = ι (φ g) := by
    intro g
    have h : (MonoidHom.ofInjective hι).symm ⟨ι g, g, rfl⟩ = g := by
      rw [MulEquiv.symm_apply_eq]; rfl
    simp only [iso, MulEquiv.trans_apply, h]
    rfl
  have iso_symm_apply : ∀ g : G,
      ((iso.symm ⟨ι (φ g), g, rfl⟩ : ι.range) : E) = ι g := by
    intro g
    have : iso.symm ⟨ι (φ g), g, rfl⟩ = ⟨ι g, g, rfl⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [iso_apply]
    rw [this]
  have hfg : Group.FG ι.range := by
    rw [Group.fg_iff_subgroup_fg, MonoidHom.range_eq_map]
    exact Subgroup.fg_map' _ (Group.fg_def.1 hG)
  obtain ⟨c1, c2⟩ := classCR_isFP_two_hnn hE1 hE2 iso hfg
  refine ⟨HNNExtension E ι.range (ι.comp φ).range iso, inferInstance, c1, c2, of,
    of_injective _, t, ?_, ?_⟩
  · intro g
    have := equiv_eq_conj (φ := iso) ⟨ι g, g, rfl⟩
    rw [iso_apply] at this
    exact this.symm
  · apply le_antisymm
    · intro x hx
      obtain ⟨w, hw, hwx⟩ := mem_of_mem_closure_invariant iso M
        (by
          rintro ⟨_, g, rfl⟩ ha
          have hg : g ∈ K := by rw [← hM]; exact ha
          have : (iso ⟨ι g, g, rfl⟩ : E) = ι (φ g) := iso_apply g
          rw [this]
          have : φ g ∈ K := hK1 ⟨g, hg, rfl⟩
          rw [← hM] at this
          exact this)
        (by
          rintro ⟨_, g, rfl⟩ hb
          have hg : φ g ∈ K := by rw [← hM]; exact hb
          obtain ⟨k, hk, hkg⟩ := hK2 ⟨hg, g, rfl⟩
          have hkg' : k = g := hφ hkg
          subst hkg'
          show (iso.symm ⟨ι (φ k), k, rfl⟩ : E) ∈ M
          rw [iso_symm_apply]
          show k ∈ M.comap ι
          rw [hM]; exact hk)
        (of x) hx ⟨x, rfl⟩
      rw [of_injective _ hwx] at hw
      exact hw
    · intro x hx
      exact Subgroup.subset_closure (Or.inl ⟨x, hx, rfl⟩)

/-- **The tower.**  For a finite list `Φ` of injective endomorphisms under which `K` is invariant
and saturated, and any embedding `ι : G → E` into a suitable group with a subgroup `M ≤ E`
satisfying `ι⁻¹(M) = K`, there is a suitable `E'`, an embedding `j : E → E'` and a finite list
`T ⊆ E'` of stable letters, one for each `φ ∈ Φ`, with `⟨j(M), T⟩ ∩ j(E) = j(M)`. -/
theorem exists_tower {G : Type u} [Group G] (hG : Group.FG G) (K : Subgroup G) :
    ∀ (Φ : List (G →* G)), (∀ φ ∈ Φ, Function.Injective φ) → (∀ φ ∈ Φ, K.map φ ≤ K) →
      (∀ φ ∈ Φ, K ⊓ φ.range ≤ K.map φ) →
      ∀ (E : Type u) [Group E], ClassCR R E → IsFP 2 E → ∀ (ι : G →* E),
        Function.Injective ι → ∀ (M : Subgroup E), M.comap ι = K →
        ∃ (E' : Type u) (_ : Group E'), ClassCR R E' ∧ IsFP 2 E' ∧ ∃ j : E →* E',
          Function.Injective j ∧ ∃ T : List E',
            (∀ φ ∈ Φ, ∃ τ ∈ T, ∀ g, τ * j (ι g) * τ⁻¹ = j (ι (φ g))) ∧
            (Subgroup.closure (j '' (M : Set E) ∪ {x | x ∈ T})).comap j = M
  | [], _, _, _, E, _, h1, h2, ι, hι, M, hM => by
    refine ⟨E, inferInstance, h1, h2, MonoidHom.id E, Function.injective_id, [], by simp, ?_⟩
    simp
  | φ :: Φ, hinj, hK1, hK2, E, _, h1, h2, ι, hι, M, hM => by
    obtain ⟨E₁, _, a1, a2, j, hj, τ, hτ, hc⟩ := hnn_step hG h1 h2 ι hι φ
      (hinj φ (by simp)) K (hK1 φ (by simp)) (hK2 φ (by simp)) M hM
    let M₁ : Subgroup E₁ := Subgroup.closure (j '' (M : Set E) ∪ {τ})
    have hM₁ : M₁.comap (j.comp ι) = K := by
      rw [← Subgroup.comap_comap, hc, hM]
    obtain ⟨E₂, _, b1, b2, j', hj', T, hT, hc'⟩ := exists_tower hG K Φ
      (fun ψ hψ => hinj ψ (by simp [hψ])) (fun ψ hψ => hK1 ψ (by simp [hψ]))
      (fun ψ hψ => hK2 ψ (by simp [hψ])) E₁ a1 a2 (j.comp ι) (hj.comp hι) M₁ hM₁
    refine ⟨E₂, inferInstance, b1, b2, j'.comp j, hj'.comp hj, j' τ :: T, ?_, ?_⟩
    · intro ψ hψ
      rcases List.mem_cons.1 hψ with rfl | hψ
      · refine ⟨j' τ, by simp, fun g => ?_⟩
        simp only [MonoidHom.comp_apply]
        rw [← map_inv, ← map_mul, ← map_mul, hτ]
      · obtain ⟨τ', hτ', h'⟩ := hT ψ hψ
        exact ⟨τ', List.mem_cons_of_mem _ hτ', h'⟩
    · apply le_antisymm
      · have hle : Subgroup.closure ((j'.comp j) '' (M : Set E) ∪ {x | x ∈ j' τ :: T}) ≤
            Subgroup.closure (j' '' (M₁ : Set E₁) ∪ {x | x ∈ T}) := by
          rw [Subgroup.closure_le]
          rintro _ (⟨m, hm, rfl⟩ | hx)
          · exact Subgroup.subset_closure
              (Or.inl ⟨j m, Subgroup.subset_closure (Or.inl ⟨m, hm, rfl⟩), rfl⟩)
          · rcases List.mem_cons.1 hx with rfl | hx
            · exact Subgroup.subset_closure
                (Or.inl ⟨τ, Subgroup.subset_closure (Or.inr rfl), rfl⟩)
            · exact Subgroup.subset_closure (Or.inr hx)
        intro x hx
        have h3 : j x ∈ M₁ := by
          have : j' (j x) ∈ Subgroup.closure (j' '' (M₁ : Set E₁) ∪ {x | x ∈ T}) := hle hx
          rw [← hc']; exact this
        rw [← hc]; exact h3
      · intro x hx
        exact Subgroup.subset_closure (Or.inl ⟨x, hx, rfl⟩)

/-- **Benignness of a saturated subgroup.**  `K` is invariant and saturated under every
`φ ∈ Φ`, and is the smallest subgroup containing the finite set `k₀ ⊆ K` and closed under every
`φ ∈ Φ`.  Then `K` is `HB_R` in `G` (same oracle `R`). -/
theorem hb_of_saturated {G : Type u} [Group G] (hG : Group.FG G) (hG1 : ClassCR R G)
    (hG2 : IsFP 2 G) (K : Subgroup G) (Φ : List (G →* G))
    (hinj : ∀ φ ∈ Φ, Function.Injective φ) (hK1 : ∀ φ ∈ Φ, K.map φ ≤ K)
    (hK2 : ∀ φ ∈ Φ, K ⊓ φ.range ≤ K.map φ) (k₀ : Finset G) (hk₀ : (k₀ : Set G) ⊆ K)
    (hmin : ∀ L : Subgroup G, (k₀ : Set G) ⊆ L → (∀ φ ∈ Φ, L.map φ ≤ L) → K ≤ L) :
    HB R K := by
  obtain ⟨E, _, e1, e2, j, hj, T, hT, hc⟩ := exists_tower hG K Φ hinj hK1 hK2 G hG1 hG2
    (MonoidHom.id G) Function.injective_id K rfl
  classical
  let V : Subgroup E := Subgroup.closure ((k₀.image j : Set E) ∪ {x | x ∈ T})
  have hV : V.FG := ⟨k₀.image j ∪ T.toFinset, by simp [V]⟩
  refine ⟨E, inferInstance, e1, e2, j, hj, V, hV, le_antisymm ?_ ?_⟩
  · intro x hx
    have hle : V ≤ Subgroup.closure (j '' (K : Set G) ∪ {x | x ∈ T}) := by
      apply Subgroup.closure_mono
      rintro _ (hx | hx)
      · simp only [Finset.coe_image] at hx
        obtain ⟨g, hg, rfl⟩ := hx
        exact Or.inl ⟨g, hk₀ hg, rfl⟩
      · exact Or.inr hx
    rw [← hc]
    exact hle hx
  · apply hmin (V.comap j)
    · intro g hg
      exact Subgroup.subset_closure (Or.inl (by simp only [Finset.coe_image]; exact ⟨g, hg, rfl⟩))
    · intro φ hφ
      rintro _ ⟨g, hg, rfl⟩
      obtain ⟨τ, hτ, h⟩ := hT φ hφ
      have hτV : τ ∈ V := Subgroup.subset_closure (Or.inr hτ)
      show j (φ g) ∈ V
      have := h g
      simp only [MonoidHom.id_apply] at this
      rw [← this]
      exact V.mul_mem (V.mul_mem hτV hg) (V.inv_mem hτV)

end TheoremA.Kernel
