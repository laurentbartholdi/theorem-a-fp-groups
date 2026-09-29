module

public import RequestProject.TheoremA.Groups.ProdAmalgPres

/-!
# Relative homological benignness `HB_R`

`HB R N` (for a subgroup `N` of a group `G`) asserts that there is a group `P` in `C_R` of type
`FP₂`, an injective homomorphism `f : G → P` and a finitely generated subgroup `V ≤ P` with
`f⁻¹(V) = N`.  All closure properties below keep the same oracle `R`.

* `HB.of_fg` — finitely generated subgroups of a group that embeds in a suitable group;
* `HB.comap` — pullback along an injective homomorphism;
* `HB.map_equiv` — transport along isomorphisms;
* `HB.inf` — intersections (via direct products);
* `HB.transfer` — ambient transfer to a larger group that itself embeds in a suitable group
  (via amalgamation over the finitely generated smaller group).
-/

@[expose] public section

namespace TheoremA.RelPres

universe u

/-- Relative homological benignness with oracle `R`. -/
def HB (R : Set ℕ) {G : Type u} [Group G] (N : Subgroup G) : Prop :=
  ∃ (P : Type u) (_ : Group P), ClassCR R P ∧ IsFP 2 P ∧
    ∃ f : G →* P, Function.Injective f ∧ ∃ V : Subgroup P, V.FG ∧ V.comap f = N

/-- `G` embeds in a group of `C_R` of type `FP₂`. -/
def EmbedsSuitable (R : Set ℕ) (G : Type u) [Group G] : Prop :=
  ∃ (P : Type u) (_ : Group P), ClassCR R P ∧ IsFP 2 P ∧ ∃ f : G →* P, Function.Injective f

theorem Subgroup.fg_map' {G P : Type*} [Group G] [Group P] (f : G →* P) {H : Subgroup G}
    (hH : H.FG) : (H.map f).FG := by
  obtain ⟨s, rfl⟩ := hH
  classical
  refine ⟨s.image f, ?_⟩
  rw [MonoidHom.map_closure, Finset.coe_image]

theorem Subgroup.fg_prod' {G P : Type*} [Group G] [Group P] {H : Subgroup G} {K : Subgroup P}
    (hH : H.FG) (hK : K.FG) : (H.prod K).FG := by
  have : H.prod K = H.map (MonoidHom.inl G P) ⊔ K.map (MonoidHom.inr G P) := by
    apply le_antisymm
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      have : ((a, b) : G × P) = MonoidHom.inl G P a * MonoidHom.inr G P b := by simp
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨a, ha, rfl⟩)
        (Subgroup.mem_sup_right ⟨b, hb, rfl⟩)
    · refine sup_le ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩; exact ⟨ha, K.one_mem⟩
      · rintro _ ⟨b, hb, rfl⟩; exact ⟨H.one_mem, hb⟩
  rw [this]
  exact (Subgroup.fg_map' _ hH).sup (Subgroup.fg_map' _ hK)

variable {R : Set ℕ}

theorem HB.embedsSuitable {G : Type u} [Group G] {N : Subgroup G} (h : HB R N) :
    EmbedsSuitable R G := by
  obtain ⟨P, _, h1, h2, f, hf, -⟩ := h
  exact ⟨P, _, h1, h2, f, hf⟩

/-- Finitely generated subgroups are `HB_R` in any group embedding in a suitable group. -/
theorem HB.of_fg {G : Type u} [Group G] (hG : EmbedsSuitable R G) {N : Subgroup G}
    (hN : N.FG) : HB R N := by
  obtain ⟨P, _, h1, h2, f, hf⟩ := hG
  exact ⟨P, _, h1, h2, f, hf, N.map f, Subgroup.fg_map' f hN,
    Subgroup.comap_map_eq_self_of_injective hf N⟩

/-- Pullback along an injective homomorphism. -/
theorem HB.comap {G₀ G : Type u} [Group G₀] [Group G] {N : Subgroup G} (h : HB R N)
    (g : G₀ →* G) (hg : Function.Injective g) : HB R (N.comap g) := by
  obtain ⟨P, _, h1, h2, f, hf, V, hV, rfl⟩ := h
  exact ⟨P, _, h1, h2, f.comp g, hf.comp hg, V, hV, rfl⟩

/-- Transport along isomorphisms. -/
theorem HB.map_equiv {G G' : Type u} [Group G] [Group G'] {N : Subgroup G} (h : HB R N)
    (e : G ≃* G') : HB R (N.map (e : G →* G')) := by
  have := h.comap (e.symm : G' →* G) e.symm.injective
  rwa [Subgroup.comap_equiv_eq_map_symm] at this

/-- **Intersection closure**, via the diagonal embedding into a direct product. -/
theorem HB.inf {G : Type u} [Group G] {N₀ N₁ : Subgroup G} (h₀ : HB R N₀) (h₁ : HB R N₁) :
    HB R (N₀ ⊓ N₁) := by
  obtain ⟨P₀, _, a₀, b₀, f₀, hf₀, V₀, hV₀, rfl⟩ := h₀
  obtain ⟨P₁, _, a₁, b₁, f₁, hf₁, V₁, hV₁, rfl⟩ := h₁
  obtain ⟨c, d⟩ := classCR_isFP_two_prod a₀ b₀ a₁ b₁
  refine ⟨P₀ × P₁, _, c, d, f₀.prod f₁, fun x y hxy => hf₀ (congrArg Prod.fst hxy),
    V₀.prod V₁, Subgroup.fg_prod' hV₀ hV₁, ?_⟩
  ext x
  simp [Subgroup.mem_prod]

/-- **Ambient transfer**: an `HB_R` witness for `N ≤ G` is promoted along an embedding
`i : G → H` of a finitely generated group into a group `H` that embeds in a suitable group. -/
theorem HB.transfer {G H : Type u} [Group G] [Group H] (hGfg : Group.FG G) {N : Subgroup G}
    (hN : HB R N) (i : G →* H) (hi : Function.Injective i) (hH : EmbedsSuitable R H) :
    HB R (N.map i) := by
  obtain ⟨P, _, a, b, f, hf, V, hV, rfl⟩ := hN
  obtain ⟨Q, _, a', b', k, hk⟩ := hH
  have hki : Function.Injective (k.comp i) := hk.comp hi
  obtain ⟨c, d⟩ := classCR_isFP_two_amalg a b a' b' hGfg f (k.comp i)
  refine ⟨Amalg f (k.comp i), _, c, d, (Amalg.inr f (k.comp i)).comp k,
    (Amalg.inr_injective hf hki).comp hk, V.map (Amalg.inl f (k.comp i)),
    Subgroup.fg_map' _ hV, ?_⟩
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨v, hv, hvx⟩
    have hmem : Amalg.inr f (k.comp i) (k x) ∈
        (Amalg.inl f (k.comp i)).range ⊓ (Amalg.inr f (k.comp i)).range :=
      ⟨⟨v, hvx⟩, ⟨k x, rfl⟩⟩
    rw [Amalg.range_inl_inf_range_inr hf hki] at hmem
    obtain ⟨g, hg⟩ := hmem
    have h1 : Amalg.inr f (k.comp i) (k (i g)) = Amalg.inr f (k.comp i) (k x) := by
      rw [← hg]; exact Amalg.inr_apply f (k.comp i) g
    have hx : i g = x := hk (Amalg.inr_injective hf hki h1)
    have h2 : Amalg.inl f (k.comp i) (f g) = Amalg.inl f (k.comp i) v := by
      rw [hvx, ← hg]; exact Amalg.inl_apply f (k.comp i) g
    have hv' : f g = v := Amalg.inl_injective hf hki h2
    exact ⟨g, show f g ∈ V by rw [hv']; exact hv, hx⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨f g, hg, ?_⟩
    rw [Amalg.inl_apply]
    exact (Amalg.inr_apply f (k.comp i) g).symm

end TheoremA.RelPres
