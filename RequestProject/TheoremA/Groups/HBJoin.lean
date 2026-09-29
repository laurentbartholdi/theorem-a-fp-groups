module

public import RequestProject.TheoremA.Groups.HB
public import RequestProject.TheoremA.Groups.Britton

/-!
# `HB_R`: joins with finitely generated subgroups, and the centralizing HNN form

* `HB.sup_fg` — if `G` is finitely generated, `N` is `HB_R` and `K` is finitely generated, then
  `N ⊔ K` is `HB_R`.  (Adjoin to the witness `P` a stable letter centralizing `V`; the detecting
  subgroup is `⟨f K, t f(G) t⁻¹⟩`, and the centralizing join lemma of `Britton.lean` computes its
  intersection with `f(G)`.)
* `HB.exists_centralizing_embedding` — `HB_R(G, N)` gives an injective homomorphism from the
  centralizing HNN extension `⟨G, t | t n t⁻¹ = n (n ∈ N)⟩` into a group of `C_R` of type `FP₂`
  (HNN functoriality).
-/

@[expose] public section

namespace TheoremA.RelPres

open HNNExtension TheoremA.Britton

universe u

variable {R : Set ℕ}

theorem conj_t_of_mem_centralizing {P : Type*} [Group P] (V : Subgroup P) (v : P) (hv : v ∈ V) :
    (t * of v * t⁻¹ : HNNExtension P V V (MulEquiv.refl V)) = of v := by
  have := equiv_eq_conj (φ := MulEquiv.refl V) ⟨v, hv⟩
  simpa using this.symm

/-- The centralizing HNN extension of a witness is again a suitable group. -/
theorem classCR_isFP_two_centralizing {P : Type u} [Group P] (h1 : ClassCR R P) (h2 : IsFP 2 P)
    (V : Subgroup P) (hV : V.FG) :
    ClassCR R (HNNExtension P V V (MulEquiv.refl V)) ∧
      IsFP 2 (HNNExtension P V V (MulEquiv.refl V)) :=
  classCR_isFP_two_hnn h1 h2 (MulEquiv.refl V) ((Group.fg_iff_subgroup_fg V).2 hV)

/-- **Join with a finitely generated subgroup.** -/
theorem HB.sup_fg {G : Type u} [Group G] (hG : Group.FG G) {N : Subgroup G} (hN : HB R N)
    {K : Subgroup G} (hK : K.FG) : HB R (N ⊔ K) := by
  obtain ⟨P, _, h1, h2, f, hf, V, hV, rfl⟩ := hN
  obtain ⟨c, d⟩ := classCR_isFP_two_centralizing h1 h2 V hV
  let E := HNNExtension P V V (MulEquiv.refl V)
  let conjT : E →* E := (MulAut.conj (t : E)).toMonoidHom
  let Z : Subgroup E := (K.map f).map (of : P →* E) ⊔ (f.range.map (of : P →* E)).map conjT
  have hGr : f.range.FG := by
    rw [MonoidHom.range_eq_map]
    exact Subgroup.fg_map' f hG.out
  refine ⟨E, _, c, d, (of : P →* E).comp f, (by rw [MonoidHom.coe_comp]; exact (of_injective (φ := MulEquiv.refl V)).comp hf), Z,
    (Subgroup.fg_map' _ (Subgroup.fg_map' _ hK)).sup
      (Subgroup.fg_map' _ (Subgroup.fg_map' _ hGr)), ?_⟩
  let W₀ : Subgroup P := ((V.comap f) ⊔ K).map f
  have hXV : f.range ⊓ V ≤ W₀ := by
    rintro _ ⟨⟨g, rfl⟩, hv⟩
    exact ⟨g, Subgroup.mem_sup_left hv, rfl⟩
  have hWV : W₀ ⊓ V ≤ f.range := by
    rintro _ ⟨⟨g, -, rfl⟩, -⟩
    exact ⟨g, rfl⟩
  ext x
  simp only [Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · intro hx
    have hZ : Z ≤ Subgroup.closure ((of '' (W₀ : Set P)) ∪
        ((fun y => t * of y * t⁻¹) '' (f.range : Set P))) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
        exact Subgroup.subset_closure (Or.inl ⟨f k, ⟨k, Subgroup.mem_sup_right hk, rfl⟩, rfl⟩)
      · rintro _ ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, rfl⟩
        exact Subgroup.subset_closure (Or.inr ⟨f g, ⟨g, rfl⟩, rfl⟩)
    obtain ⟨w, hw, hweq⟩ := mem_of_mem_closure_centralizing V f.range W₀ hXV hWV
      (of (f x)) (hZ hx) ⟨f x, rfl⟩
    have : w = f x := of_injective (φ := MulEquiv.refl V) hweq
    subst this
    exact (Subgroup.mem_map_iff_mem hf).1 hw
  · intro hx
    have hle : V.comap f ⊔ K ≤ Z.comap ((of : P →* E).comp f) := by
      refine sup_le ?_ ?_
      · intro n hn
        simp only [Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply] at hn ⊢
        refine Subgroup.mem_sup_right ⟨of (f n), ⟨f n, ⟨n, rfl⟩, rfl⟩, ?_⟩
        exact conj_t_of_mem_centralizing V (f n) hn
      · intro k hk
        exact Subgroup.mem_sup_left ⟨f k, ⟨k, hk, rfl⟩, rfl⟩
    exact hle hx

/-- **From an `HB_R` witness to an embedding of the centralizing HNN extension.** -/
theorem HB.exists_centralizing_embedding {G : Type u} [Group G] {N : Subgroup G}
    (hN : HB R N) : ∃ (B : Type u) (_ : Group B), ClassCR R B ∧ IsFP 2 B ∧
      ∃ g : HNNExtension G N N (MulEquiv.refl N) →* B, Function.Injective g := by
  obtain ⟨P, _, h1, h2, f, hf, V, hV, rfl⟩ := hN
  obtain ⟨c, d⟩ := classCR_isFP_two_centralizing h1 h2 V hV
  exact ⟨_, _, c, d, hnnMap (MulEquiv.refl _) (MulEquiv.refl V) f (fun a ha => ha)
    (fun a => rfl), hnnMap_injective _ _ _ _ _ hf (fun g hg => hg) (fun g hg => hg)⟩

end TheoremA.RelPres
