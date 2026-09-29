module

public import RequestProject.TheoremA.Groups.HBJoin

/-!
# The homological rope trick, part 1: the double `L` and its map `α` to `Q`

Let `F = FreeGroup (Fin d)`, `N ⊴ F`, `Q = F ⧸ N`, and let
`C = ⟨F, t | t n t⁻¹ = n (n ∈ N)⟩` be the centralizing HNN extension.  In `C` put
`xᵢ = of (of i)`, `yᵢ = t xᵢ t⁻¹`, `L' = ⟨x, y⟩`.

A homomorphism `θ : C → (Q × Q) ⋊ ℤ` (`ℤ` acting by swapping the factors, `f ↦ ((π f, 1), 0)`,
`t ↦ ((1, 1), 1)`) maps `L'` into `Q × Q`; its first coordinate is a homomorphism
`α' : L' → Q` with `α'(xᵢ) = π(xᵢ)` and `α'(yᵢ) = 1`.  No normal form theorem is needed.

For an injective `g : C → B` the same holds for `L = g(L') = ⟨g x, g y⟩ ≤ B`
(`ropeAlpha`, `ropeAlpha_x`, `ropeAlpha_y`).  In `B`, `g(yᵣ) = g(xᵣ)` for every word `r ∈ N`.
-/

@[expose] public section

namespace TheoremA.RelPres

open HNNExtension

universe u

section Alpha

variable {d : ℕ} (N : Subgroup (FreeGroup (Fin d))) [N.Normal]

/-- The centralizing HNN extension `C(F, N)`. -/
abbrev CentHNN : Type := HNNExtension (FreeGroup (Fin d)) N N (MulEquiv.refl N)

/-- The swap action of `ℤ` on `Q × Q`. -/
def swapAct (Q : Type*) [Group Q] : Multiplicative ℤ →* MulAut (Q × Q) :=
  zpowersHom _ MulEquiv.prodComm

/-- The target `(Q × Q) ⋊ ℤ`. -/
abbrev SwapW : Type :=
  SemidirectProduct ((FreeGroup (Fin d) ⧸ N) × (FreeGroup (Fin d) ⧸ N)) (Multiplicative ℤ)
    (swapAct _)

/-- `θ : C(F, N) → (Q × Q) ⋊ ℤ`. -/
noncomputable def thetaMap : CentHNN N →* SwapW N :=
  HNNExtension.lift
    (SemidirectProduct.inl.comp ((MonoidHom.inl _ _).comp (QuotientGroup.mk' N)))
    (SemidirectProduct.inr (Multiplicative.ofAdd 1)) (by
      intro a
      have h : ((a : FreeGroup (Fin d)) : FreeGroup (Fin d) ⧸ N) = 1 :=
        (QuotientGroup.eq_one_iff _).2 a.2
      simp [h, Prod.mk_one_one])

theorem thetaMap_of (f : FreeGroup (Fin d)) :
    thetaMap N (of f) = SemidirectProduct.inl ((f : FreeGroup (Fin d) ⧸ N), 1) := by
  simp [thetaMap]

theorem thetaMap_conj (f : FreeGroup (Fin d)) :
    thetaMap N (t * of f * t⁻¹) = SemidirectProduct.inl (1, (f : FreeGroup (Fin d) ⧸ N)) := by
  rw [map_mul, map_mul, map_inv, thetaMap_of]
  simp only [thetaMap, lift_t]
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  simp [swapAct]

/-- The generators `xᵢ` of `C`. -/
def ropeXs (i : Fin d) : CentHNN N := of (FreeGroup.of i)

/-- The generators `yᵢ = t xᵢ t⁻¹` of `C`. -/
noncomputable def ropeYs (i : Fin d) : CentHNN N := t * of (FreeGroup.of i) * t⁻¹

/-- `L' = ⟨x, y⟩ ≤ C`. -/
def ropeL' : Subgroup (CentHNN N) := Subgroup.closure (Set.range (ropeXs N) ∪ Set.range (ropeYs N))

theorem thetaMap_right (l : ropeL' N) : (thetaMap N l).right = 1 := by
  have : ropeL' N ≤ (SemidirectProduct.rightHom.comp (thetaMap N)).ker := by
    rw [ropeL', Subgroup.closure_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · simp [ropeXs, thetaMap_of]
    · simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, ropeYs]
      rw [thetaMap_conj]; simp
  simpa using this l.2

/-- `α' : L' → Q`, the first coordinate of `θ`. -/
noncomputable def alphaC : ropeL' N →* FreeGroup (Fin d) ⧸ N :=
  MonoidHom.mk' (fun l => (thetaMap N l).left.1) (by
    intro a b
    dsimp only
    rw [Subgroup.coe_mul, map_mul, SemidirectProduct.mul_left, thetaMap_right N a, map_one,
      MulAut.one_apply]
    rfl)

theorem alphaC_x (i : Fin d) (h : ropeXs N i ∈ ropeL' N) :
    alphaC N ⟨ropeXs N i, h⟩ = ((FreeGroup.of i : FreeGroup (Fin d)) : FreeGroup (Fin d) ⧸ N) := by
  simp [alphaC, ropeXs, thetaMap_of]

theorem alphaC_y (i : Fin d) (h : ropeYs N i ∈ ropeL' N) : alphaC N ⟨ropeYs N i, h⟩ = 1 := by
  simp only [alphaC, MonoidHom.mk'_apply, ropeYs]
  rw [thetaMap_conj]; simp

theorem centHNN_conj_of_mem (r : FreeGroup (Fin d)) (hr : r ∈ N) :
    (t * of r * t⁻¹ : CentHNN N) = of r :=
  conj_t_of_mem_centralizing N r hr

variable {B : Type u} [Group B] (gC : CentHNN N →* B) (hg : Function.Injective gC)

/-- `x_i ∈ B`. -/
noncomputable def ropeXB (i : Fin d) : B := gC (ropeXs N i)

/-- `y_i ∈ B`. -/
noncomputable def ropeYB (i : Fin d) : B := gC (ropeYs N i)

/-- `L = ⟨x, y⟩ ≤ B`. -/
noncomputable def ropeL : Subgroup B := Subgroup.closure (Set.range (ropeXB N gC) ∪ Set.range (ropeYB N gC))

theorem ropeL'_map : (ropeL' N).map gC = ropeL N gC := by
  rw [ropeL', MonoidHom.map_closure, Set.image_union, ← Set.range_comp, ← Set.range_comp]
  rfl

/-- `L' ≃* L`. -/
noncomputable def ropeLEquiv : ropeL' N ≃* ropeL N gC :=
  ((ropeL' N).equivMapOfInjective gC hg).trans (MulEquiv.subgroupCongr (ropeL'_map N gC))

theorem ropeLEquiv_apply (l : ropeL' N) : (ropeLEquiv N gC hg l : B) = gC l := rfl

/-- **`α : L → Q`.** -/
noncomputable def ropeAlpha : ropeL N gC →* FreeGroup (Fin d) ⧸ N :=
  (alphaC N).comp (ropeLEquiv N gC hg).symm.toMonoidHom

theorem ropeXB_mem (i : Fin d) : ropeXB N gC i ∈ ropeL N gC :=
  Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)

theorem ropeYB_mem (i : Fin d) : ropeYB N gC i ∈ ropeL N gC :=
  Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)

theorem ropeXs_mem (i : Fin d) : ropeXs N i ∈ ropeL' N :=
  Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)

theorem ropeYs_mem (i : Fin d) : ropeYs N i ∈ ropeL' N :=
  Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)

theorem ropeAlpha_x (i : Fin d) :
    ropeAlpha N gC hg ⟨ropeXB N gC i, ropeXB_mem N gC i⟩ =
      ((FreeGroup.of i : FreeGroup (Fin d)) : FreeGroup (Fin d) ⧸ N) := by
  have : (ropeLEquiv N gC hg).symm ⟨ropeXB N gC i, ropeXB_mem N gC i⟩ =
      ⟨ropeXs N i, ropeXs_mem N i⟩ :=
    (MulEquiv.symm_apply_eq _).2 (Subtype.ext rfl)
  simp only [ropeAlpha, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, alphaC_x]

theorem ropeAlpha_y (i : Fin d) :
    ropeAlpha N gC hg ⟨ropeYB N gC i, ropeYB_mem N gC i⟩ = 1 := by
  have : (ropeLEquiv N gC hg).symm ⟨ropeYB N gC i, ropeYB_mem N gC i⟩ =
      ⟨ropeYs N i, ropeYs_mem N i⟩ :=
    (MulEquiv.symm_apply_eq _).2 (Subtype.ext rfl)
  simp only [ropeAlpha, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this, alphaC_y]

/-- The substitution homomorphism `r ↦ r(x)` into `B`. -/
noncomputable def ropeXHom : FreeGroup (Fin d) →* B := gC.comp of

/-- The substitution homomorphism `r ↦ r(y)` into `B`. -/
noncomputable def ropeYHom : FreeGroup (Fin d) →* B :=
  gC.comp ((MulAut.conj (t : CentHNN N)).toMonoidHom.comp of)

theorem ropeXHom_of (i : Fin d) : ropeXHom N gC (FreeGroup.of i) = ropeXB N gC i := rfl

theorem ropeYHom_of (i : Fin d) : ropeYHom N gC (FreeGroup.of i) = ropeYB N gC i := rfl

/-- **`r(y) = r(x)` in `B` for every `r ∈ N`.** -/
theorem ropeYHom_eq_of_mem (r : FreeGroup (Fin d)) (hr : r ∈ N) :
    ropeYHom N gC r = ropeXHom N gC r := by
  simp only [ropeYHom, ropeXHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  rw [centHNN_conj_of_mem N r hr]

/-- The generators of `L`, inside `L`. -/
theorem ropeL_closure_gens : Subgroup.closure
    ((ropeL N gC).subtype ⁻¹' (Set.range (ropeXB N gC) ∪ Set.range (ropeYB N gC))) = ⊤ :=
  Subgroup.closure_closure_coe_preimage

end Alpha

end TheoremA.RelPres
