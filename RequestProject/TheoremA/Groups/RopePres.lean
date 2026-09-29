module

public import RequestProject.TheoremA.Groups.RopeAlpha

/-!
# The homological rope trick, part 2: the group `K` and its finite relative presentation

With the notation of `RopeAlpha.lean` (`N ⊴ F = FreeGroup (Fin d)`, `Q = F ⧸ N`, an injective
`g : C(F, N) → B`, `L = ⟨x, y⟩ ≤ B`, `α : L → Q`), let `K` be the actual HNN extension of
`B × Q` with stable letter `t` and `t (l, 1) t⁻¹ = (l, α l)` (`RopeK`).  `Q` embeds in `K`
by `q ↦ of (1, q)`.

Given a presentation `ψ : ⟨b₁ … bₙ | S⟩ ≃* B`, `K` has the finite relative presentation
(`ropePresEquiv`) on `b₁ … bₙ, z₁ … z_d, s` with the old relators `S` and only the finite
families

    [bⱼ, zᵢ],     s Xᵢ s⁻¹ = Xᵢ zᵢ,     s Yᵢ s⁻¹ = Yᵢ

(`Xᵢ`, `Yᵢ` words for `xᵢ`, `yᵢ`).  The relators of `Q` are **not** added: they follow, since for
`r ∈ N`, `r(x) = r(y)` in `B` and hence `r(x) r(z) = s r(x) s⁻¹ = s r(y) s⁻¹ = r(y) = r(x)`
(`ropeZeta_eq_one`).

`rope_trick`: **if `N ⊴ FreeGroup (Fin d)` is `HB_R`, then `F ⧸ N` embeds in a group of `C_R`
(same `R`) of type `FP₂`.**
-/

@[expose] public section

namespace TheoremA.RelPres

open HNNExtension

universe u

section RopeK

variable {d : ℕ} (N : Subgroup (FreeGroup (Fin d))) [N.Normal]
  {B : Type u} [Group B] (gC : CentHNN N →* B) (hg : Function.Injective gC)

/-- `Q = F ⧸ N`. -/
abbrev RopeQ : Type := FreeGroup (Fin d) ⧸ N

/-- `l ↦ (l, 1)`. -/
noncomputable def ropeι₁ : ropeL N gC →* B × RopeQ N := (ropeL N gC).subtype.prod 1

/-- `l ↦ (l, α l)`. -/
noncomputable def ropeι₂ : ropeL N gC →* B × RopeQ N :=
  (ropeL N gC).subtype.prod (ropeAlpha N gC hg)

theorem ropeι₁_injective : Function.Injective (ropeι₁ N gC) :=
  fun _ _ h => Subtype.ext (congrArg Prod.fst h)

theorem ropeι₂_injective : Function.Injective (ropeι₂ N gC hg) :=
  fun _ _ h => Subtype.ext (congrArg Prod.fst h)

/-- The associated subgroups and their isomorphism. -/
noncomputable def ropePhi : (ropeι₁ N gC).range ≃* (ropeι₂ N gC hg).range :=
  (MonoidHom.ofInjective (ropeι₁_injective N gC)).symm.trans
    (MonoidHom.ofInjective (ropeι₂_injective N gC hg))

/-- **The group `K`.** -/
abbrev RopeK : Type u :=
  HNNExtension (B × RopeQ N) (ropeι₁ N gC).range (ropeι₂ N gC hg).range (ropePhi N gC hg)

theorem ropePhi_apply (l : ropeL N gC) :
    (ropePhi N gC hg ⟨ropeι₁ N gC l, ⟨l, rfl⟩⟩ : B × RopeQ N) = ropeι₂ N gC hg l := by
  have : (MonoidHom.ofInjective (ropeι₁_injective N gC)).symm ⟨ropeι₁ N gC l, ⟨l, rfl⟩⟩ = l :=
    (MulEquiv.symm_apply_eq _).2 (Subtype.ext (MonoidHom.ofInjective_apply _).symm)
  simp only [ropePhi, MulEquiv.trans_apply, this, MonoidHom.ofInjective_apply]

/-- **The defining relation** `t (l, 1) t⁻¹ = (l, α l)`. -/
theorem ropeK_conj (l : ropeL N gC) :
    (t * of ((l : B), (1 : RopeQ N)) * t⁻¹ : RopeK N gC hg) =
      of ((l : B), ropeAlpha N gC hg l) := by
  have := equiv_eq_conj (φ := ropePhi N gC hg) ⟨ropeι₁ N gC l, ⟨l, rfl⟩⟩
  rw [ropePhi_apply] at this
  exact this.symm

/-- **`Q` embeds in `K`.** -/
theorem ropeQ_injective :
    Function.Injective ((of : B × RopeQ N →* RopeK N gC hg).comp (MonoidHom.inr B (RopeQ N))) := by
  rw [MonoidHom.coe_comp]
  exact (of_injective (φ := ropePhi N gC hg)).comp (fun _ _ h => congrArg Prod.snd h)

end RopeK

section RopePres

variable {d : ℕ} (N : Subgroup (FreeGroup (Fin d))) [N.Normal]
  {B : Type u} [Group B] (gC : CentHNN N →* B) (hg : Function.Injective gC)
  {n : ℕ} {S : Set (FreeGroup (Fin n))} (ψ : PresentedGroup S ≃* B)

/-- Old letters. -/
def ropeBL (d : ℕ) (j : Fin n) : Fin (n + (d + 1)) := Fin.castAdd (d + 1) j

/-- The letters `zᵢ`. -/
def ropeZL (n : ℕ) (i : Fin d) : Fin (n + (d + 1)) := Fin.natAdd n (Fin.castAdd 1 i)

/-- The letter `s`. -/
def ropeSL (n d : ℕ) : Fin (n + (d + 1)) := Fin.natAdd n (Fin.natAdd d 0)

/-- Words for `xᵢ`. -/
noncomputable def ropeXw (i : Fin d) : RawWord (Fin (n + (d + 1))) :=
  RawWord.rename (Fin.castAdd (d + 1)) (wordFor ψ (ropeXB N gC i))

/-- Words for `yᵢ`. -/
noncomputable def ropeYw (i : Fin d) : RawWord (Fin (n + (d + 1))) :=
  RawWord.rename (Fin.castAdd (d + 1)) (wordFor ψ (ropeYB N gC i))

/-- `[bⱼ, zᵢ]`. -/
def ropeCommRel (j : Fin n) (i : Fin d) : RawWord (Fin (n + (d + 1))) :=
  [(ropeBL d j, true)] ++ [(ropeZL n i, true)] ++ [(ropeBL d j, false)] ++ [(ropeZL n i, false)]

/-- `s Xᵢ s⁻¹ (Xᵢ zᵢ)⁻¹`. -/
noncomputable def ropeXRel (i : Fin d) : RawWord (Fin (n + (d + 1))) :=
  [(ropeSL n d, true)] ++ ropeXw N gC ψ i ++ [(ropeSL n d, false)] ++
    RawWord.inv (ropeXw N gC ψ i ++ [(ropeZL n i, true)])

/-- `s Yᵢ s⁻¹ Yᵢ⁻¹`. -/
noncomputable def ropeYRel (i : Fin d) : RawWord (Fin (n + (d + 1))) :=
  [(ropeSL n d, true)] ++ ropeYw N gC ψ i ++ [(ropeSL n d, false)] ++
    RawWord.inv (ropeYw N gC ψ i)

/-- **The finite list of extra relators** (no relator of `Q` is included). -/
noncomputable def ropeRels : List (RawWord (Fin (n + (d + 1)))) :=
  (List.finRange n).flatMap (fun j => (List.finRange d).map (ropeCommRel (d := d) j)) ++
    List.ofFn (ropeXRel N gC ψ) ++ List.ofFn (ropeYRel N gC ψ)

/-- The new generators of `K`: `zᵢ ↦ (1, π xᵢ)`, `s ↦ t`. -/
noncomputable def ropeY : Fin (d + 1) → RopeK N gC hg :=
  Fin.append (fun i => of ((1 : B), ((FreeGroup.of i : FreeGroup (Fin d)) : RopeQ N)))
    (fun _ => t)

/-- The base map `B → K`, `b ↦ (b, 1)`. -/
noncomputable def ropeI : B →* RopeK N gC hg := of.comp (MonoidHom.inl B (RopeQ N))

theorem eval_ropeXw (i : Fin d) : FreeGroup.lift (relGens ψ (ropeI N gC hg) (ropeY N gC hg))
    (ropeXw N gC ψ i).eval = ropeI N gC hg (ropeXB N gC i) := by
  rw [ropeXw, RawWord.eval_rename, lift_relGens_castAdd, wordFor_spec]

theorem eval_ropeYw (i : Fin d) : FreeGroup.lift (relGens ψ (ropeI N gC hg) (ropeY N gC hg))
    (ropeYw N gC ψ i).eval = ropeI N gC hg (ropeYB N gC i) := by
  rw [ropeYw, RawWord.eval_rename, lift_relGens_castAdd, wordFor_spec]

theorem relGens_ropeBL (j : Fin n) :
    relGens ψ (ropeI N gC hg) (ropeY N gC hg) (ropeBL d j) = ropeI N gC hg (ψ (PresentedGroup.of j)) := by
  simp [relGens, ropeBL]

theorem relGens_ropeZL (i : Fin d) :
    relGens ψ (ropeI N gC hg) (ropeY N gC hg) (ropeZL n i) =
      of ((1 : B), ((FreeGroup.of i : FreeGroup (Fin d)) : RopeQ N)) := by
  simp [relGens, ropeZL, ropeY]

theorem relGens_ropeSL :
    relGens ψ (ropeI N gC hg) (ropeY N gC hg) (ropeSL n d) = t := by
  simp [relGens, ropeSL, ropeY]

theorem ropeI_apply (b : B) : ropeI N gC hg b = of (b, 1) := rfl

theorem ropeI_mul_z (b : B) (q : RopeQ N) :
    ropeI N gC hg b * of ((1 : B), q) = (of (b, q) : RopeK N gC hg) := by
  rw [ropeI_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem ropeRels_hold : ∀ u ∈ ropeRels N gC ψ,
    FreeGroup.lift (relGens ψ (ropeI N gC hg) (ropeY N gC hg)) u.eval = 1 := by
  intro u hu
  simp only [ropeRels, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_ofFn,
    List.mem_finRange, true_and] at hu
  rcases hu with (⟨j, i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
  · simp only [ropeCommRel, RawWord.eval_append, RawWord.eval_pos, RawWord.eval_neg, map_mul,
      map_inv, FreeGroup.lift_apply_of, relGens_ropeBL, relGens_ropeZL]
    rw [ropeI_apply, ← commutatorElement_def, commutatorElement_eq_one_iff_commute]
    exact Commute.map (Prod.ext (by simp) (by simp)) _
  · simp only [ropeXRel, RawWord.eval_append, RawWord.eval_pos, RawWord.eval_neg,
      RawWord.eval_inv, map_mul, map_inv, FreeGroup.lift_apply_of, relGens_ropeSL,
      relGens_ropeZL, eval_ropeXw]
    rw [ropeI_mul_z, ropeI_apply,
      ropeK_conj N gC hg ⟨ropeXB N gC i, ropeXB_mem N gC i⟩, ropeAlpha_x, mul_inv_cancel]
  · simp only [ropeYRel, RawWord.eval_append, RawWord.eval_pos, RawWord.eval_neg,
      RawWord.eval_inv, map_mul, map_inv, FreeGroup.lift_apply_of, relGens_ropeSL,
      eval_ropeYw]
    rw [ropeI_apply,
      ropeK_conj N gC hg ⟨ropeYB N gC i, ropeYB_mem N gC i⟩, ropeAlpha_y, mul_inv_cancel]

/-! ### Consequences of the relators in the presented group `P` -/

/-- The presented group `P`. -/
abbrev RopeP : Type := PresentedGroup (relExt S (d + 1) (ropeRels N gC ψ))

/-- `B → P`. -/
noncomputable def ropeBP : B →* RopeP N gC ψ := relBase ψ (d + 1) (ropeRels N gC ψ)

/-- `zᵢ ∈ P`. -/
def ropeZP (i : Fin d) : RopeP N gC ψ := PresentedGroup.of (ropeZL n i)

/-- `s ∈ P`. -/
def ropeSP : RopeP N gC ψ := PresentedGroup.of (ropeSL n d)

theorem ropeRel_one {u : RawWord (Fin (n + (d + 1)))} (hu : u ∈ ropeRels N gC ψ) :
    PresentedGroup.mk (relExt S (d + 1) (ropeRels N gC ψ)) u.eval = 1 :=
  PresentedGroup.one_of_mem (Or.inr ⟨u, hu, rfl⟩)

theorem ropeP_comm (j : Fin n) (i : Fin d) :
    Commute (PresentedGroup.of (ropeBL d j) : RopeP N gC ψ) (ropeZP N gC ψ i) := by
  have h := ropeRel_one N gC ψ (u := ropeCommRel j i) (by
    simp [ropeRels, List.mem_flatMap])
  simp only [ropeCommRel, RawWord.eval_append, RawWord.eval_pos, RawWord.eval_neg, map_mul,
    map_inv] at h
  rw [← commutatorElement_eq_one_iff_commute, commutatorElement_def]
  exact h

theorem ropeP_x (i : Fin d) : ropeSP N gC ψ * ropeBP N gC ψ (ropeXB N gC i) * (ropeSP N gC ψ)⁻¹ =
    ropeBP N gC ψ (ropeXB N gC i) * ropeZP N gC ψ i := by
  have h := ropeRel_one N gC ψ (u := ropeXRel N gC ψ i) (by simp [ropeRels])
  simp only [ropeXRel, ropeXw, RawWord.eval_append, RawWord.eval_pos, RawWord.eval_neg,
    RawWord.eval_inv, RawWord.eval_rename, map_mul, map_inv] at h
  rw [ropeBP, ← wordFor_spec ψ (ropeXB N gC i), relBase_mk]
  exact mul_inv_eq_one.1 h

theorem ropeP_y (i : Fin d) : ropeSP N gC ψ * ropeBP N gC ψ (ropeYB N gC i) * (ropeSP N gC ψ)⁻¹ =
    ropeBP N gC ψ (ropeYB N gC i) := by
  have h := ropeRel_one N gC ψ (u := ropeYRel N gC ψ i) (by simp [ropeRels])
  simp only [ropeYRel, ropeYw, RawWord.eval_append, RawWord.eval_pos, RawWord.eval_neg,
    RawWord.eval_inv, RawWord.eval_rename, map_mul, map_inv] at h
  rw [ropeBP, ← wordFor_spec ψ (ropeYB N gC i), relBase_mk]
  exact mul_inv_eq_one.1 h

/-- `ζ : F → P`, `xᵢ ↦ zᵢ`. -/
noncomputable def ropeZeta : FreeGroup (Fin d) →* RopeP N gC ψ := FreeGroup.lift (ropeZP N gC ψ)

theorem ropeP_comm_gen_zeta (j : Fin n) (g : FreeGroup (Fin d)) :
    Commute (PresentedGroup.of (ropeBL d j) : RopeP N gC ψ) (ropeZeta N gC ψ g) := by
  have : (MulAut.conj (PresentedGroup.of (ropeBL d j) : RopeP N gC ψ)).toMonoidHom.comp (ropeZeta N gC ψ) =
      ropeZeta N gC ψ := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ropeZeta,
      FreeGroup.lift_apply_of]
    rw [(ropeP_comm N gC ψ j i).eq, mul_inv_cancel_right]
  have h := DFunLike.congr_fun this g
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem ropeP_comm_bz (b : B) (g : FreeGroup (Fin d)) :
    Commute (ropeBP N gC ψ b) (ropeZeta N gC ψ g) := by
  have : (MulAut.conj (ropeZeta N gC ψ g)).toMonoidHom.comp (ropeBP N gC ψ) = ropeBP N gC ψ := by
    refine hom_ext_presentation ψ fun j => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ropeBP,
      relBase_gen]
    have c := ropeP_comm_gen_zeta N gC ψ j g
    simp only [ropeBL] at c
    rw [← c.eq, mul_inv_cancel_right]
  have h := DFunLike.congr_fun this b
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

/-- **Relator elimination**: `ζ` kills `N`. -/
theorem ropeZeta_eq_one (r : FreeGroup (Fin d)) (hr : r ∈ N) : ropeZeta N gC ψ r = 1 := by
  let bx := (ropeBP N gC ψ).comp (ropeXHom N gC)
  let by' := (ropeBP N gC ψ).comp (ropeYHom N gC)
  let h₁ := (MulAut.conj (ropeSP N gC ψ)).toMonoidHom.comp bx
  let h₂ := (bx.noncommCoprod (ropeZeta N gC ψ) (fun a b => ropeP_comm_bz N gC ψ _ b)).comp
    ((MonoidHom.id _).prod (MonoidHom.id _))
  let h₃ := (MulAut.conj (ropeSP N gC ψ)).toMonoidHom.comp by'
  have e₁₂ : h₁ = h₂ := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    simp only [h₁, h₂, bx, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.prod_apply, MonoidHom.id_apply, MonoidHom.noncommCoprod_apply, ropeXHom_of,
      ropeZeta, FreeGroup.lift_apply_of]
    exact ropeP_x N gC ψ i
  have e₃₄ : h₃ = by' := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    simp only [h₃, by', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      ropeYHom_of]
    exact ropeP_y N gC ψ i
  have k₁ := DFunLike.congr_fun e₁₂ r
  have k₂ := DFunLike.congr_fun e₃₄ r
  simp only [h₁, h₂, h₃, bx, by', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, MonoidHom.prod_apply, MonoidHom.id_apply,
    MonoidHom.noncommCoprod_apply] at k₁ k₂
  rw [ropeYHom_eq_of_mem N gC r hr] at k₂
  rw [k₂] at k₁
  exact mul_eq_left.1 k₁.symm

/-- `ζ̄ : Q → P`. -/
noncomputable def ropeZetaQ : RopeQ N →* RopeP N gC ψ :=
  QuotientGroup.lift N (ropeZeta N gC ψ) fun r hr => (MonoidHom.mem_ker).2 (ropeZeta_eq_one N gC ψ r hr)

theorem ropeZetaQ_mk (g : FreeGroup (Fin d)) :
    ropeZetaQ N gC ψ (g : RopeQ N) = ropeZeta N gC ψ g := QuotientGroup.lift_mk _ _ _

theorem ropeP_comm_bq (b : B) (q : RopeQ N) :
    Commute (ropeBP N gC ψ b) (ropeZetaQ N gC ψ q) := by
  induction q using QuotientGroup.induction_on with
  | H g => rw [ropeZetaQ_mk]; exact ropeP_comm_bz N gC ψ b g

/-- `B × Q → P`. -/
noncomputable def ropeβ₀ : B × RopeQ N →* RopeP N gC ψ :=
  (ropeBP N gC ψ).noncommCoprod (ropeZetaQ N gC ψ) (ropeP_comm_bq N gC ψ)

theorem ropeβ₀_apply (b : B) (q : RopeQ N) :
    ropeβ₀ N gC ψ (b, q) = ropeBP N gC ψ b * ropeZetaQ N gC ψ q := rfl

theorem ropeβ₀_conj (l : ropeL N gC) :
    ropeSP N gC ψ * ropeBP N gC ψ l * (ropeSP N gC ψ)⁻¹ =
      ropeβ₀ N gC ψ (ropeι₂ N gC hg l) := by
  let F₁ := (MulAut.conj (ropeSP N gC ψ)).toMonoidHom.comp
    ((ropeBP N gC ψ).comp (ropeL N gC).subtype)
  let F₂ := (ropeβ₀ N gC ψ).comp (ropeι₂ N gC hg)
  have e : F₁ = F₂ := by
    refine MonoidHom.eq_of_eqOn_dense (ropeL_closure_gens N gC) ?_
    rintro ⟨x, hxL⟩ hx
    simp only [Set.mem_preimage, Subgroup.coe_subtype, Set.mem_union, Set.mem_range] at hx
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · simp only [F₁, F₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Subgroup.coe_subtype, ropeι₂, MonoidHom.prod_apply, ropeβ₀_apply]
      rw [ropeP_x, ropeAlpha_x, ropeZetaQ_mk]
      simp [ropeZeta, ropeZP]
    · simp only [F₁, F₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Subgroup.coe_subtype, ropeι₂, MonoidHom.prod_apply, ropeβ₀_apply]
      rw [ropeP_y, ropeAlpha_y, map_one, mul_one]
  exact DFunLike.congr_fun e l

/-- The backward map `K → P`. -/
noncomputable def ropeβ : RopeK N gC hg →* RopeP N gC ψ :=
  HNNExtension.lift (ropeβ₀ N gC ψ) (ropeSP N gC ψ) (by
    rintro ⟨_, l, rfl⟩
    rw [ropePhi_apply, ← ropeβ₀_conj N gC hg ψ l, inv_mul_cancel_right]
    simp [ropeι₁, ropeβ₀_apply])

/-- **The finite relative presentation of `K`.** -/
noncomputable def ropePresEquiv : RopeP N gC ψ ≃* RopeK N gC hg :=
  relPresEquiv ψ (ropeI N gC hg) (ropeY N gC hg) (ropeRels N gC ψ) (ropeRels_hold N gC hg ψ)
    (ropeβ N gC hg ψ)
    (fun b => by simp [ropeβ, ropeI, ropeβ₀_apply, ropeBP])
    (fun l => by
      refine Fin.addCases (fun i => ?_) (fun l => ?_) l
      · simp only [ropeY, Fin.append_left, ropeβ, lift_of, ropeβ₀_apply, map_one, one_mul]
        rw [ropeZetaQ_mk]
        simp [ropeZeta, ropeZP, ropeZL]
      · simp only [ropeY, Fin.append_right, ropeβ, lift_t, ropeSP, ropeSL]
        rw [Subsingleton.elim l 0])
    (fun f hf hy => by
      apply HNNExtension.hom_ext
      · ext ⟨b, q⟩
        simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
        have hb : f (of (b, 1)) = of (b, 1) := DFunLike.congr_fun hf b
        have hq : f (of ((1 : B), q)) = of ((1 : B), q) := by
          induction q using QuotientGroup.induction_on with
          | H g =>
            let G₁ := f.comp ((of : B × RopeQ N →* RopeK N gC hg).comp
              ((MonoidHom.inr B (RopeQ N)).comp (QuotientGroup.mk' N)))
            let G₂ := (of : B × RopeQ N →* RopeK N gC hg).comp
              ((MonoidHom.inr B (RopeQ N)).comp (QuotientGroup.mk' N))
            have : G₁ = G₂ := FreeGroup.ext_hom _ _ fun i => by
              have := hy (Fin.castAdd 1 i)
              simp only [ropeY, Fin.append_left] at this
              simpa [G₁, G₂] using this
            simpa [G₁, G₂] using DFunLike.congr_fun this g
        have : ((b, q) : B × RopeQ N) = (b, 1) * (1, q) := by simp
        rw [this, map_mul, map_mul, hb, hq]
      · have := hy (Fin.natAdd d 0)
        simpa [ropeY] using this)

end RopePres

/-- **The same-oracle homological rope trick.**  If `N ⊴ FreeGroup (Fin d)` is `HB_R`, then
`FreeGroup (Fin d) ⧸ N` embeds in a group of `C_R` (same `R`) of type `FP₂`. -/
theorem rope_trick {R : Set ℕ} {d : ℕ} (N : Subgroup (FreeGroup (Fin d))) [N.Normal]
    (hN : HB R N) : ∃ (K : Type) (_ : Group K), ClassCR R K ∧ IsFP 2 K ∧
      ∃ f : FreeGroup (Fin d) ⧸ N →* K, Function.Injective f := by
  obtain ⟨B, _, hBC, hBF, gC, hg⟩ := hN.exists_centralizing_embedding
  obtain ⟨n, e, he, ⟨ψ⟩⟩ := hBC
  let Φ := ropePresEquiv N gC hg ψ
  exact ⟨RopeK N gC hg, inferInstance, classCR_of_relPres he _ Φ,
    isFP_two_of_relPres ψ hBF _ Φ, _, ropeQ_injective N gC hg⟩

end TheoremA.RelPres
