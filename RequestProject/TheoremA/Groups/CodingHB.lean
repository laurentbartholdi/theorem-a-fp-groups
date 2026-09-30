module

public import RequestProject.TheoremA.Groups.CodingVS
public import RequestProject.TheoremA.Groups.HBJoin
public import RequestProject.TheoremA.FP2.PresentationCriterion

/-!
# `HB_R(V_S)`: the relative form of [Leary 2018, Lemma 2.4]

* `classCR_isFP_two_freeGroup` — free groups of finite rank are in `C_R` and of type `FP₂`;
* `coprodIEquiv` — the two-factor free product `CoprodI (amalgFam B₀ B₁) ≃* B₀ ∗ B₁`;
* `psi` — the automorphisms `ψ_s` of `F_c` with `ψ_s(v_r) = v_{r+s}`; `hb_VZ`: `V_ℤ` is `HB_R`
  (via the HNN extension by `ψ₁` and Britton's lemma);
* `hb_VS` — if `J ∈ C_R` has type `FP₂` and `j₁, …, j_ℓ ∈ J` detect `S ∋ 0`, then `V_S` is `HB_R`
  in `F_c` (via the HNN extension of `A₃ ∗ (F(ℓ) × J)` identifying the untwisted and the twisted
  copy of `F_c`).
-/

@[expose] public section

namespace TheoremA.Coding

open Monoid NF TheoremA.RelPres TheoremA.Britton HNNExtension

universe u

variable {R : Set ℕ}

/-! ### Suitability of free groups and two-factor free products -/

theorem presentedGroupEmptyEquiv (n : ℕ) :
    Nonempty (PresentedGroup (∅ : Set (FreeGroup (Fin n))) ≃* FreeGroup (Fin n)) := by
  have h : Subgroup.normalClosure (∅ : Set (FreeGroup (Fin n))) = ⊥ :=
    le_bot_iff.1 (Subgroup.normalClosure_le_normal (Set.empty_subset _))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot⟩

theorem classCR_isFP_two_freeGroup (n : ℕ) :
    ClassCR R (FreeGroup (Fin n)) ∧ IsFP 2 (FreeGroup (Fin n)) := by
  obtain ⟨e⟩ := presentedGroupEmptyEquiv n
  refine ⟨⟨n, noneEnum, IsEnumerator.noneEnum, ⟨?_⟩⟩, ?_⟩
  · rw [enumRelators_noneEnum]; exact e
  · exact IsFP.of_mulEquiv e (isFP_two_presentedGroup_of_finite _ Set.finite_empty)

theorem classCR_isFP_two_freeGroup' (X : Type) [Finite X] :
    ClassCR R (FreeGroup X) ∧ IsFP 2 (FreeGroup X) := by
  obtain ⟨n, ⟨eX⟩⟩ := Finite.exists_equiv_fin X
  obtain ⟨h1, h2⟩ := classCR_isFP_two_freeGroup (R := R) n
  exact ⟨h1.of_mulEquiv (FreeGroup.freeGroupCongr eX.symm),
    IsFP.of_mulEquiv (FreeGroup.freeGroupCongr eX.symm) h2⟩

section CoprodI2

variable {B₀ B₁ : Type u} [Group B₀] [Group B₁]

/-- `CoprodI` over `Bool` is the binary free product. -/
def coprodIEquiv : CoprodI (amalgFam B₀ B₁) ≃* Monoid.Coprod B₀ B₁ :=
  MonoidHom.toMulEquiv (CoprodI.lift (amalgLiftFam Monoid.Coprod.inl Monoid.Coprod.inr))
    (Monoid.Coprod.lift (CoprodI.of (M := amalgFam B₀ B₁) (i := false))
      (CoprodI.of (M := amalgFam B₀ B₁) (i := true)))
    (by
      apply CoprodI.ext_hom
      intro b
      cases b
      · ext x
        simp only [MonoidHom.comp_apply]
        erw [CoprodI.lift_of]
      · ext x
        simp only [MonoidHom.comp_apply]
        erw [CoprodI.lift_of])
    (by
      apply Monoid.Coprod.hom_ext
      · ext x
        simp only [MonoidHom.comp_apply, Monoid.Coprod.lift_apply_inl]
        exact CoprodI.lift_of (N := Monoid.Coprod B₀ B₁) (amalgLiftFam _ _) (i := false) x
      · ext x
        simp only [MonoidHom.comp_apply, Monoid.Coprod.lift_apply_inr]
        exact CoprodI.lift_of (N := Monoid.Coprod B₀ B₁) (amalgLiftFam _ _) (i := true) x)

theorem classCR_isFP_two_coprodI (h₀ : ClassCR R B₀) (h₀' : IsFP 2 B₀) (h₁ : ClassCR R B₁)
    (h₁' : IsFP 2 B₁) :
    ClassCR R (CoprodI (amalgFam B₀ B₁)) ∧ IsFP 2 (CoprodI (amalgFam B₀ B₁)) := by
  obtain ⟨c, d⟩ := classCR_isFP_two_coprod h₀ h₀' h₁ h₁'
  exact ⟨c.of_mulEquiv coprodIEquiv.symm, IsFP.of_mulEquiv coprodIEquiv.symm d⟩

end CoprodI2

variable {ℓ : ℕ}

theorem classCR_isFP_two_Fc : ClassCR R (Fc ℓ) ∧ IsFP 2 (Fc ℓ) :=
  classCR_isFP_two_freeGroup' _

theorem fg_Fc : Group.FG (Fc ℓ) := (classCR_isFP_two_Fc (R := ∅)).1.fg

/-! ### The automorphisms `ψ_s` and `HB_R(V_ℤ)` -/

/-- `Q s i = c₀^s c₁^s ⋯ c_i^s` (the first `i` of `c₁, …, c_ℓ`). -/
def Q (s : ℤ) (i : ℕ) : Fc ℓ := c0 ^ s * ((List.ofFn fun k : Fin ℓ => cc k ^ s).take i).prod

theorem Q_zero (s : ℤ) : (Q s 0 : Fc ℓ) = c0 ^ s := by simp [Q]

theorem Q_succ (s : ℤ) {i : ℕ} (hi : i < ℓ) : (Q s (i + 1) : Fc ℓ) = Q s i * cc ⟨i, hi⟩ ^ s := by
  rw [Q, Q, List.prod_take_succ _ _ (by simpa using hi), mul_assoc]
  simp

theorem Q_top (s : ℤ) : (Q s ℓ : Fc ℓ) = c0 ^ s * Cs s := by
  rw [Q, List.take_of_length_le (by simp)]; rfl

theorem vv_eq_Q (s : ℤ) : (vv s : Fc ℓ) = Q s ℓ * dd * ee ^ s := by
  rw [Q_top, vv]

/-- `ψ_s`. -/
def psi (s : ℤ) : Fc ℓ →* Fc ℓ :=
  FreeGroup.lift (Sum.elim ![c0, Q s ℓ * dd * ee ^ s, ee]
    (fun i => Q s i * cc i * (Q s i)⁻¹))

theorem psi_c0 (s : ℤ) : psi s (c0 : Fc ℓ) = c0 := by simp [psi, c0]
theorem psi_dd (s : ℤ) : psi s (dd : Fc ℓ) = Q s ℓ * dd * ee ^ s := by simp [psi, dd]
theorem psi_ee (s : ℤ) : psi s (ee : Fc ℓ) = ee := by simp [psi, ee]
theorem psi_cc (s : ℤ) (i : Fin ℓ) : psi s (cc i) = Q s i * cc i * (Q s i)⁻¹ := by
  simp [psi, cc]

theorem psi_Q (s r : ℤ) : ∀ i ≤ ℓ, psi s (Q r i : Fc ℓ) = Q (r + s) i * (Q s i)⁻¹
  | 0, _ => by
    rw [Q_zero, Q_zero, Q_zero, map_zpow, psi_c0, zpow_add]; group
  | i + 1, hi => by
    rw [Q_succ r (by omega), map_mul, psi_Q s r i (by omega), map_zpow, psi_cc, Q_succ _ (by omega),
      Q_succ _ (by omega)]
    simp only [conj_zpow, zpow_add]
    group

theorem psi_vv (s r : ℤ) : psi s (vv r : Fc ℓ) = vv (r + s) := by
  rw [vv_eq_Q, vv_eq_Q, map_mul, map_mul, psi_Q s r ℓ le_rfl, psi_dd, map_zpow, psi_ee, zpow_add]
  group

theorem psi_comp (s r : ℤ) : (psi s).comp (psi r) = (psi (r + s) : Fc ℓ →* Fc ℓ) := by
  ext k
  rcases k with k | i
  · fin_cases k
    · change psi s (psi r (c0 : Fc ℓ)) = psi (r + s) c0
      rw [psi_c0, psi_c0, psi_c0]
    · change psi s (psi r (dd : Fc ℓ)) = psi (r + s) dd
      rw [psi_dd, psi_dd, map_mul, map_mul, psi_Q s r ℓ le_rfl, psi_dd, map_zpow, psi_ee,
        zpow_add]
      group
    · change psi s (psi r (ee : Fc ℓ)) = psi (r + s) ee
      rw [psi_ee, psi_ee, psi_ee]
  · change psi s (psi r (cc i : Fc ℓ)) = psi (r + s) (cc i)
    rw [psi_cc, psi_cc, map_mul, map_mul, map_inv, psi_Q s r i (by omega), psi_cc]
    group

theorem psi_zero : psi 0 = MonoidHom.id (Fc ℓ) := by
  ext k
  rcases k with k | i
  · fin_cases k
    · exact psi_c0 0
    · change psi 0 (dd : Fc ℓ) = dd; rw [psi_dd, Q_top, Cs_zero]; simp
    · exact psi_ee 0
  · change psi 0 (cc i : Fc ℓ) = cc i; rw [psi_cc]; simp [Q]

theorem psi_neg_psi (x : Fc ℓ) : psi (-1) (psi 1 x) = x := by
  rw [← MonoidHom.comp_apply, psi_comp]; simp [psi_zero]

theorem psi_injective : Function.Injective (psi 1 : Fc ℓ →* Fc ℓ) :=
  Function.LeftInverse.injective psi_neg_psi

theorem psi_map_VZ (s : ℤ) {x : Fc ℓ} (hx : x ∈ VZ ℓ) : psi s x ∈ VZ ℓ := by
  have : VZ ℓ ≤ (VZ ℓ).comap (psi s) := by
    rw [VZ, Subgroup.closure_le]
    rintro _ ⟨r, rfl⟩
    show psi s (vv r : Fc ℓ) ∈ VZ ℓ
    rw [psi_vv]; exact Subgroup.subset_closure ⟨_, rfl⟩
  exact this hx

/-- The identification `⊤ ≃ ψ₁(F_c)`. -/
noncomputable def phiPsi (ℓ : ℕ) : (⊤ : Subgroup (Fc ℓ)) ≃* (psi 1 : Fc ℓ →* Fc ℓ).range :=
  Subgroup.topEquiv.trans (MonoidHom.ofInjective psi_injective)

/-- The ascending HNN extension by `ψ₁`. -/
abbrev EPsi (ℓ : ℕ) : Type :=
  HNNExtension (Fc ℓ) ⊤ (psi 1 : Fc ℓ →* Fc ℓ).range (phiPsi ℓ)

theorem conj_EPsi (x : Fc ℓ) :
    (t * of x * t⁻¹ : EPsi ℓ) = of (psi 1 x) :=
  (equiv_eq_conj (φ := phiPsi ℓ) (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup (Fc ℓ)))).symm

/-- **`V_ℤ` is `HB_R`.** -/
theorem hb_VZ : HB R (VZ ℓ) := by
  obtain ⟨c1, c2⟩ := classCR_isFP_two_Fc (R := R) (ℓ := ℓ)
  have htop : Group.FG (⊤ : Subgroup (Fc ℓ)) := (Group.fg_iff_subgroup_fg ⊤).2 (Group.fg_def.1 fg_Fc)
  obtain ⟨e1, e2⟩ := classCR_isFP_two_hnn c1 c2 (phiPsi ℓ) htop
  let V : Subgroup (EPsi ℓ) := Subgroup.closure {of dd, t}
  have hV : V.FG := by
    classical
    exact Subgroup.isMulFG_iff.mpr ⟨{of dd, t}, by simp [V]⟩
  refine ⟨EPsi ℓ, inferInstance, e1, e2, of, of_injective _, V, hV, ?_⟩
  apply le_antisymm
  · intro x hx
    have hsub : V ≤ Subgroup.closure ((of '' (VZ ℓ : Set (Fc ℓ))) ∪ {t}) := by
      apply Subgroup.closure_mono
      rintro _ (rfl | rfl)
      · exact Or.inl ⟨dd, by rw [← vv_zero]; exact Subgroup.subset_closure ⟨0, rfl⟩, rfl⟩
      · exact Or.inr rfl
    obtain ⟨w, hw, hwx⟩ := mem_of_mem_closure_invariant _ (VZ ℓ)
      (fun a ha => psi_map_VZ 1 ha)
      (fun b hb => by
        have key : psi 1 (((phiPsi ℓ).symm b : (⊤ : Subgroup (Fc ℓ))) : Fc ℓ) = (b : Fc ℓ) :=
          congrArg Subtype.val ((phiPsi ℓ).apply_symm_apply b)
        rw [← psi_neg_psi (((phiPsi ℓ).symm b : (⊤ : Subgroup (Fc ℓ))) : Fc ℓ), key]
        exact psi_map_VZ (-1) hb)
      (of x) (hsub hx) ⟨x, rfl⟩
    rw [of_injective _ hwx] at hw
    exact hw
  · rw [VZ, Subgroup.closure_le]
    rintro _ ⟨r, rfl⟩
    show (of (vv r) : EPsi ℓ) ∈ V
    induction r using Int.induction_on with
    | zero => rw [vv_zero]; exact Subgroup.subset_closure (by simp)
    | succ r ih =>
      rw [← psi_vv, ← conj_EPsi]
      exact V.mul_mem (V.mul_mem (Subgroup.subset_closure (by simp)) ih)
        (V.inv_mem (Subgroup.subset_closure (by simp)))
    | pred r ih =>
      have h := conj_EPsi (ℓ := ℓ) (vv (-(r : ℤ) - 1))
      rw [psi_vv, show -(r : ℤ) - 1 + 1 = -r by ring] at h
      have : (of (vv (-(r : ℤ) - 1)) : EPsi ℓ) = t⁻¹ * of (vv (-(r : ℤ))) * t := by
        rw [← h]; group
      rw [this]
      exact V.mul_mem (V.mul_mem (V.inv_mem (Subgroup.subset_closure (by simp))) ih)
        (Subgroup.subset_closure (by simp))

/-! ### `HB_R(V_S)` -/

section VS

variable {J : Type} [Group J] (j : Fin ℓ → J) {S : Set ℤ}

/-- The identification of the untwisted and twisted copies of `F_c`. -/
noncomputable def phiTw : (kappa (yU (ℓ := ℓ) (J := J))).range ≃* (kappa (yT j)).range :=
  (MonoidHom.ofInjective kappa_yU_injective).symm.trans (MonoidHom.ofInjective (kappa_yT_injective j))

/-- `M(S)`: the HNN extension of `A₃ ∗ (F(ℓ) × J)` with `t ι(h) t⁻¹ = τ(h)`. -/
abbrev MTw : Type :=
  HNNExtension (KF (FreeGroup (Fin ℓ) × J)) (kappa yU).range (kappa (yT j)).range (phiTw j)

theorem phiTw_apply (x : Fc ℓ) :
    ((phiTw j ⟨kappa yU x, x, rfl⟩ : (kappa (yT j)).range) : KF (FreeGroup (Fin ℓ) × J)) =
      kappa (yT j) x := by
  have h : (MonoidHom.ofInjective (kappa_yU_injective (ℓ := ℓ) (J := J))).symm
      ⟨kappa yU x, x, rfl⟩ = x := by
    rw [MulEquiv.symm_apply_eq]; rfl
  simp only [phiTw, MulEquiv.trans_apply, h]
  rfl

theorem conj_MTw (x : Fc ℓ) :
    (t * of (kappa yU x) * t⁻¹ : MTw j) = of (kappa (yT j) x) := by
  have := equiv_eq_conj (φ := phiTw j)
    (⟨kappa yU x, x, rfl⟩ : (kappa (yU (ℓ := ℓ) (J := J))).range)
  rw [← this, phiTw_apply]

theorem classCR_isFP_two_KF (h1 : ClassCR R J) (h2 : IsFP 2 J) :
    ClassCR R (KF (FreeGroup (Fin ℓ) × J)) ∧ IsFP 2 (KF (FreeGroup (Fin ℓ) × J)) := by
  obtain ⟨a1, a2⟩ := classCR_isFP_two_freeGroup (R := R) 3
  obtain ⟨b1, b2⟩ := classCR_isFP_two_freeGroup (R := R) ℓ
  obtain ⟨p1, p2⟩ := classCR_isFP_two_prod b1 b2 h1 h2
  exact classCR_isFP_two_coprodI a1 a2 p1 p2

theorem classCR_isFP_two_MTw (h1 : ClassCR R J) (h2 : IsFP 2 J) :
    ClassCR R (MTw j) ∧ IsFP 2 (MTw j) := by
  obtain ⟨k1, k2⟩ := classCR_isFP_two_KF (ℓ := ℓ) h1 h2
  have hfg : Group.FG (kappa (yU (ℓ := ℓ) (J := J))).range := by
    rw [Group.fg_iff_subgroup_fg, MonoidHom.range_eq_map]
    exact Subgroup.fg_map' _ (Group.fg_def.1 fg_Fc)
  exact classCR_isFP_two_hnn k1 k2 (phiTw j) hfg

/-- **`V_S` is `HB_R`** (the relative form of [Leary 2018, Lemma 2.4]). -/
theorem hb_VS (hℓ : 1 ≤ ℓ) (h1 : ClassCR R J) (h2 : IsFP 2 J) (hD : ∀ s, Ys j s = 1 ↔ s ∈ S)
    (h0 : (0 : ℤ) ∈ S) : HB R (VS ℓ S) := by
  obtain ⟨m1, m2⟩ := classCR_isFP_two_MTw j h1 h2
  let ι' : Fc ℓ →* MTw j := (of : _ →* MTw j).comp (kappa yU)
  have hι' : Function.Injective ι' := (of_injective _).comp kappa_yU_injective
  have hM : EmbedsSuitable R (MTw j) := ⟨MTw j, inferInstance, m1, m2, MonoidHom.id _,
    Function.injective_id⟩
  have hA := HB.transfer fg_Fc (hb_VZ (R := R) (ℓ := ℓ)) ι' hι' hM
  have hB := hA.map_equiv (MulAut.conj (t : MTw j))
  have hC : HB R ι'.range := HB.of_fg hM (by
    rw [MonoidHom.range_eq_map ι']; exact Subgroup.fg_map' _ (Group.fg_def.1 fg_Fc))
  have hE := (hB.inf hC).comap ι' hι'
  convert hE using 1
  ext y
  simp only [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · intro hy
    refine ⟨⟨ι' y, ⟨y, VS_le_VZ S hy, rfl⟩, ?_⟩, y, rfl⟩
    show t * ι' y * t⁻¹ = ι' y
    simp only [ι', MonoidHom.comp_apply]
    rw [conj_MTw, kappa_eq_of_mem_VS j hD hy]
  · rintro ⟨⟨_, ⟨x, hx, rfl⟩, hxy⟩, -⟩
    change t * ι' x * t⁻¹ = ι' y at hxy
    simp only [ι', MonoidHom.comp_apply] at hxy
    rw [conj_MTw] at hxy
    have h3 := of_injective _ hxy
    have hxy' : x = y := by
      have := congrArg retr h3
      rwa [retr_apply_kappa _ (fun i => rfl), retr_apply_kappa _ (fun i => rfl)] at this
    subst hxy'
    exact mem_VS_of_kappa_eq hℓ j hD h0 hx h3

end VS

end TheoremA.Coding
