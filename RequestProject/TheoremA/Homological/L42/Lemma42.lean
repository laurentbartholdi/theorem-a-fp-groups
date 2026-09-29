module

public import RequestProject.TheoremA.Homological.L42.ChainLifts
public import RequestProject.TheoremA.Homological.Cor43

/-!
# Lemma 4.2 (commuting products)

We assemble the pieces: `N_prod = Λ h_m d_{m+1}(Q_{m+1})` (4.7) is finitely generated and lies in
`S`; the Künneth decomposition (4.9) is obtained from the contracting homotopy; and Lemma 4.1 is
applied to the pairs `(τ_a, id)`, `(hΔ, Φ_δ)`, `(f, Φ_α)`, `(g, Φ_β)`.
-/

@[expose] public section

namespace TheoremA

open TensorProduct

universe u

variable {B : Type u} [Group B] {k : ℕ}

/-- A semilinear chain lift maps a finitely generated submodule of `S` into a finitely generated
submodule of `S`. -/
theorem image_fg {R : Res B k} {θ : B →* B} {φ : ∀ i, FreeMod B (R.c i) →+ FreeMod B (R.c i)}
    (hφ : IsChainLift R θ φ) (N : Submodule (ZG B) (FreeMod B (R.c (k + 1)))) (hN : N.FG)
    (hNS : N ≤ R.S) : ∃ N' : Submodule (ZG B) (FreeMod B (R.c (k + 1))), N'.FG ∧ N' ≤ R.S ∧
      ∀ c ∈ N, φ (k + 1) c ∈ N' := by
  obtain ⟨s, rfl⟩ := hN
  refine ⟨Submodule.span (ZG B) (φ (k + 1) '' s), Submodule.fg_span (s.finite_toSet.image _), ?_,
    fun c hc => ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hxS : R.d k x = 0 := hNS (Submodule.subset_span hx)
    show R.d k (φ (k + 1) x) = 0
    rw [← hφ.comm k le_rfl, hxS, map_zero]
  · induction hc using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul l x _ hx => rw [hφ.semilinear]; exact Submodule.smul_mem _ _ hx

namespace L42

variable {R : Res B k} (C : Contr R) (α β : B →* B)

/-- Generators of `N_prod`: boundary values of basis tensors in `F_P ⊗ F_Q`, `P, Q ≥ 1`,
`P + Q = m + 1`. -/
def NGen : Set (F R (k + 1)) :=
  {x | ∃ P Q, 1 ≤ P ∧ 1 ≤ Q ∧ P + Q = k + 2 ∧ ∃ (a : Fin (R.c P)) (b : Fin (R.c Q)),
    x = bd R α β (YY C α β (k + 1)) P Q (Pi.single a 1 ⊗ₜ Pi.single b 1)}

/-- `N_prod` (4.7). -/
noncomputable def Nprod : Submodule (ZG B) (F R (k + 1)) :=
  Submodule.span (ZG B) (NGen C α β)

theorem Nprod_fg : (Nprod C α β).FG := by
  let G : ℕ → ℕ → Set (F R (k + 1)) := fun P Q =>
    Set.range (fun ab : Fin (R.c P) × Fin (R.c Q) =>
      bd R α β (YY C α β (k + 1)) P Q (Pi.single ab.1 1 ⊗ₜ Pi.single ab.2 1))
  have hG : ∀ P Q, (G P Q).Finite := fun P Q => Set.finite_range _
  have hfin : (⋃ P ∈ (↑(Finset.range (k + 3)) : Set ℕ),
      ⋃ Q ∈ (↑(Finset.range (k + 3)) : Set ℕ), G P Q).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun P _ =>
      Set.Finite.biUnion (Finset.finite_toSet _) fun Q _ => hG P Q
  refine Submodule.fg_span (hfin.subset ?_)
  rintro x ⟨P, Q, hP, hQ, hPQ, a, b, rfl⟩
  simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_range]
  exact ⟨P, by omega, Q, by omega, (a, b), rfl⟩

variable (hαβ : ∀ b c, Commute (α b) (β c))
include hαβ

theorem Nprod_le_S : Nprod C α β ≤ R.S := by
  rw [Nprod, Submodule.span_le]
  rintro _ ⟨P, Q, hP, hQ, hPQ, a, b, rfl⟩
  exact d_bd R α β _ _ (YY_chain C α β hαβ k le_rfl) P Q (by omega) (by omega) _

theorem bd_mem_Nprod (P Q : ℕ) (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hPQ : P + Q = k + 2) (t : T R P Q) :
    bd R α β (YY C α β (k + 1)) P Q t ∈ Nprod C α β := by
  let N := Nprod C α β
  let ψ : T R P Q →+ F R (k + 1) :=
    { toFun := bd R α β (YY C α β (k + 1)) P Q
      map_zero' := by simp [bd]
      map_add' := bd_add R α β _ P Q }
  have := tensor_hom_ext R
    (fun b c => DistribSMul.toAddMonoidHom (F R (k + 1) ⧸ N) (MonoidAlgebra.of ℤ B (α b * β c)))
    (φ := N.mkQ.toAddMonoidHom.comp ψ) (ψ := 0)
    (fun b c t => by
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, ψ, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, bd_act R hαβ, map_smul, DistribSMul.toAddMonoidHom_apply])
    (fun b c t => by simp)
    (fun a b => by
      simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, ψ, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, AddMonoidHom.zero_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨P, Q, hP, hQ, hPQ, a, b, rfl⟩)
  have h := congrArg (fun f => f t) this
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, ψ, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, AddMonoidHom.zero_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at h
  exact h

omit hαβ in
theorem bd_zero_arg {n : ℕ} (Y : Lvl R n) (p q : ℕ) : bd R α β Y p q 0 = 0 := by simp [bd]

/-- The Künneth step (4.9)–(4.10): `(hΔ - f τ₁ - g τ₂)(S) ⊆ N_prod`. -/
theorem kunneth (hk : 1 ≤ k) (s : F R (k + 1)) (hs : R.d k s = 0) :
    hΔ C α β (k + 1) s - fL C α β (k + 1) (τ1 C (k + 1) s) - gL C α β (k + 1) (τ2 C (k + 1) s)
      ∈ Nprod C α β := by
  set y := Δ C (k + 1) s with hydef
  have hy : D R y = 0 := by rw [hydef, Δ_chain C k le_rfl, hs, map_zero]
  have hydeg : IsDeg (k + 1) y := Δ_deg C (k + 1) s
  set w := Sig C y with hwdef
  have hSD : Sig C (D R y) = 0 := by rw [hy, map_zero]
  -- `D w = y` away from the two corners
  have hDw : ∀ p q, ¬ (p = k + 1 ∧ q = 0) → ¬ (p = 0 ∧ q = k + 1) → (y - D R w) p q = 0 := by
    intro p q h1 h2
    rw [Pi.sub_apply, Pi.sub_apply, sub_eq_zero]
    by_cases hpq : p + q = k + 1
    · rcases p with _ | p
      · obtain ⟨i, rfl⟩ : ∃ i, q = i + 1 := ⟨q - 1, by omega⟩
        have := homotopy_zero_succ C y i (by omega)
        rw [hSD, Pi.zero_apply, Pi.zero_apply, add_zero] at this
        exact this.symm
      · have := homotopy_succ C y p q (by omega)
        rw [hSD, Pi.zero_apply, Pi.zero_apply, add_zero] at this
        exact this.symm
    · rw [hydeg p q hpq, ((hydeg.Sig C).D) p q hpq]
  -- the corner `(m, 0)`
  set u := y (k + 1) 0
  let π : F R (k + 1) →ₗ[ℤ] F R (k + 1) := LinearMap.id - C.σ k ∘ₗ dZ R k
  have hπ : dZ R k ∘ₗ π = 0 := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    refine LinearMap.ext fun x => ?_
    have h1 := C.ci k' (by omega) (dZ R (k' + 1) x)
    have h2 : dZ R k' (dZ R (k' + 1) x) = 0 := R.d_d k' (by omega) x
    rw [h2, map_zero, add_zero] at h1
    simp only [π, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub, h1,
      sub_self, LinearMap.zero_apply]
  have hcornerL : (y - D R w) (k + 1) 0 =
      map LinearMap.id (ιε C) u + dR R (k + 1) 0 (map π (C.σ 0) u) := by
    have hw : D R w (k + 1) 0 = map (C.σ k ∘ₗ dZ R k) LinearMap.id u := by
      have := homotopy_top C y 0
      rwa [hSD, Pi.zero_apply, Pi.zero_apply, add_zero] at this
    have hdL : dL R k 0 u = -(((-1 : ℤ) ^ k) • dR R k 0 (y k 1)) := by
      have := congrFun (congrFun hy k) 0
      rw [D_apply, Pi.zero_apply, Pi.zero_apply] at this
      exact eq_neg_of_add_eq_zero_left this
    have e1 : dR R (k + 1) 0 (map π (C.σ 0) u) = map π (dZ R 0 ∘ₗ C.σ 0) u := by
      rw [map_map, LinearMap.id_comp]
    have e2 := map_id_add π (dZ R 0 ∘ₗ C.σ 0) (ιε C) u
    rw [c0' C] at e2
    have e3 := map_add_id π (C.σ k ∘ₗ dZ R k) LinearMap.id u
    rw [show π + C.σ k ∘ₗ dZ R k = LinearMap.id from sub_add_cancel _ _, map_id,
      LinearMap.id_apply] at e3
    have e4 := map_add_id π (C.σ k ∘ₗ dZ R k) (ιε C) u
    rw [show π + C.σ k ∘ₗ dZ R k = LinearMap.id from sub_add_cancel _ _] at e4
    have e5 : map (C.σ k ∘ₗ dZ R k) (ιε C) u = 0 := by
      have : map (C.σ k ∘ₗ dZ R k) (ιε C) u = map (C.σ k) (ιε C) (dL R k 0 u) := by
        rw [map_map, LinearMap.comp_id]
      rw [this, hdL, map_neg, map_zsmul, map_map, LinearMap.comp_id, ιε_dZ, map_zero_right,
        LinearMap.zero_apply, smul_zero, neg_zero]
    show u - D R w (k + 1) 0 = _
    rw [hw, e1, eq_sub_of_add_eq e2, eq_sub_of_add_eq e4, e5, eq_sub_of_add_eq e3]
    abel
  -- the corner `(0, m)`
  set v := y 0 (k + 1)
  have hcornerR : (y - D R w) 0 (k + 1) = map (ιε C) LinearMap.id v := by
    have hw : D R w 0 (k + 1) = map (dZ R 0 ∘ₗ C.σ 0) LinearMap.id v +
        map (ιε C) (C.σ k ∘ₗ dZ R k) v := by
      have := homotopy_zero_top C y
      rwa [hSD, Pi.zero_apply, Pi.zero_apply, add_zero] at this
    have hdR : dR R 0 k v = -dL R 0 k (y 1 k) := by
      have := congrFun (congrFun hy 0) k
      rw [D_apply, Pi.zero_apply, Pi.zero_apply, pow_zero, one_smul] at this
      exact eq_neg_of_add_eq_zero_right this
    have f5 : map (ιε C) (C.σ k ∘ₗ dZ R k) v = 0 := by
      have : map (ιε C) (C.σ k ∘ₗ dZ R k) v = map (ιε C) (C.σ k) (dR R 0 k v) := by
        rw [map_map, LinearMap.comp_id]
      rw [this, hdR, map_neg, map_map, LinearMap.comp_id, ιε_dZ, map_zero_left, LinearMap.zero_apply,
        neg_zero]
    have f6 := map_add_id (dZ R 0 ∘ₗ C.σ 0) (ιε C) LinearMap.id v
    rw [c0' C, map_id, LinearMap.id_apply] at f6
    show v - D R w 0 (k + 1) = _
    rw [hw, f5, add_zero, sub_eq_iff_eq_add]
    exact f6.symm.trans (add_comm _ _)
  -- assemble
  have htot : hΔ C α β (k + 1) s = hTot α β (k + 3) (YY C α β (k + 1)) (D R w) +
      (Hm R α β (YY C α β (k + 1)) (k + 1) 0 ((y - D R w) (k + 1) 0) +
        Hm R α β (YY C α β (k + 1)) 0 (k + 1) ((y - D R w) 0 (k + 1))) := by
    rw [← hTot_two α β (k + 3) _ (y - D R w) (k + 1) (by omega) (by omega) hDw, hTot_sub,
      hΔ_apply, ← hydef]
    abel
  have hf : fL C α β (k + 1) (τ1 C (k + 1) s) =
      Hm R α β (YY C α β (k + 1)) (k + 1) 0 (map LinearMap.id (ιε C) u) := by
    rw [fL_apply, τ1_apply, contrR_tmul_x0]
  have hg : gL C α β (k + 1) (τ2 C (k + 1) s) =
      Hm R α β (YY C α β (k + 1)) 0 (k + 1) (map (ιε C) LinearMap.id v) := by
    rw [gL_apply, τ2_apply, x0_tmul_contrL]
  have hcorr : Hm R α β (YY C α β (k + 1)) (k + 1) 0 (dR R (k + 1) 0 (map π (C.σ 0) u)) =
      ((-1 : ℤ) ^ (k + 1)) • bd R α β (YY C α β (k + 1)) (k + 1) 1 (map π (C.σ 0) u) := by
    have hdL0 : dL R k 1 (map π (C.σ 0) u) = 0 := by
      rw [map_map, hπ, map_zero_left, LinearMap.zero_apply]
    have hbd : bd R α β (YY C α β (k + 1)) (k + 1) 1 (map π (C.σ 0) u) =
        Hm R α β (YY C α β (k + 1)) k 1 (dL R k 1 (map π (C.σ 0) u)) +
          ((-1 : ℤ) ^ (k + 1)) • Hm R α β (YY C α β (k + 1)) (k + 1) 0
            (dR R (k + 1) 0 (map π (C.σ 0) u)) := rfl
    rw [hbd, hdL0, map_zero]
    generalize Hm R α β (YY C α β (k + 1)) (k + 1) 0 (dR R (k + 1) 0 (map π (C.σ 0) u)) = X
    rw [zero_add, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  rw [htot, hcornerL, hcornerR, map_add, hf, hg, hcorr]
  have hmem1 : hTot α β (k + 3) (YY C α β (k + 1)) (D R w) ∈ Nprod C α β := by
    rw [hTot_D α β (k + 2) _ (YY_off C α β (k + 1)) (by omega)]
    refine Submodule.sum_mem _ fun P _ => Submodule.sum_mem _ fun Q _ => ?_
    by_cases hPQ : P + Q = k + 1 + 1
    · rcases P with _ | P
      · rw [show Q = k + 2 by omega, hwdef, Sig_zero_succ, C.σ_top (k + 1) (by omega),
          map_zero_right, LinearMap.zero_apply, bd_zero_arg]
        exact Submodule.zero_mem _
      · rcases Q with _ | Q
        · rw [show P = k + 1 by omega, hwdef, Sig_succ, C.σ_top (k + 1) (by omega),
            map_zero_left, LinearMap.zero_apply, bd_zero_arg]
          exact Submodule.zero_mem _
        · exact bd_mem_Nprod C α β hαβ _ _ (by omega) (by omega) (by omega) _
    · rw [bd_off R α β (YY_off C α β (k + 1)) hPQ]
      exact Submodule.zero_mem _
  have hmem2 : ((-1 : ℤ) ^ (k + 1)) • bd R α β (YY C α β (k + 1)) (k + 1) 1 (map π (C.σ 0) u) ∈
      Nprod C α β :=
    Submodule.smul_of_tower_mem _ _ (bd_mem_Nprod C α β hαβ _ _ (by omega) le_rfl (by omega) _)
  convert Submodule.add_mem _ hmem1 hmem2 using 1
  abel

end L42

/-- **Lemma 4.2 (commuting products).** -/
theorem lemma42 : Lemma42.{u} := by
  intro k hk B _ R α β δ hαβ hδ Φα Φβ Φδ hα hβ hδl
  obtain ⟨C⟩ := L42.exists_contr R
  have hf := L42.fL_isChainLift C α β hαβ
  have hg := L42.gL_isChainLift C α β hαβ
  have hh := L42.hΔ_isChainLift C α β hαβ δ hδ
  obtain ⟨N3, h3fg, h3S, h3⟩ := comparison R δ _ Φδ hh hδl
  obtain ⟨N4, h4fg, h4S, h4⟩ := comparison R α _ Φα hf hα
  obtain ⟨N5, h5fg, h5S, h5⟩ := comparison R β _ Φβ hg hβ
  obtain ⟨C1, h1fg, h1S, h1⟩ := comparison R _ _ _ (L42.τ1_isChainLift C)
    (L42.idLift_isChainLift R)
  obtain ⟨C2, h2fg, h2S, h2⟩ := comparison R _ _ _ (L42.τ2_isChainLift C)
    (L42.idLift_isChainLift R)
  obtain ⟨Nf, hffg, hfS, hfN⟩ := image_fg hf C1 h1fg h1S
  obtain ⟨Ng, hgfg, hgS, hgN⟩ := image_fg hg C2 h2fg h2S
  refine ⟨N3 ⊔ L42.Nprod C α β ⊔ Nf ⊔ N4 ⊔ Ng ⊔ N5,
    ((((h3fg.sup (L42.Nprod_fg C α β)).sup hffg).sup h4fg).sup hgfg).sup h5fg,
    sup_le (sup_le (sup_le (sup_le (sup_le h3S (L42.Nprod_le_S C α β hαβ)) hfS) h4S) hgS) h5S,
    fun s hs => ?_⟩
  have hs' : R.d k s = 0 := hs
  have e : Φδ (k + 1) s - Φα (k + 1) s - Φβ (k + 1) s =
      -(L42.hΔ C α β (k + 1) s - Φδ (k + 1) s) +
      (L42.hΔ C α β (k + 1) s - L42.fL C α β (k + 1) (L42.τ1 C (k + 1) s) -
        L42.gL C α β (k + 1) (L42.τ2 C (k + 1) s)) +
      L42.fL C α β (k + 1) (L42.τ1 C (k + 1) s - s) +
      (L42.fL C α β (k + 1) s - Φα (k + 1) s) +
      L42.gL C α β (k + 1) (L42.τ2 C (k + 1) s - s) +
      (L42.gL C α β (k + 1) s - Φβ (k + 1) s) := by
    rw [map_sub, map_sub]; abel
  rw [e]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ ?_ ?_) ?_) ?_) ?_) ?_
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.neg_mem _ (h3 s hs))))))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_left (Submodule.mem_sup_right (L42.kunneth C α β hαβ hk s hs')))))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_right (hfN _ (h1 s hs)))))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (h4 s hs)))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right (hgN _ (h2 s hs)))
  · exact Submodule.mem_sup_right (h5 s hs)

end TheoremA
