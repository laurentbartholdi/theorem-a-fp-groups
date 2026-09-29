module

public import RequestProject.TheoremA.Homological.L42.Maps

/-!
# Lemma 4.2, part 8: the chain lifts `f`, `g`, `hΔ`, `τ₁`, `τ₂`
-/

@[expose] public section

namespace TheoremA

open TensorProduct

universe u

variable {B : Type u} [Group B] {k : ℕ}

namespace L42

variable {R : Res B k} (C : Contr R) (α β : B →* B)

/-- `f = h ∘ i₁`, `i₁ x = x ⊗ x₀`. -/
noncomputable def fL (i : ℕ) : F R i →+ F R i :=
  (Hm R α β (YY C α β i) i 0).comp ((TensorProduct.mk ℤ (F R i) (F R 0)).flip C.x0).toAddMonoidHom

/-- `g = h ∘ i₂`, `i₂ y = x₀ ⊗ y`. -/
noncomputable def gL (i : ℕ) : F R i →+ F R i :=
  (Hm R α β (YY C α β i) 0 i).comp ((TensorProduct.mk ℤ (F R 0) (F R i)) C.x0).toAddMonoidHom

@[simp] theorem fL_apply (i : ℕ) (x : F R i) : fL C α β i x = Hm R α β (YY C α β i) i 0 (x ⊗ₜ C.x0) :=
  rfl

@[simp] theorem gL_apply (i : ℕ) (x : F R i) : gL C α β i x = Hm R α β (YY C α β i) 0 i (C.x0 ⊗ₜ x) :=
  rfl

/-- `h ∘ Δ`. -/
noncomputable def hΔ (i : ℕ) : F R i →+ F R i :=
  AddMonoidHom.mk' (fun x => hTot α β (k + 3) (YY C α β i) (Δ C i x)) (fun x y => by
    simp only [hTot, map_add, Pi.add_apply, Finset.sum_add_distrib])

@[simp] theorem hΔ_apply (i : ℕ) (x : F R i) :
    hΔ C α β i x = hTot α β (k + 3) (YY C α β i) (Δ C i x) := rfl

/-- `τ₁ = ρ₁ ∘ Δ`. -/
noncomputable def τ1 (i : ℕ) : F R i →+ F R i :=
  AddMonoidHom.mk' (fun x => contrR R i (Δ C i x i 0)) (fun x y => by simp)

/-- `τ₂ = ρ₂ ∘ Δ`. -/
noncomputable def τ2 (i : ℕ) : F R i →+ F R i :=
  AddMonoidHom.mk' (fun x => contrL R i (Δ C i x 0 i)) (fun x y => by simp)

@[simp] theorem τ1_apply (i : ℕ) (x : F R i) : τ1 C i x = contrR R i (Δ C i x i 0) := rfl
@[simp] theorem τ2_apply (i : ℕ) (x : F R i) : τ2 C i x = contrL R i (Δ C i x 0 i) := rfl

theorem idLift_isChainLift (R : Res B k) :
    IsChainLift R (MonoidHom.id B) (fun i => AddMonoidHom.id (F R i)) where
  semilinear i l x := by simp
  comm i _ x := rfl
  aug x := rfl

variable (hαβ : ∀ b c, Commute (α b) (β c))
include hαβ

theorem fL_isChainLift : IsChainLift R α (fL C α β) where
  semilinear i := semilinear_of_group α _ fun g x => by
    have e : (MonoidAlgebra.of ℤ B g • x) ⊗ₜ C.x0 = act R i 0 g 1 (x ⊗ₜ C.x0) := by
      rw [act, map_tmul, gsm_apply, gsm_apply, map_one, one_smul]
    rw [fL_apply, e, Hm_act R hαβ, map_one, mul_one]; rfl
  comm i hi x := by
    rw [fL_apply, fL_apply, YY_chain C α β hαβ i hi, bd, bdL_succ, bdR_zero, smul_zero, add_zero]
    rfl
  aug x := by
    rw [fL_apply, ε_hExt_eq α β hαβ (YY_aug C α β), εε_tmul, C.hx0, mul_one]

theorem gL_isChainLift : IsChainLift R β (gL C α β) where
  semilinear i := semilinear_of_group β _ fun g x => by
    have e : C.x0 ⊗ₜ (MonoidAlgebra.of ℤ B g • x) = act R 0 i 1 g (C.x0 ⊗ₜ x) := by
      rw [act, map_tmul, gsm_apply, gsm_apply, map_one, one_smul]
    rw [gL_apply, e, Hm_act R hαβ, map_one, one_mul]; rfl
  comm i hi x := by
    rw [gL_apply, gL_apply, YY_chain C α β hαβ i hi, bd, bdL_zero, bdR_succ, pow_zero, one_smul,
      zero_add]
    rfl
  aug x := by
    rw [gL_apply, ε_hExt_eq α β hαβ (YY_aug C α β), εε_tmul, C.hx0, one_mul]

theorem hΔ_isChainLift (δ : B →* B) (hδ : ∀ b, δ b = α b * β b) :
    IsChainLift R δ (hΔ C α β) where
  semilinear i := semilinear_of_group δ _ fun g x => by
    rw [hΔ_apply, hΔ_apply, Δ_of, hTot_act α β hαβ, hδ]
  comm i hi x := by
    rw [hΔ_apply, hΔ_apply, ← Δ_chain C i hi, hTot_D α β (k + 2) _ (YY_off C α β i) (by omega),
      hTot, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [YY_chain C α β hαβ i hi]
  aug x := by
    rw [hΔ_apply, hTot_single α β _ (by omega) _ (YY_off C α β 0), ε_hExt_eq α β hαβ (YY_aug C α β),
      Δ_aug]

omit hαβ in
theorem τ1_isChainLift : IsChainLift R (MonoidHom.id B) (τ1 C) where
  semilinear i := semilinear_of_group _ _ fun g x => by
    rw [τ1_apply, τ1_apply, Δ_of, actQ_apply, contrR_act]; rfl
  comm i hi x := by
    rw [τ1_apply, τ1_apply, ← Δ_chain C i hi, D_apply, map_add, map_zsmul, contrR_dL, contrR_dR,
      smul_zero, add_zero]
  aug x := by
    rw [τ1_apply, ε_contrR, Δ_aug]

omit hαβ in
theorem τ2_isChainLift : IsChainLift R (MonoidHom.id B) (τ2 C) where
  semilinear i := semilinear_of_group _ _ fun g x => by
    rw [τ2_apply, τ2_apply, Δ_of, actQ_apply, contrL_act]; rfl
  comm i hi x := by
    rw [τ2_apply, τ2_apply, ← Δ_chain C i hi, D_apply, map_add, map_zsmul, contrL_dR, contrL_dL,
      zero_add, pow_zero, one_smul]
  aug x := by
    rw [τ2_apply, ε_contrL, Δ_aug]

end L42

end TheoremA
