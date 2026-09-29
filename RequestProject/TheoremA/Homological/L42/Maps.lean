module

public import RequestProject.TheoremA.Homological.L42.Delta

/-!
# Lemma 4.2, part 7: the chain lifts `f = h i₁`, `g = h i₂`, `hΔ` and `τ_a = ρ_a Δ`
-/

@[expose] public section

namespace TheoremA

open TensorProduct

universe u

variable {B : Type u} [Group B] {k : ℕ}

namespace L42

variable {R : Res B k}

section tot

variable (α β : B →* B)

/-- The total map `h_n : Q_n → F_n` (summed over a box `p, q < L`). -/
noncomputable def hTot (L : ℕ) {n : ℕ} (Y : Lvl R n) (z : Qm R) : F R n :=
  ∑ p ∈ Finset.range L, ∑ q ∈ Finset.range L, Hm R α β Y p q (z p q)

theorem hTot_sub (L : ℕ) {n : ℕ} (Y : Lvl R n) (z w : Qm R) :
    hTot α β L Y (z - w) = hTot α β L Y z - hTot α β L Y w := by
  simp only [hTot, Pi.sub_apply, map_sub, Finset.sum_sub_distrib]

theorem hTot_act (hαβ : ∀ b c, Commute (α b) (β c)) (L : ℕ) {n : ℕ} (Y : Lvl R n) (b c : B)
    (z : Qm R) :
    hTot α β L Y (actQ R b c z) = MonoidAlgebra.of ℤ B (α b * β c) • hTot α β L Y z := by
  simp only [hTot, actQ_apply, Hm_act R hαβ, Finset.smul_sum]

/-- Reindexing: `h_n ∘ D` is the sum of the boundary values `bd`. -/
theorem hTot_D (L : ℕ) {n : ℕ} (Y : Lvl R n) (hY : OffZero R Y) (hn : n + 1 ≤ L) (z : Qm R) :
    hTot α β (L + 1) Y (D R z) =
      ∑ p ∈ Finset.range (L + 1), ∑ q ∈ Finset.range (L + 1), bd R α β Y p q (z p q) := by
  simp only [hTot, D_apply, map_add, map_zsmul, bd, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm, Finset.sum_comm (f := fun p q => bdL R α β Y p q (z p q))]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_range_succ, Finset.sum_range_succ', bdL_zero, add_zero,
      Hm_off R α β hY (by omega), add_zero]
    rfl
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_range_succ, Finset.sum_range_succ', bdR_zero, smul_zero, add_zero,
      Hm_off R α β hY (by omega), smul_zero, add_zero]
    rfl

/-- A box sum with only two nonzero terms. -/
theorem hTot_two (L : ℕ) {n : ℕ} (Y : Lvl R n) (z : Qm R) (m : ℕ) (hm : 1 ≤ m) (hmL : m < L)
    (hz : ∀ p q, ¬ (p = m ∧ q = 0) → ¬ (p = 0 ∧ q = m) → z p q = 0) :
    hTot α β L Y z = Hm R α β Y m 0 (z m 0) + Hm R α β Y 0 m (z 0 m) := by
  rw [hTot, ← Finset.sum_product']
  rw [Finset.sum_eq_add_of_mem (m, 0) (0, m) (by simp; omega) (by simp; omega)
    (by simp; omega)]
  rintro ⟨p, q⟩ _ ⟨h1, h2⟩
  rw [hz p q (fun h => h1 (by rw [h.1, h.2])) (fun h => h2 (by rw [h.1, h.2])), map_zero]

theorem hTot_single (L : ℕ) (hL : 0 < L) (Y : Lvl R 0) (hY : OffZero R Y) (z : Qm R) :
    hTot α β L Y z = Hm R α β Y 0 0 (z 0 0) := by
  rw [hTot, ← Finset.sum_product']
  rw [Finset.sum_eq_single (0, 0)]
  · rintro ⟨p, q⟩ _ h
    rw [Hm_off R α β hY (fun h' => h (by simp only [Prod.mk.injEq]; omega))]
  · intro h; exact absurd (by simp; omega) h

end tot

section contr

variable (R)

/-- `x ⊗ y ↦ ε(y) x : F_p ⊗ F_0 → F_p`. -/
noncomputable def contrR (p : ℕ) : T R p 0 →ₗ[ℤ] F R p :=
  (TensorProduct.rid ℤ (F R p)) ∘ₗ map LinearMap.id (εZ R)

/-- `x ⊗ y ↦ ε(x) y : F_0 ⊗ F_q → F_q`. -/
noncomputable def contrL (q : ℕ) : T R 0 q →ₗ[ℤ] F R q :=
  (TensorProduct.lid ℤ (F R q)) ∘ₗ map (εZ R) LinearMap.id

@[simp] theorem contrR_tmul (p : ℕ) (x : F R p) (y : F R 0) :
    contrR R p (x ⊗ₜ y) = R.ε y • x := rfl

@[simp] theorem contrL_tmul (q : ℕ) (x : F R 0) (y : F R q) :
    contrL R q (x ⊗ₜ y) = R.ε x • y := rfl

theorem contrR_act (p : ℕ) (b c : B) (t : T R p 0) :
    contrR R p (act R p 0 b c t) = MonoidAlgebra.of ℤ B b • contrR R p t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul x y => simp only [act, map_tmul, gsm_apply, contrR_tmul, R.ε_inv, smul_comm _ (R.ε y)]

theorem contrL_act (q : ℕ) (b c : B) (t : T R 0 q) :
    contrL R q (act R 0 q b c t) = MonoidAlgebra.of ℤ B c • contrL R q t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul x y => simp only [act, map_tmul, gsm_apply, contrL_tmul, R.ε_inv, smul_comm _ (R.ε x)]

theorem contrR_dL (p : ℕ) (t : T R (p + 1) 0) :
    contrR R p (dL R p 0 t) = R.d p (contrR R (p + 1) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp [-zsmul_eq_mul, map_zsmul]

theorem contrR_dR (p : ℕ) (t : T R p 1) : contrR R p (dR R p 0 t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul x y =>
    simp only [map_tmul, LinearMap.id_apply, contrR_tmul]
    rw [show R.ε (dZ R 0 y) = 0 from R.ε_d y, zero_smul]

theorem contrL_dR (q : ℕ) (t : T R 0 (q + 1)) :
    contrL R q (dR R 0 q t) = R.d q (contrL R (q + 1) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp [-zsmul_eq_mul, map_zsmul]

theorem contrL_dL (q : ℕ) (t : T R 1 q) : contrL R q (dL R 0 q t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul x y =>
    simp only [map_tmul, LinearMap.id_apply, contrL_tmul]
    rw [show R.ε (dZ R 0 x) = 0 from R.ε_d x, zero_smul]

theorem ε_contrR (t : T R 0 0) : R.ε (contrR R 0 t) = εε R t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp [-zsmul_eq_mul, map_zsmul, mul_comm]

theorem ε_contrL (t : T R 0 0) : R.ε (contrL R 0 t) = εε R t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp [-zsmul_eq_mul, map_zsmul]

variable {R} (C : Contr R)

theorem contrR_tmul_x0 (p : ℕ) (t : T R p 0) :
    contrR R p t ⊗ₜ C.x0 = map LinearMap.id (ιε C) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
  | tmul x y => simp only [contrR_tmul, map_tmul, LinearMap.id_apply, ιε_apply, smul_tmul]

theorem x0_tmul_contrL (q : ℕ) (t : T R 0 q) :
    C.x0 ⊗ₜ contrL R q t = map (ιε C) LinearMap.id t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, tmul_add, hx, hy]
  | tmul x y => simp only [contrL_tmul, map_tmul, LinearMap.id_apply, ιε_apply, tmul_smul,
      smul_tmul']

end contr

end L42

end TheoremA
