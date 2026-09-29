module

public import RequestProject.TheoremA.Homological.L42.Ext

/-!
# Lemma 4.2, part 4: the `η`-semilinear chain map `h : Q_{≤ m} → F`

Level `n` of `h` is given by values `Y p q i j ∈ F_n` on basis tensors `e_i ⊗ e_j ∈ F_p ⊗ F_q`
(zero unless `p + q = n`).  `bd Y p q : F_p ⊗ F_q → F_n` is the value of `h_n ∘ D` on that
bidegree.  We construct all levels by lifting through the resolution.
-/

@[expose] public section

namespace TheoremA

open TensorProduct

universe u

variable {B : Type u} [Group B] {k : ℕ}

namespace L42

variable (R : Res B k) (α β : B →* B)

/-- Values on basis tensors for one level `n`. -/
abbrev Lvl (n : ℕ) := ∀ p q, Fin (R.c p) → Fin (R.c q) → F R n

/-- The component `h_n : F_p ⊗ F_q → F_n`. -/
noncomputable abbrev Hm {n : ℕ} (Y : Lvl R n) (p q : ℕ) : T R p q →+ F R n :=
  hExt R α β (Y p q)

/-- The `d ⊗ 1` part of `h_n ∘ D` on bidegree `(p, q)`. -/
noncomputable def bdL {n : ℕ} (Y : Lvl R n) : ∀ p q, T R p q →+ F R n
  | 0, _ => 0
  | p + 1, q => (Hm R α β Y p q).comp (dL R p q).toAddMonoidHom

/-- The `1 ⊗ d` part of `h_n ∘ D` on bidegree `(p, q)` (without sign). -/
noncomputable def bdR {n : ℕ} (Y : Lvl R n) : ∀ p q, T R p q →+ F R n
  | _, 0 => 0
  | p, q + 1 => (Hm R α β Y p q).comp (dR R p q).toAddMonoidHom

/-- `h_n ∘ D` on bidegree `(p, q)`. -/
noncomputable def bd {n : ℕ} (Y : Lvl R n) (p q : ℕ) (t : T R p q) : F R n :=
  bdL R α β Y p q t + ((-1 : ℤ) ^ p) • bdR R α β Y p q t

@[simp] theorem bdL_zero {n : ℕ} (Y : Lvl R n) (q : ℕ) (t : T R 0 q) : bdL R α β Y 0 q t = 0 := rfl
@[simp] theorem bdL_succ {n : ℕ} (Y : Lvl R n) (p q : ℕ) (t : T R (p + 1) q) :
    bdL R α β Y (p + 1) q t = Hm R α β Y p q (dL R p q t) := rfl
@[simp] theorem bdR_zero {n : ℕ} (Y : Lvl R n) (p : ℕ) (t : T R p 0) : bdR R α β Y p 0 t = 0 := rfl
@[simp] theorem bdR_succ {n : ℕ} (Y : Lvl R n) (p q : ℕ) (t : T R p (q + 1)) :
    bdR R α β Y p (q + 1) t = Hm R α β Y p q (dR R p q t) := rfl

theorem bd_add {n : ℕ} (Y : Lvl R n) (p q : ℕ) (t t' : T R p q) :
    bd R α β Y p q (t + t') = bd R α β Y p q t + bd R α β Y p q t' := by
  simp only [bd, map_add, smul_add]; abel

/-- A level is concentrated on the diagonal `p + q = n`. -/
def OffZero {n : ℕ} (Y : Lvl R n) : Prop := ∀ p q, p + q ≠ n → Y p q = 0

theorem Hm_off {n : ℕ} {Y : Lvl R n} (hY : OffZero R Y) {p q : ℕ} (h : p + q ≠ n) (t : T R p q) :
    Hm R α β Y p q t = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, add_zero]
  | tmul x y => simp [hExt_tmul, hY p q h]

theorem bd_off {n : ℕ} {Y : Lvl R n} (hY : OffZero R Y) {p q : ℕ} (h : p + q ≠ n + 1)
    (t : T R p q) : bd R α β Y p q t = 0 := by
  rcases p with _ | p <;> rcases q with _ | q
  · simp [bd]
  · simp [bd, Hm_off R α β hY (show 0 + q ≠ n by omega)]
  · simp [bd, Hm_off R α β hY (show p + 0 ≠ n by omega)]
  · simp [bd, Hm_off R α β hY (show p + (q + 1) ≠ n by omega),
      Hm_off R α β hY (show p + 1 + q ≠ n by omega)]

/-- `ε ⊗ ε : F_0 ⊗ F_0 → ℤ`. -/
noncomputable def εε : T R 0 0 →ₗ[ℤ] ℤ := (TensorProduct.lid ℤ ℤ) ∘ₗ map (εZ R) (εZ R)

@[simp] theorem εε_tmul (x y : F R 0) : εε R (x ⊗ₜ y) = R.ε x * R.ε y := rfl

theorem εε_dL (t : T R 1 0) : εε R (dL R 0 0 t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | tmul x y => simp [R.ε_d]

theorem εε_dR (t : T R 0 1) : εε R (dR R 0 0 t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | tmul x y => simp [R.ε_d]

section equivariance

variable {α β} (hαβ : ∀ b c, Commute (α b) (β c))
include hαβ

theorem Hm_act {n : ℕ} (Y : Lvl R n) (p q : ℕ) (b c : B) (t : T R p q) :
    Hm R α β Y p q (act R p q b c t) = MonoidAlgebra.of ℤ B (α b * β c) • Hm R α β Y p q t :=
  hExt_act R α β hαβ _ b c t

theorem bd_act {n : ℕ} (Y : Lvl R n) (p q : ℕ) (b c : B) (t : T R p q) :
    bd R α β Y p q (act R p q b c t) = MonoidAlgebra.of ℤ B (α b * β c) • bd R α β Y p q t := by
  simp only [bd, smul_add]
  congr 1
  · rcases p with _ | p
    · simp
    · simp only [bdL_succ, dL_act, Hm_act R hαβ]
  · rw [smul_comm (MonoidAlgebra.of ℤ B _) ((-1 : ℤ) ^ p)]
    congr 1
    rcases q with _ | q
    · simp
    · simp only [bdR_succ, dR_act, Hm_act R hαβ]

/-- The chain condition, checked on basis tensors, holds on all tensors. -/
theorem chain_of_basis {n : ℕ} (Y : Lvl R n) (Y' : Lvl R (n + 1)) (p q : ℕ)
    (h : ∀ i j, R.d n (Y' p q i j) = bd R α β Y p q (Pi.single i 1 ⊗ₜ Pi.single j 1))
    (t : T R p q) : R.d n (Hm R α β Y' p q t) = bd R α β Y p q t := by
  let φ : T R p q →+ F R n := (R.d n).toAddMonoidHom.comp (Hm R α β Y' p q)
  let ψ : T R p q →+ F R n :=
    { toFun := bd R α β Y p q
      map_zero' := by simp [bd]
      map_add' := bd_add R α β Y p q }
  have := tensor_hom_ext R (fun b c => DistribSMul.toAddMonoidHom _ (MonoidAlgebra.of ℤ B (α b * β c)))
    (φ := φ) (ψ := ψ)
    (fun b c t => by simp [φ, Hm_act R hαβ])
    (fun b c t => by simp [ψ, bd_act R hαβ])
    (fun i j => by simp [φ, ψ, hExt_basis, h])
  exact congrArg (fun f => f t) this

end equivariance

end L42

namespace L42

variable (R : Res B k) (α β : B →* B)

theorem bdL_dL {n : ℕ} (Y : Lvl R n) (p q : ℕ) (hp : p ≤ k) (t : T R (p + 1) q) :
    bdL R α β Y p q (dL R p q t) = 0 := by
  rcases p with _ | p
  · rfl
  · rw [bdL_succ, dL_dL R p q (by omega), map_zero]

theorem bdR_dR {n : ℕ} (Y : Lvl R n) (p q : ℕ) (hq : q ≤ k) (t : T R p (q + 1)) :
    bdR R α β Y p q (dR R p q t) = 0 := by
  rcases q with _ | q
  · rfl
  · rw [bdR_succ, dR_dR R p q (by omega), map_zero]

/-- `d ∘ (h ∘ D) = 0`: the boundary values of a chain map are cycles. -/
theorem d_bd {n : ℕ} (Y : Lvl R n) (Y' : Lvl R (n + 1))
    (hch : ∀ p q t, R.d n (Hm R α β Y' p q t) = bd R α β Y p q t) (p q : ℕ) (hp : p ≤ k + 1)
    (hq : q ≤ k + 1) (t : T R p q) : R.d n (bd R α β Y' p q t) = 0 := by
  rcases p with _ | p <;> rcases q with _ | q
  · simp [bd]
  · simp only [bd, bdL_zero, bdR_succ, pow_zero, one_smul, zero_add]
    rw [hch, bd, bdR_dR R α β Y 0 q (by omega), bdL_zero, smul_zero, add_zero]
  · simp only [bd, bdL_succ, bdR_zero, smul_zero, add_zero]
    rw [hch, bd, bdL_dL R α β Y p 0 (by omega), bdR_zero, smul_zero, add_zero]
  · simp only [bd, bdL_succ, bdR_succ, map_add, map_zsmul]
    rw [hch, hch, bd, bd, bdL_dL R α β Y p (q + 1) (by omega),
      bdR_dR R α β Y (p + 1) q (by omega), bdR_succ, bdL_succ, dL_dR, sign_succ]
    simp only [smul_zero, zero_add, add_zero]
    exact add_neg_cancel _

end L42

end TheoremA
