module

public import RequestProject.TheoremA.Homological.L42.Tensor

/-!
# Lemma 4.2, part 2: the contracting homotopy of `F ⊗_ℤ F`

From the integral contraction `σ` of `F` we build `Σ = σ ⊗ 1 + ιε ⊗ σ` on bigraded families and
compute `DΣ + ΣD` componentwise.  Consequences: cycles of total degree `1, …, k` are boundaries
(`DΣz = z`), and in degree `0` and `m = k + 1` we identify the correction terms.
-/

@[expose] public section

namespace TheoremA

open TensorProduct

universe u

variable {B : Type u} [Group B] {k : ℕ}

namespace L42

variable {R : Res B k} (C : Contr R)

/-- `x ↦ ε(x) x₀`. -/
noncomputable def ιε : F R 0 →ₗ[ℤ] F R 0 := (LinearMap.toSpanSingleton ℤ (F R 0) C.x0) ∘ₗ εZ R

@[simp] theorem ιε_apply (x : F R 0) : ιε C x = R.ε x • C.x0 := rfl

theorem c0' : dZ R 0 ∘ₗ C.σ 0 + ιε C = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, ιε_apply, LinearMap.id_apply]
  exact C.c0 x

theorem ci' (i : ℕ) (hi : i < k) :
    dZ R (i + 1) ∘ₗ C.σ (i + 1) + C.σ i ∘ₗ dZ R i = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
  exact C.ci i hi x

theorem ιε_dZ : ιε C ∘ₗ dZ R 0 = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, ιε_apply, LinearMap.zero_apply]
  rw [show R.ε (dZ R 0 x) = 0 from R.ε_d x, zero_smul]

theorem ιε_ιε : ιε C ∘ₗ ιε C = ιε C := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, ιε_apply, map_zsmul, C.hx0, one_smul]

/-- The raw components of `Σ z`. -/
noncomputable def SigF (z : Qm R) : ∀ p q, T R p q
  | p + 1, q => map (C.σ p) LinearMap.id (z p q)
  | 0, q + 1 => map (ιε C) (C.σ q) (z 0 q)
  | 0, 0 => 0

/-- The contracting homotopy `Σ`. -/
noncomputable def Sig : Qm R →+ Qm R where
  toFun := SigF C
  map_zero' := by
    funext p q; rcases p with _ | p <;> rcases q with _ | q <;> simp [SigF]
  map_add' z w := by
    funext p q; rcases p with _ | p <;> rcases q with _ | q <;> simp [SigF]

@[simp] theorem Sig_succ (z : Qm R) (p q : ℕ) :
    Sig C z (p + 1) q = map (C.σ p) LinearMap.id (z p q) := rfl
@[simp] theorem Sig_zero_succ (z : Qm R) (q : ℕ) :
    Sig C z 0 (q + 1) = map (ιε C) (C.σ q) (z 0 q) := rfl
@[simp] theorem Sig_zero_zero (z : Qm R) : Sig C z 0 0 = 0 := rfl

/-- `z` is concentrated in total degree `n`. -/
def IsDeg (n : ℕ) (z : Qm R) : Prop := ∀ p q, p + q ≠ n → z p q = 0

theorem IsDeg.Sig {n : ℕ} {z : Qm R} (h : IsDeg n z) : IsDeg (n + 1) (Sig C z) := by
  intro p q hpq
  rcases p with _ | p <;> rcases q with _ | q
  · rfl
  · simp [h 0 q (by omega)]
  · simp [h p 0 (by omega)]
  · simp [h p (q + 1) (by omega)]

theorem IsDeg.D {n : ℕ} {z : Qm R} (h : IsDeg (n + 1) z) : IsDeg n (D R z) := by
  intro p q hpq
  simp [D_apply, h (p + 1) q (by omega), h p (q + 1) (by omega)]

theorem IsDeg.actQ {n : ℕ} {z : Qm R} (h : IsDeg n z) (b c : B) : IsDeg n (actQ R b c z) := by
  intro p q hpq; simp [h p q hpq]

theorem sign_succ (i : ℕ) {M : Type*} [AddCommGroup M] (x : M) :
    ((-1 : ℤ) ^ (i + 1)) • x = -(((-1 : ℤ) ^ i) • x) := by
  rw [pow_succ, mul_neg_one, neg_smul]

theorem map_add_id {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (a b : M →ₗ[ℤ] P) (g : N →ₗ[ℤ] N) (t : M ⊗[ℤ] N) :
    map a g t + map b g t = map (a + b) g t := by
  rw [map_add_left]; rfl

theorem map_id_add {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    (f : M →ₗ[ℤ] M) (a b : N →ₗ[ℤ] P) (t : M ⊗[ℤ] N) :
    map f a t + map f b t = map f (a + b) t := by
  rw [map_add_right]; rfl

/-- `DΣ + ΣD = 1` in bidegree `(i+1, q)`, `i < k`. -/
theorem homotopy_succ (z : Qm R) (i q : ℕ) (hi : i < k) :
    D R (Sig C z) (i + 1) q + Sig C (D R z) (i + 1) q = z (i + 1) q := by
  simp only [D_apply, Sig_succ, map_add, map_zsmul, map_map, LinearMap.comp_id,
    LinearMap.id_comp, sign_succ]
  have key := map_add_id (dZ R (i + 1) ∘ₗ C.σ (i + 1)) (C.σ i ∘ₗ dZ R i) LinearMap.id (z (i + 1) q)
  rw [ci' C i hi, map_id, LinearMap.id_apply] at key
  convert key using 1; abel

/-- `DΣ + ΣD = 1` in bidegree `(0, i+1)`, `i < k`. -/
theorem homotopy_zero_succ (z : Qm R) (i : ℕ) (hi : i < k) :
    D R (Sig C z) 0 (i + 1) + Sig C (D R z) 0 (i + 1) = z 0 (i + 1) := by
  simp only [D_apply, Sig_succ, Sig_zero_succ, map_add, map_map, LinearMap.comp_id,
    LinearMap.id_comp, pow_zero, one_smul, ιε_dZ, map_zero_left, LinearMap.zero_apply, zero_add]
  have k1 := map_id_add (ιε C) (dZ R (i + 1) ∘ₗ C.σ (i + 1)) (C.σ i ∘ₗ dZ R i) (z 0 (i + 1))
  rw [ci' C i hi] at k1
  have k2 := map_add_id (dZ R 0 ∘ₗ C.σ 0) (ιε C) LinearMap.id (z 0 (i + 1))
  rw [c0' C, map_id, LinearMap.id_apply] at k2
  rw [← k1] at k2; convert k2 using 1; abel

/-- `DΣ = 1 - ιε ⊗ ιε` in bidegree `(0, 0)`. -/
theorem homotopy_zero_zero (z : Qm R) :
    D R (Sig C z) 0 0 = z 0 0 - map (ιε C) (ιε C) (z 0 0) := by
  simp only [D_apply, Sig_succ, Sig_zero_succ, map_map, LinearMap.comp_id, LinearMap.id_comp,
    pow_zero, one_smul]
  have k1 := map_id_add (ιε C) (dZ R 0 ∘ₗ C.σ 0) (ιε C) (z 0 0)
  rw [c0' C] at k1
  have k2 := map_add_id (dZ R 0 ∘ₗ C.σ 0) (ιε C) LinearMap.id (z 0 0)
  rw [c0' C, map_id, LinearMap.id_apply] at k2
  rw [← k1] at k2; rw [eq_sub_iff_add_eq]; convert k2 using 1; abel

/-- In bidegree `(k+1, q)`: `DΣ + ΣD = σ d ⊗ 1`. -/
theorem homotopy_top (z : Qm R) (q : ℕ) :
    D R (Sig C z) (k + 1) q + Sig C (D R z) (k + 1) q =
      map (C.σ k ∘ₗ dZ R k) LinearMap.id (z (k + 1) q) := by
  simp only [D_apply, Sig_succ, map_add, map_zsmul, map_map, LinearMap.comp_id,
    LinearMap.id_comp, sign_succ, C.σ_top (k + 1) (by omega), map_zero_left,
    LinearMap.zero_apply, zero_add, map_zero]
  abel

/-- In bidegree `(0, k+1)`: `DΣ + ΣD = dσ ⊗ 1 + ιε ⊗ σ d`. -/
theorem homotopy_zero_top (z : Qm R) :
    D R (Sig C z) 0 (k + 1) + Sig C (D R z) 0 (k + 1) =
      map (dZ R 0 ∘ₗ C.σ 0) LinearMap.id (z 0 (k + 1)) +
        map (ιε C) (C.σ k ∘ₗ dZ R k) (z 0 (k + 1)) := by
  simp only [D_apply, Sig_succ, Sig_zero_succ, map_add, map_map, LinearMap.comp_id,
    pow_zero, one_smul, ιε_dZ, map_zero_left, LinearMap.zero_apply, zero_add,
    C.σ_top (k + 1) (by omega), map_zero_right, map_zero, add_zero]

/-- **(K1)** Cycles of total degree `n`, `1 ≤ n ≤ k`, are boundaries: `D (Σ z) = z`. -/
theorem D_Sig_of_cycle {n : ℕ} {z : Qm R} (hz : IsDeg n z) (hD : D R z = 0) (hn1 : 1 ≤ n)
    (hnk : n ≤ k) : D R (Sig C z) = z := by
  funext p q
  by_cases hpq : p + q = n
  · rcases p with _ | p
    · obtain ⟨i, rfl⟩ : ∃ i, q = i + 1 := ⟨q - 1, by omega⟩
      have := homotopy_zero_succ C z i (by omega)
      rwa [hD, map_zero, Pi.zero_apply, Pi.zero_apply, add_zero] at this
    · have := homotopy_succ C z p q (by omega)
      rwa [hD, map_zero, Pi.zero_apply, Pi.zero_apply, add_zero] at this
  · rw [(hz.Sig C).D p q hpq, hz p q hpq]

/-- Degree-`0` version of (K1). -/
theorem D_Sig_deg0 {z : Qm R} (hz : IsDeg 0 z) (h00 : map (ιε C) (ιε C) (z 0 0) = 0) :
    D R (Sig C z) = z := by
  funext p q
  by_cases h : p = 0 ∧ q = 0
  · obtain ⟨rfl, rfl⟩ := h
    rw [homotopy_zero_zero, h00, sub_zero]
  · rw [(hz.Sig C).D p q (by omega), hz p q (by omega)]

end L42

end TheoremA
