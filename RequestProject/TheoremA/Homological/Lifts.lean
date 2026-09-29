module

public import RequestProject.TheoremA.Homological.Setup

/-!
# Semilinear maps on free modules, chain lifts and the comparison lemma (Lemma 4.1)
-/

@[expose] public section

namespace TheoremA

universe u

variable {B : Type u} [Group B]

/-- The `σ`-semilinear additive map `Λ^n → N` sending the `i`-th basis vector to `y i`. -/
noncomputable def semiExt {N : Type*} [AddCommGroup N] [Module (ZG B) N] (σ : ZG B →+* ZG B)
    {n : ℕ} (y : Fin n → N) : FreeMod B n →+ N where
  toFun x := ∑ i, σ (x i) • y i
  map_zero' := by simp
  map_add' x x' := by simp [add_smul, Finset.sum_add_distrib]

theorem semiExt_smul {N : Type*} [AddCommGroup N] [Module (ZG B) N] (σ : ZG B →+* ZG B)
    {n : ℕ} (y : Fin n → N) (l : ZG B) (x : FreeMod B n) :
    semiExt σ y (l • x) = σ l • semiExt σ y x := by
  simp [semiExt, Finset.smul_sum, mul_smul]

theorem semiExt_single {N : Type*} [AddCommGroup N] [Module (ZG B) N] (σ : ZG B →+* ZG B)
    {n : ℕ} (y : Fin n → N) (j : Fin n) : semiExt σ y (Pi.single j 1) = y j := by
  simp [semiExt, Pi.single_apply]

theorem eq_sum_single {n : ℕ} (x : FreeMod B n) :
    x = ∑ i, x i • (Pi.single i 1 : FreeMod B n) := by
  ext j; simp [Pi.single_apply]

/-- Two `σ`-semilinear additive maps on `Λ^n` agreeing on the basis are equal. -/
theorem semilinear_ext {N : Type*} [AddCommGroup N] [Module (ZG B) N] (σ : ZG B →+* ZG B)
    {n : ℕ} (f g : FreeMod B n →+ N) (hf : ∀ l x, f (l • x) = σ l • f x)
    (hg : ∀ l x, g (l • x) = σ l • g x) (h : ∀ j, f (Pi.single j 1) = g (Pi.single j 1)) :
    f = g := by
  refine AddMonoidHom.ext fun x => ?_
  rw [eq_sum_single x]
  simp [map_sum, hf, hg, h]

/-- The image of a `σ`-semilinear map on `Λ^n` lies in the span of the images of the basis. -/
theorem semilinear_mem_span {N : Type*} [AddCommGroup N] [Module (ZG B) N] (σ : ZG B →+* ZG B)
    {n : ℕ} (f : FreeMod B n →+ N) (hf : ∀ l x, f (l • x) = σ l • f x) (x : FreeMod B n) :
    f x ∈ Submodule.span (ZG B) (Set.range fun j => f (Pi.single j 1)) := by
  rw [eq_sum_single x, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hf]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- The augmentation `ℤ[B] → ℤ`. -/
noncomputable def augZG : ZG B →+* ℤ :=
  (MonoidAlgebra.lift ℤ ℤ B (1 : B →* ℤ)).toRingHom

@[simp] theorem augZG_single (g : B) (n : ℤ) : augZG (MonoidAlgebra.single g n : ZG B) = n := by
  simp [augZG, MonoidAlgebra.lift_single]

@[simp] theorem augZG_mapDomain (θ : B →* B) (l : ZG B) :
    augZG (MonoidAlgebra.mapDomain θ l) = augZG l := by
  induction l using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [MonoidAlgebra.mapDomain_add, map_add, map_add, ha, hb]
  | single g n => simp

theorem augZG_hat (θ : B →* B) (l : ZG B) : augZG (hat θ l) = augZG l :=
  augZG_mapDomain θ l

namespace Res

variable {k : ℕ} (R : Res B k)

theorem ε_smul (l : ZG B) (x : FreeMod B (R.c 0)) : R.ε (l • x) = augZG l * R.ε x := by
  induction l using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [add_smul, ha, hb, add_mul]
  | single g n =>
    have : (MonoidAlgebra.single g n : ZG B) • x = n • (MonoidAlgebra.of ℤ B g • x) := by
      rw [← smul_assoc]; congr 1
      simp
    rw [this, map_zsmul, R.ε_inv]; simp

theorem d_d (i : ℕ) (hi : i < k) (x : FreeMod B (R.c (i + 2))) :
    R.d i (R.d (i + 1) x) = 0 := by
  have : R.d (i + 1) x ∈ LinearMap.ker (R.d i) := by
    rw [R.exact i hi]; exact ⟨x, rfl⟩
  exact this

theorem ε_d (x : FreeMod B (R.c 1)) : R.ε (R.d 0 x) = 0 := by
  have : R.d 0 x ∈ R.ε.ker := by
    rw [R.exact0]; exact ⟨x, rfl⟩
  exact this

end Res

/-- A partial chain lift: semilinear, augmentation-preserving, commuting in degrees `< n`. -/
def PartialLift {k : ℕ} (R : Res B k) (θ : B →* B) (n : ℕ)
    (Φ : ∀ i, FreeMod B (R.c i) →+ FreeMod B (R.c i)) : Prop :=
  (∀ i (l : ZG B) (x : FreeMod B (R.c i)), Φ i (l • x) = hat θ l • Φ i x) ∧
  (∀ x, R.ε (Φ 0 x) = R.ε x) ∧
  (∀ i, i < n → i ≤ k → ∀ x, Φ i (R.d i x) = R.d i (Φ (i + 1) x))

theorem exists_partialLift {k : ℕ} (R : Res B k) (θ : B →* B) :
    ∀ n, ∃ Φ, PartialLift R θ n Φ := by
  intro n
  induction n with
  | zero =>
    choose y hy using fun j : Fin (R.c 0) => R.ε_surj (R.ε (Pi.single j 1))
    classical
    refine ⟨fun i => if h : i = 0 then h ▸ semiExt (hat θ) y else 0, ?_, ?_, ?_⟩
    · intro i l x
      by_cases h : i = 0
      · subst h; simp [semiExt_smul]
      · simp [h]
    · intro x
      simp only [dite_true]
      conv_rhs => rw [eq_sum_single x]
      simp [semiExt, map_sum, Res.ε_smul, hy]
    · intro i hi; omega
  | succ n ih =>
    obtain ⟨Φ, hsl, haug, hcomm⟩ := ih
    by_cases hn : n ≤ k
    · -- choose lifts of `Φ n (d n e_j)` through `d n`
      have hmem : ∀ j : Fin (R.c (n + 1)),
          Φ n (R.d n (Pi.single j 1)) ∈ LinearMap.range (R.d n) := by
        intro j
        cases n with
        | zero =>
          have : Φ 0 (R.d 0 (Pi.single j 1)) ∈ R.ε.ker := by
            show R.ε _ = 0
            rw [haug, R.ε_d]
          rw [R.exact0] at this
          exact this
        | succ n' =>
          rw [← R.exact n' (by omega)]
          show R.d n' _ = 0
          rw [← hcomm n' (by omega) (by omega), R.d_d n' (by omega), map_zero]
      choose y hy using hmem
      classical
      let f : FreeMod B (R.c (n + 1)) →+ FreeMod B (R.c (n + 1)) := semiExt (hat θ) y
      refine ⟨Function.update (β := fun i => FreeMod B (R.c i) →+ FreeMod B (R.c i)) Φ (n + 1) f,
        ?_, ?_, ?_⟩
      · intro i l x
        by_cases h : i = n + 1
        · subst h; simp [f, semiExt_smul]
        · simp [Function.update_of_ne h, hsl]
      · intro x
        rw [Function.update_of_ne (by omega)]; exact haug x
      · intro i hi hik x
        rw [Function.update_of_ne (by omega)]
        by_cases h : i = n
        · subst h
          rw [Function.update_self]
          have := semilinear_ext (hat θ) ((Φ i).comp (R.d i).toAddMonoidHom)
            ((R.d i).toAddMonoidHom.comp f)
            (fun l x => by simp [hsl]) (fun l x => by simp [f, semiExt_smul])
            (fun j => by simp [f, semiExt_single, hy])
          exact congrArg (fun F => F x) this
        · rw [Function.update_of_ne (by omega)]
          exact hcomm i (by omega) hik x
    · exact ⟨Φ, hsl, haug, fun i hi hik x => hcomm i (by omega) hik x⟩

/-- Chain lifts exist (§4, before Lemma 4.1). -/
theorem exists_chainLift {k : ℕ} (R : Res B k) (θ : B →* B) : ∃ Φ, IsChainLift R θ Φ := by
  obtain ⟨Φ, hsl, haug, hcomm⟩ := exists_partialLift R θ (k + 1)
  exact ⟨Φ, ⟨hsl, fun i hi x => hcomm i (by omega) hi x, haug⟩⟩

end TheoremA
