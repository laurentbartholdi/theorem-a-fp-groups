module

public import RequestProject.TheoremA.Homological.Lifts

/-!
# The generator boundary and exactness at degree zero

Let `G` be a group and `x : Fin n → G` a generating tuple (`Subgroup.closure (range x) = ⊤`).
With `Λ = ℤ[G]` (`ZG G`), `C₁ = Λ^n` (`FreeMod G n`) and `C₀ = Λ`, the generator boundary is the
left `Λ`-linear map

  `genBoundary x : C₁ → C₀`,  `e_i ↦ [x_i] - 1`,

so `genBoundary x v = ∑ i, v i * ([x_i] - 1)`.  The augmentation is the project's
`augZG : ℤ[G] →+* ℤ`, `∑ a_g [g] ↦ ∑ a_g`; as a map to the trivial module `ℤ` it is `Λ`-linear
(`augZG_smul`).

Main results:
* `augZG_surjective`, `augZG_genBoundary` (`ε ∘ d₁ = 0`);
* `mem_range_genBoundary_iff`: for a generating tuple, `range d₁ = ker ε`
  (no finiteness, presentation or decidability hypothesis on `G`; `n = 0` is allowed).
-/

@[expose] public section

namespace TheoremA

universe u

variable {G : Type u} [Group G]

/-- The group-ring element `[g] - 1`. -/
noncomputable abbrev gm1 (g : G) : ZG G := MonoidAlgebra.of ℤ G g - 1

/-- The generator boundary `d₁ : ℤ[G]^n → ℤ[G]`, `e_i ↦ [x_i] - 1`, extended left-linearly. -/
noncomputable def genBoundary {n : ℕ} (x : Fin n → G) : FreeMod G n →ₗ[ZG G] ZG G :=
  Fintype.linearCombination (ZG G) fun i => gm1 (x i)

theorem genBoundary_apply {n : ℕ} (x : Fin n → G) (v : FreeMod G n) :
    genBoundary x v = ∑ i, v i * gm1 (x i) := by
  simp [genBoundary, Fintype.linearCombination_apply, smul_eq_mul]

theorem genBoundary_single {n : ℕ} (x : Fin n → G) (i : Fin n) :
    genBoundary x (Pi.single i 1) = gm1 (x i) := by
  rw [genBoundary_apply]
  simp [Pi.single_apply]

/-- The augmentation is surjective. -/
theorem augZG_surjective : Function.Surjective (augZG : ZG G →+* ℤ) :=
  fun m => ⟨MonoidAlgebra.single 1 m, augZG_single 1 m⟩

/-- The augmentation is `Λ`-linear to the trivial module `ℤ`. -/
theorem augZG_smul (l a : ZG G) : augZG (l • a) = augZG l * augZG a := by
  rw [smul_eq_mul, map_mul]

/-- The augmentation is invariant under the group action. -/
theorem augZG_of_smul (g : G) (a : ZG G) : augZG (MonoidAlgebra.of ℤ G g • a) = augZG a := by
  rw [augZG_smul]; simp

theorem augZG_gm1 (g : G) : augZG (gm1 g) = 0 := by
  simp [gm1]

/-- `ε ∘ d₁ = 0`. -/
theorem augZG_genBoundary {n : ℕ} (x : Fin n → G) (v : FreeMod G n) :
    augZG (genBoundary x v) = 0 := by
  rw [genBoundary_apply, map_sum]
  simp [augZG_gm1]

/-- Every `[g] - 1` with `g` in the generated subgroup lies in the range of `d₁`. -/
theorem gm1_mem_range_genBoundary {n : ℕ} (x : Fin n → G) {g : G}
    (hg : g ∈ Subgroup.closure (Set.range x)) : gm1 g ∈ LinearMap.range (genBoundary x) := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact ⟨Pi.single i 1, genBoundary_single x i⟩
  | one => rw [gm1, map_one, sub_self]; exact Submodule.zero_mem _
  | mul a b _ _ ha hb =>
    have : gm1 (a * b) = MonoidAlgebra.of ℤ G a • gm1 b + gm1 a := by
      simp only [gm1, map_mul, smul_eq_mul, mul_sub, mul_one]; abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hb) ha
  | inv a _ ha =>
    have : gm1 a⁻¹ = -(MonoidAlgebra.of ℤ G a⁻¹ • gm1 a) := by
      simp only [gm1, smul_eq_mul, mul_sub, ← map_mul, inv_mul_cancel, map_one, mul_one]; abel
    rw [this]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ ha)

/-- For a generating tuple, every element minus its augmentation lies in `range d₁`. -/
theorem sub_augZG_mem_range_genBoundary {n : ℕ} (x : Fin n → G)
    (hx : Subgroup.closure (Set.range x) = ⊤) (a : ZG G) :
    a - MonoidAlgebra.single 1 (augZG a) ∈ LinearMap.range (genBoundary x) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    have : a + b - MonoidAlgebra.single 1 (augZG (a + b)) =
        (a - MonoidAlgebra.single 1 (augZG a)) + (b - MonoidAlgebra.single 1 (augZG b)) := by
      rw [map_add, MonoidAlgebra.single_add]; abel
    rw [this]; exact Submodule.add_mem _ ha hb
  | single g m =>
    have : (MonoidAlgebra.single g m : ZG G) - MonoidAlgebra.single 1 (augZG (MonoidAlgebra.single g m)) =
        (MonoidAlgebra.single 1 m : ZG G) • gm1 g := by
      rw [augZG_single, smul_eq_mul, gm1, mul_sub, mul_one, MonoidAlgebra.of_apply,
        MonoidAlgebra.single_mul_single, one_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (gm1_mem_range_genBoundary x (hx ▸ Subgroup.mem_top g))

/-- **Exactness at `C₀`.** For a generating tuple `x`, `range d₁ = ker ε`. -/
theorem mem_range_genBoundary_iff {n : ℕ} (x : Fin n → G)
    (hx : Subgroup.closure (Set.range x) = ⊤) (a : ZG G) :
    a ∈ LinearMap.range (genBoundary x) ↔ augZG a = 0 := by
  constructor
  · rintro ⟨v, rfl⟩; exact augZG_genBoundary x v
  · intro ha
    have := sub_augZG_mem_range_genBoundary x hx a
    rwa [ha, MonoidAlgebra.single_zero, sub_zero] at this

/-- **Exactness at `C₀`**, as an equality of additive subgroups of `ℤ[G]`. -/
theorem range_genBoundary_eq_ker_augZG {n : ℕ} (x : Fin n → G)
    (hx : Subgroup.closure (Set.range x) = ⊤) :
    (LinearMap.range (genBoundary x)).toAddSubgroup = (augZG : ZG G →+* ℤ).toAddMonoidHom.ker := by
  ext a
  exact mem_range_genBoundary_iff x hx a

end TheoremA
