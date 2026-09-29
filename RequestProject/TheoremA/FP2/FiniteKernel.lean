module

public import RequestProject.TheoremA.FP2.Augmentation
public import RequestProject.TheoremA.Homological.FPData

/-!
# The finite-kernel criterion for `FP₂`

For a generating tuple `x : Fin n → G`, let `K = ker (genBoundary x) ≤ ℤ[G]^n`.  Then

  `IsFP 2 G ↔ K.FG`   (`isFP_two_iff_fg_ker_genBoundary`).

* Sufficiency (`isFP_two_of_fg_ker_genBoundary`): the generator boundary together with the
  augmentation is a partial resolution of length one (`genFPData`), and a finite free module
  mapping onto `K` supplies the degree-two term (`FPData.isFP_succ`).
* Necessity (`fg_ker_genBoundary_of_isFP_two`): an explicit comparison of an arbitrary partial
  resolution `P₂ → P₁ → P₀ → ℤ` with `C₁ → C₀ → ℤ`.  With chain maps `α, α₁` and `β, β₁` and a
  homotopy `s₀`, `K = span {T eᵢ} ⊔ β₁(ker d₀)` for `T = id - β₁α₁ - s₀ d₁`; both pieces are
  finitely generated.  No Noetherian hypothesis is used.

`isFP_two_of_span` is the convenient sufficiency corollary for a finite spanning family of `K`.
-/

@[expose] public section

namespace TheoremA

universe u

variable {G : Type u} [Group G]

/-- `ℤ[G]^1 ≃ ℤ[G]`. -/
noncomputable abbrev freeModOneEquiv (G : Type u) [Group G] : FreeMod G 1 ≃ₗ[ZG G] ZG G :=
  LinearEquiv.funUnique (Fin 1) (ZG G) (ZG G)

/-- The ranks `1, n, n, …` of the length-one partial resolution `ℤ[G]^n → ℤ[G] → ℤ`. -/
def genRanks (n : ℕ) : ℕ → ℕ := fun i => Nat.rec 1 (fun _ _ => n) i

/-- The partial resolution `ℤ[G]^n → ℤ[G] → ℤ → 0` of length one given by a generating tuple. -/
noncomputable def genFPData {n : ℕ} (x : Fin n → G) (hx : Subgroup.closure (Set.range x) = ⊤) :
    FPData G 1 where
  c := genRanks n
  d i := Nat.rec (motive := fun i => FreeMod G (genRanks n (i + 1)) →ₗ[ZG G]
      FreeMod G (genRanks n i))
    ((freeModOneEquiv G).symm.toLinearMap ∘ₗ genBoundary x) (fun _ _ => 0) i
  ε := (augZG : ZG G →+* ℤ).toAddMonoidHom.comp (freeModOneEquiv G).toLinearMap.toAddMonoidHom
  ε_inv g v := by
    show augZG (freeModOneEquiv G (MonoidAlgebra.of ℤ G g • v)) = augZG (freeModOneEquiv G v)
    rw [LinearEquiv.map_smul, augZG_of_smul]
  ε_surj m := by
    obtain ⟨a, ha⟩ := augZG_surjective (G := G) m
    exact ⟨(freeModOneEquiv G).symm a, by simpa using ha⟩
  exact0 _ := by
    ext v
    show augZG (freeModOneEquiv G v) = 0 ↔ _
    rw [← mem_range_genBoundary_iff x hx]
    simp only [Submodule.mem_toAddSubgroup, LinearMap.mem_range]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨w, ?_⟩
      show (freeModOneEquiv G).symm (genBoundary x w) = v
      rw [hw, LinearEquiv.symm_apply_apply]
    · rintro ⟨w, hw⟩
      refine ⟨w, ?_⟩
      rw [← hw]
      exact ((freeModOneEquiv G).apply_symm_apply _).symm
  exact i hi := absurd hi (by omega)

/-- **Sufficiency.** For a generating tuple, if `ker d₁` is finitely generated then `G` has type
`FP₂`. -/
theorem isFP_two_of_fg_ker_genBoundary {n : ℕ} (x : Fin n → G)
    (hx : Subgroup.closure (Set.range x) = ⊤) (hK : (LinearMap.ker (genBoundary x)).FG) :
    IsFP 2 G := by
  obtain ⟨m, k, hk⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  refine (genFPData x hx).isFP_succ (n := 0) m (Fintype.linearCombination (ZG G) k) ?_
  rw [Fintype.range_linearCombination, hk]
  ext v
  show genBoundary x v = 0 ↔ (freeModOneEquiv G).symm (genBoundary x v) = 0
  simp

/-- **Sufficiency corollary.** If a finite family of elements of `ker d₁` spans it, then `G`
has type `FP₂`. -/
theorem isFP_two_of_span {n : ℕ} (x : Fin n → G) (hx : Subgroup.closure (Set.range x) = ⊤)
    {m : ℕ} (k : Fin m → FreeMod G n)
    (hk : Submodule.span (ZG G) (Set.range k) = LinearMap.ker (genBoundary x)) : IsFP 2 G :=
  isFP_two_of_fg_ker_genBoundary x hx (hk ▸ Submodule.fg_span (Set.finite_range k))

/-- The range of a linear map out of a finite free module is finitely generated. -/
theorem fg_range_freeMod {M : Type*} [AddCommGroup M] [Module (ZG G) M] {q : ℕ}
    (f : FreeMod G q →ₗ[ZG G] M) : (LinearMap.range f).FG := by
  rw [LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map f

/-- **Necessity.** For a generating tuple, if `G` has type `FP₂` then `ker d₁` is finitely
generated. -/
theorem fg_ker_genBoundary_of_isFP_two {n : ℕ} (x : Fin n → G)
    (hx : Subgroup.closure (Set.range x) = ⊤) (hG : IsFP 2 G) :
    (LinearMap.ker (genBoundary x)).FG := by
  classical
  obtain ⟨c, d, ε, hinv, hsurj, h0, hex⟩ := hG
  let R : Res G 0 := ⟨c, d, ε, hinv, hsurj, h0 (by omega), fun i hi => absurd hi (by omega)⟩
  have hεs : ∀ (l : ZG G) v, ε (l • v) = augZG l * ε v := R.ε_smul
  have hεd : ∀ v, ε (d 0 v) = 0 := R.ε_d
  have hker0 : ∀ v, ε v = 0 → v ∈ LinearMap.range (d 0) := by
    intro v hv
    have : v ∈ ε.ker := hv
    rw [h0 (by omega)] at this; exact this
  set d₁ := genBoundary x with hd₁
  -- comparison maps in degree zero
  obtain ⟨p, hp⟩ := hsurj 1
  let α : ZG G →ₗ[ZG G] FreeMod G (c 0) := LinearMap.toSpanSingleton (ZG G) _ p
  let β : FreeMod G (c 0) →ₗ[ZG G] ZG G :=
    Fintype.linearCombination (ZG G) fun j => MonoidAlgebra.single 1 (ε (Pi.single j 1))
  have hαapp : ∀ l, α l = l • p := fun l => rfl
  have hεα : ∀ l, ε (α l) = augZG l := by intro l; rw [hαapp, hεs, hp, mul_one]
  have hβaug : ∀ v, augZG (β v) = ε v := by
    intro v
    conv_rhs => rw [eq_sum_single v]
    simp [β, Fintype.linearCombination_apply, map_sum, hεs]
  have hβα : ∀ l, β (α l) = l * β p := by
    intro l; rw [hαapp, LinearMap.map_smul, smul_eq_mul]
  -- comparison maps in degree one
  have ha : ∀ i, ∃ a, d 0 a = α (d₁ (Pi.single i 1)) := by
    intro i
    obtain ⟨a, ha⟩ := hker0 (α (d₁ (Pi.single i 1))) (by rw [hεα]; exact augZG_genBoundary x _)
    exact ⟨a, ha⟩
  choose a ha using ha
  have hb : ∀ j, ∃ b, d₁ b = β (d 0 (Pi.single j 1)) := by
    intro j
    have : β (d 0 (Pi.single j 1)) ∈ LinearMap.range d₁ := by
      rw [hd₁, mem_range_genBoundary_iff x hx, hβaug, hεd]
    exact this
  choose b hb using hb
  let α₁ : FreeMod G n →ₗ[ZG G] FreeMod G (c 1) := Fintype.linearCombination (ZG G) a
  let β₁ : FreeMod G (c 1) →ₗ[ZG G] FreeMod G n := Fintype.linearCombination (ZG G) b
  have hα₁ : ∀ v, d 0 (α₁ v) = α (d₁ v) := by
    intro v
    rw [show α₁ v = ∑ i, v i • a i from Fintype.linearCombination_apply _ _ _]
    conv_rhs => rw [eq_sum_single v]
    simp only [map_sum, LinearMap.map_smul, ha]
  have hβ₁ : ∀ w, d₁ (β₁ w) = β (d 0 w) := by
    intro w
    rw [show β₁ w = ∑ j, w j • b j from Fintype.linearCombination_apply _ _ _]
    conv_rhs => rw [eq_sum_single w]
    simp only [map_sum, LinearMap.map_smul, hb]
  -- the homotopy in degree zero
  obtain ⟨s₀, hs₀⟩ : 1 - β p ∈ LinearMap.range d₁ := by
    rw [hd₁, mem_range_genBoundary_iff x hx, map_sub, hβaug, hp, map_one, sub_self]
  let T : FreeMod G n →ₗ[ZG G] FreeMod G n :=
    LinearMap.id - β₁ ∘ₗ α₁ - LinearMap.toSpanSingleton (ZG G) _ s₀ ∘ₗ d₁
  have hTapp : ∀ v, T v = v - β₁ (α₁ v) - d₁ v • s₀ := fun v => rfl
  have hT : ∀ v, d₁ (T v) = 0 := by
    intro v
    rw [hTapp, map_sub, map_sub, hβ₁, hα₁, hβα, LinearMap.map_smul, hs₀, smul_eq_mul,
      mul_sub, mul_one]
    abel
  -- the decomposition of the kernel
  let N₁ : Submodule (ZG G) (FreeMod G n) := Submodule.span (ZG G) (Set.range fun i => T (Pi.single i 1))
  let N₂ : Submodule (ZG G) (FreeMod G n) := (LinearMap.ker (d 0)).map β₁
  have hK : LinearMap.ker d₁ = N₁ ⊔ N₂ := by
    apply le_antisymm
    · intro v hv
      have hv' : d₁ v = 0 := hv
      have hsplit : v = T v + β₁ (α₁ v) := by rw [hTapp, hv', zero_smul]; abel
      rw [hsplit]
      refine Submodule.add_mem_sup ?_ ⟨α₁ v, ?_, rfl⟩
      · have := semilinear_mem_span (RingHom.id (ZG G)) T.toAddMonoidHom
          (fun l w => by simp) v
        simpa using this
      · show d 0 (α₁ v) = 0
        rw [hα₁, hv', map_zero]
    · refine sup_le ?_ ?_
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hT _
      · rintro _ ⟨w, hw, rfl⟩
        show d₁ (β₁ w) = 0
        rw [hβ₁, show d 0 w = 0 from hw, map_zero]
  have hker1 : LinearMap.ker (d 0) = LinearMap.range (d 1) := hex 0 (by omega)
  rw [hK]
  refine (Submodule.fg_span (Set.finite_range _)).sup ?_
  exact (hker1 ▸ fg_range_freeMod (d 1)).map β₁

/-- **The finite-kernel criterion.** For a generating tuple `x : Fin n → G`,
`G` has type `FP₂` iff the kernel of the generator boundary `ℤ[G]^n → ℤ[G]`,
`eᵢ ↦ [xᵢ] - 1`, is a finitely generated `ℤ[G]`-module. -/
theorem isFP_two_iff_fg_ker_genBoundary {n : ℕ} (x : Fin n → G)
    (hx : Subgroup.closure (Set.range x) = ⊤) :
    IsFP 2 G ↔ (LinearMap.ker (genBoundary x)).FG :=
  ⟨fg_ker_genBoundary_of_isFP_two x hx, isFP_two_of_fg_ker_genBoundary x hx⟩

end TheoremA
