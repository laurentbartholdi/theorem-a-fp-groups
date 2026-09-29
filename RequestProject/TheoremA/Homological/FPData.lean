module

public import RequestProject.TheoremA.Homological.Setup

/-!
# Bookkeeping for `IsFP`: transport along linear equivalences and adding a top term
-/

@[expose] public section

namespace TheoremA

universe u v

/-- The data witnessing `IsFP n G`. -/
structure FPData (G : Type u) [Group G] (n : ℕ) where
  c : ℕ → ℕ
  d : ∀ i, FreeMod G (c (i + 1)) →ₗ[ZG G] FreeMod G (c i)
  ε : FreeMod G (c 0) →+ ℤ
  ε_inv : ∀ (g : G) (x : FreeMod G (c 0)), ε (MonoidAlgebra.of ℤ G g • x) = ε x
  ε_surj : Function.Surjective ε
  exact0 : 0 < n → ε.ker = (LinearMap.range (d 0)).toAddSubgroup
  exact : ∀ i, i + 1 < n → LinearMap.ker (d i) = LinearMap.range (d (i + 1))

variable {G : Type u} [Group G]

theorem FPData.isFP {n : ℕ} (D : FPData G n) : IsFP n G :=
  ⟨D.c, D.d, D.ε, D.ε_inv, D.ε_surj, D.exact0, D.exact⟩

/-- Transport a partial resolution by modules `X i ≅ ℤ[G]^{c i}` to coordinates. -/
noncomputable def FPData.ofEquiv {n : ℕ} (X : ℕ → Type v) [∀ i, AddCommGroup (X i)]
    [∀ i, Module (ZG G) (X i)] (c : ℕ → ℕ) (e : ∀ i, X i ≃ₗ[ZG G] FreeMod G (c i))
    (D : ∀ i, X (i + 1) →ₗ[ZG G] X i) (ε : X 0 →+ ℤ)
    (hinv : ∀ (g : G) (x : X 0), ε (MonoidAlgebra.of ℤ G g • x) = ε x)
    (hsurj : Function.Surjective ε)
    (h0 : 0 < n → ∀ x, ε x = 0 ↔ x ∈ LinearMap.range (D 0))
    (hex : ∀ i, i + 1 < n → ∀ x, D i x = 0 ↔ x ∈ LinearMap.range (D (i + 1))) :
    FPData G n where
  c := c
  d i := (e i).toLinearMap ∘ₗ D i ∘ₗ (e (i + 1)).symm.toLinearMap
  ε := ε.comp (e 0).symm.toLinearMap.toAddMonoidHom
  ε_inv g x := by
    show ε ((e 0).symm (MonoidAlgebra.of ℤ G g • x)) = ε ((e 0).symm x)
    rw [LinearEquiv.map_smul, hinv]
  ε_surj x := by
    obtain ⟨y, rfl⟩ := hsurj x
    exact ⟨e 0 y, by simp⟩
  exact0 hn := by
    ext x
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
      Submodule.mem_toAddSubgroup, LinearMap.mem_range, LinearMap.coe_comp,
      LinearEquiv.coe_coe]
    rw [h0 hn]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨e 1 y, by simp [hy]⟩
    · rintro ⟨y, hy⟩
      refine ⟨(e 1).symm y, ?_⟩
      rw [← hy]; simp
  exact i hi := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.mem_range, LinearEquiv.map_eq_zero_iff]
    rw [hex i hi]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨e (i + 2) y, by simp [hy]⟩
    · rintro ⟨y, hy⟩
      refine ⟨(e (i + 2)).symm y, ?_⟩
      rw [← hy]; simp

/-- Adding a top term: if `g : ℤ[G]^q → ℤ[G]^{c (n+1)}` has image `ker d_n`, then `G` has type
`FP_{n+2}`. -/
theorem FPData.isFP_succ {n : ℕ} (D : FPData G (n + 1)) (q : ℕ)
    (g : FreeMod G q →ₗ[ZG G] FreeMod G (D.c (n + 1)))
    (hg : LinearMap.range g = LinearMap.ker (D.d n)) : IsFP (n + 2) G := by
  classical
  let c' : ℕ → ℕ := fun i => if i ≤ n + 1 then D.c i else q
  have hc : ∀ i, i ≤ n + 1 → c' i = D.c i := fun i hi => if_pos hi
  have hq : c' (n + 2) = q := if_neg (by omega)
  let e : ∀ i, i ≤ n + 1 → FreeMod G (c' i) ≃ₗ[ZG G] FreeMod G (D.c i) := fun i hi =>
    LinearEquiv.funCongrLeft (ZG G) (ZG G) (finCongr (hc i hi).symm)
  let f : FreeMod G (c' (n + 2)) ≃ₗ[ZG G] FreeMod G q :=
    LinearEquiv.funCongrLeft (ZG G) (ZG G) (finCongr hq.symm)
  let d' : ∀ i, FreeMod G (c' (i + 1)) →ₗ[ZG G] FreeMod G (c' i) := fun i =>
    if h : i + 1 ≤ n + 1 then
      (e i (by omega)).symm.toLinearMap ∘ₗ D.d i ∘ₗ (e (i + 1) h).toLinearMap
    else if h' : i = n + 1 then
      h' ▸ ((e (n + 1) le_rfl).symm.toLinearMap ∘ₗ g ∘ₗ f.toLinearMap)
    else 0
  have hd' : ∀ i (h : i + 1 ≤ n + 1), d' i =
      (e i (by omega)).symm.toLinearMap ∘ₗ D.d i ∘ₗ (e (i + 1) h).toLinearMap := by
    intro i h; simp only [d', dif_pos h]
  have hdtop : d' (n + 1) = (e (n + 1) le_rfl).symm.toLinearMap ∘ₗ g ∘ₗ f.toLinearMap := by
    simp only [d', dif_neg (show ¬ (n + 1 + 1 ≤ n + 1) by omega)]
    rw [dif_pos trivial]
  refine ⟨c', d', D.ε.comp (e 0 (by omega)).toLinearMap.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro g' x
    show D.ε (e 0 (by omega) (MonoidAlgebra.of ℤ G g' • x)) = D.ε (e 0 (by omega) x)
    rw [LinearEquiv.map_smul, D.ε_inv]
  · intro x
    obtain ⟨y, rfl⟩ := D.ε_surj x
    exact ⟨(e 0 (by omega)).symm y, by simp⟩
  · intro _
    ext x
    show D.ε (e 0 (by omega) x) = 0 ↔ x ∈ LinearMap.range (d' 0)
    rw [LinearMap.mem_range, hd' 0 (by omega)]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    have h0 := D.exact0 (by omega)
    have : D.ε ((e 0 (by omega)) x) = 0 ↔ (e 0 (by omega)) x ∈ LinearMap.range (D.d 0) := by
      rw [← AddMonoidHom.mem_ker, h0]; rfl
    rw [this]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨(e 1 (by omega)).symm y, by simp [hy]⟩
    · rintro ⟨y, hy⟩
      exact ⟨e 1 (by omega) y, by rw [← hy]; simp⟩
  · intro i hi
    ext x
    by_cases hin : i + 1 ≤ n
    · -- both maps come from `D`
      rw [LinearMap.mem_ker, LinearMap.mem_range, hd' i (by omega), hd' (i + 1) (by omega)]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.map_eq_zero_iff]
      have := D.exact i (by omega)
      have hx : D.d i ((e (i + 1) (by omega)) x) = 0 ↔
          (e (i + 1) (by omega)) x ∈ LinearMap.range (D.d (i + 1)) := by
        rw [← LinearMap.mem_ker, this]
      rw [hx]
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨(e (i + 2) (by omega)).symm y, by
          apply (e (i + 1) (by omega)).injective; simp [hy]⟩
      · rintro ⟨y, hy⟩
        exact ⟨e (i + 2) (by omega) y, by rw [← hy]; simp⟩
    · obtain rfl : i = n := by omega
      rw [LinearMap.mem_ker, LinearMap.mem_range, hd' i (by omega), hdtop]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.map_eq_zero_iff]
      have hx : D.d i ((e (i + 1) (by omega)) x) = 0 ↔
          (e (i + 1) (by omega)) x ∈ LinearMap.range g := by
        rw [← LinearMap.mem_ker, hg]
      rw [hx]
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨f.symm y, by apply (e (i + 1) le_rfl).injective; simp [hy]⟩
      · rintro ⟨y, hy⟩
        exact ⟨f y, by rw [← hy]; simp⟩

end TheoremA
