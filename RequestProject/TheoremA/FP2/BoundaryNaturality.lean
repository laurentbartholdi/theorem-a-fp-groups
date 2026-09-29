module

public import RequestProject.TheoremA.FP2.WordBoundary

/-!
# Naturality of word boundaries under a substitution

Let `H`, `K` be arbitrary groups, `x : Fin n → H`, `y : Fin m → K` arbitrary tuples (no
generation hypothesis), `f : H →* K` and `θ : FreeGroup (Fin n) →* FreeGroup (Fin m)` with the
compatibility

  `f (x i) = FreeGroup.lift y (θ (of i))` for every `i`.                         (B)

* `coeffMap f : ℤ[H] →+* ℤ[K]` is Mathlib's `MonoidAlgebra.mapDomainRingHom ℤ f`,
  with `coeffMap_of : coeffMap f [h] = [f h]`.  No injectivity of `f` is needed.
* `boundarySubst f y θ : ℤ[H]^n →ₛₗ[coeffMap f] ℤ[K]^m` is the semilinear map
  `v ↦ ∑ i, f_ℤ(v i) • D_y(θ(a_i))` (left scalar multiplication).
* `wordBoundary_substitution`: `L (D_x u) = D_y (θ u)` for every word `u`.
* `boundarySubstitution_mem_span`:
  `z ∈ span_{ℤ[H]} (D_x '' T) → L z ∈ span_{ℤ[K]} (D_y '' (θ '' T))`.
-/

@[expose] public section

namespace TheoremA

universe u v

variable {H : Type u} {K : Type v} [Group H] [Group K]

/-- The coefficient ring map `ℤ[H] →+* ℤ[K]` induced by a group homomorphism. -/
noncomputable abbrev coeffMap (f : H →* K) : ZG H →+* ZG K :=
  MonoidAlgebra.mapDomainRingHom ℤ f

@[simp] theorem coeffMap_of (f : H →* K) (h : H) :
    coeffMap f (MonoidAlgebra.of ℤ H h) = MonoidAlgebra.of ℤ K (f h) := by
  simp [coeffMap, MonoidAlgebra.of_apply]

variable {n m : ℕ}

/-- **The boundary substitution map** `L(v) = ∑ i, f_ℤ(v i) • D_y(θ(a_i))`, semilinear over
`coeffMap f`. -/
noncomputable def boundarySubst (f : H →* K) (y : Fin m → K)
    (θ : FreeGroup (Fin n) →* FreeGroup (Fin m)) :
    FreeMod H n →ₛₗ[coeffMap f] FreeMod K m where
  toFun v := ∑ i, coeffMap f (v i) • wordBoundary y (θ (FreeGroup.of i))
  map_add' v w := by
    simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

theorem boundarySubst_apply (f : H →* K) (y : Fin m → K)
    (θ : FreeGroup (Fin n) →* FreeGroup (Fin m)) (v : FreeMod H n) :
    boundarySubst f y θ v = ∑ i, coeffMap f (v i) • wordBoundary y (θ (FreeGroup.of i)) := rfl

/-- Semilinearity: `L(a • v) = f_ℤ(a) • L(v)`. -/
theorem boundarySubst_smul (f : H →* K) (y : Fin m → K)
    (θ : FreeGroup (Fin n) →* FreeGroup (Fin m)) (a : ZG H) (v : FreeMod H n) :
    boundarySubst f y θ (a • v) = coeffMap f a • boundarySubst f y θ v :=
  (boundarySubst f y θ).map_smulₛₗ a v

@[simp] theorem boundarySubst_stdBasis (f : H →* K) (y : Fin m → K)
    (θ : FreeGroup (Fin n) →* FreeGroup (Fin m)) (i : Fin n) :
    boundarySubst f y θ (stdBasis H i) = wordBoundary y (θ (FreeGroup.of i)) := by
  classical
  rw [boundarySubst_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [stdBasis, hji]
  · simp

/-- Compatibility (B) on generators gives `f ∘ q_x = q_y ∘ θ` on all words. -/
theorem lift_comp_of_compat (f : H →* K) (x : Fin n → H) (y : Fin m → K)
    (θ : FreeGroup (Fin n) →* FreeGroup (Fin m))
    (hB : ∀ i, f (x i) = FreeGroup.lift y (θ (FreeGroup.of i))) (u : FreeGroup (Fin n)) :
    f (FreeGroup.lift x u) = FreeGroup.lift y (θ u) := by
  have : f.comp (FreeGroup.lift x) = (FreeGroup.lift y).comp θ := by
    ext i; simpa using hB i
  exact DFunLike.congr_fun this u

/-- **Chain rule.** Under (B), `L(D_x u) = D_y(θ u)` for every word `u`. -/
theorem wordBoundary_substitution (f : H →* K) (x : Fin n → H) (y : Fin m → K)
    (θ : FreeGroup (Fin n) →* FreeGroup (Fin m))
    (hB : ∀ i, f (x i) = FreeGroup.lift y (θ (FreeGroup.of i))) (u : FreeGroup (Fin n)) :
    boundarySubst f y θ (wordBoundary x u) = wordBoundary y (θ u) := by
  induction u using FreeGroup.induction_on with
  | C1 => simp
  | of i => simp
  | inv_of i _ =>
    rw [wordBoundary_of_inv, map_neg, boundarySubst_smul, boundarySubst_stdBasis, coeffMap_of,
      f.map_inv, hB, θ.map_inv, wordBoundary_inv]
  | mul a b ha hb =>
    rw [wordBoundary_mul, map_add, boundarySubst_smul, ha, hb, coeffMap_of,
      lift_comp_of_compat f x y θ hB, map_mul, wordBoundary_mul]

/-- **Span transport.** Under (B), if `z` lies in the `ℤ[H]`-span of `D_x '' T`, then `L z` lies
in the `ℤ[K]`-span of `D_y '' (θ '' T)`. -/
theorem boundarySubstitution_mem_span (f : H →* K) (x : Fin n → H) (y : Fin m → K)
    (θ : FreeGroup (Fin n) →* FreeGroup (Fin m))
    (hB : ∀ i, f (x i) = FreeGroup.lift y (θ (FreeGroup.of i)))
    (T : Set (FreeGroup (Fin n))) {z : FreeMod H n}
    (hz : z ∈ Submodule.span (ZG H) (wordBoundary x '' T)) :
    boundarySubst f y θ z ∈ Submodule.span (ZG K) (wordBoundary y '' (θ '' T)) := by
  have hle : Submodule.span (ZG H) (wordBoundary x '' T) ≤
      (Submodule.span (ZG K) (wordBoundary y '' (θ '' T))).comap (boundarySubst f y θ) := by
    rw [Submodule.span_le]
    rintro _ ⟨r, hr, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, wordBoundary_substitution f x y θ hB]
    exact Submodule.subset_span ⟨θ r, ⟨r, hr, rfl⟩, rfl⟩
  exact hle hz

/-- **Span transport of words.** Under (B), if `D_x r ∈ span (D_x '' T)`, then
`D_y (θ r) ∈ span (D_y '' (θ '' T))`. -/
theorem wordBoundary_subst_mem_span (f : H →* K) (x : Fin n → H) (y : Fin m → K)
    (θ : FreeGroup (Fin n) →* FreeGroup (Fin m))
    (hB : ∀ i, f (x i) = FreeGroup.lift y (θ (FreeGroup.of i)))
    (T : Set (FreeGroup (Fin n))) {r : FreeGroup (Fin n)}
    (hr : wordBoundary x r ∈ Submodule.span (ZG H) (wordBoundary x '' T)) :
    wordBoundary y (θ r) ∈ Submodule.span (ZG K) (wordBoundary y '' (θ '' T)) := by
  rw [← wordBoundary_substitution f x y θ hB]
  exact boundarySubstitution_mem_span f x y θ hB T hr

end TheoremA
