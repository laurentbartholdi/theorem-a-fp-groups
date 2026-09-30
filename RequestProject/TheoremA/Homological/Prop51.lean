module

public import RequestProject.TheoremA.Homological.TMaps
public import RequestProject.TheoremA.Homological.FPData

/-!
# Proposition 5.1

The mapping-cone complex `C_0 = P_0`, `C_j = P_j ⊕ P_{j-1}` with differentials (5.4)–(5.5),
together with the top term (5.7)–(5.8), is a partial free resolution of `ℤ` over `ℤ[E]` of finite
type through degree `m + 1`.
-/

@[expose] public section

namespace TheoremA

universe u

open MonoidAlgebra

/-- Shifted ranks: `cm c 0 = 0`, `cm c (j+1) = c j`. -/
@[reducible] def cm (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => c j

variable {B : Type u} [Group B] (φ : B →* B) (hφ : Function.Injective φ) {k : ℕ} (R : Res B k)
  (Φ : ∀ i, FreeMod B (R.c i) →+ FreeMod B (R.c i))

/-- The cone terms `C_j = P_j × P_{j-1}` (with `P_{-1} = 0`). -/
abbrev ConeX (j : ℕ) : Type u :=
  FreeMod (ascHNN φ hφ) (R.c j) × FreeMod (ascHNN φ hφ) (cm R.c j)

/-- The differential on the second summand: `-d_{j-1}`. -/
noncomputable def dQ : ∀ j, FreeMod (ascHNN φ hφ) (cm R.c (j + 1)) →ₗ[ZG (ascHNN φ hφ)]
    FreeMod (ascHNN φ hφ) (cm R.c j)
  | 0 => 0
  | i + 1 => indMap (ofE φ hφ) (R.d i)

/-- The cone differential `D(x, y) = (d x + (1 - T) y, - d y)` of (5.4)–(5.5). -/
noncomputable def coneD (j : ℕ) : ConeX φ hφ R (j + 1) →ₗ[ZG (ascHNN φ hφ)] ConeX φ hφ R j :=
  LinearMap.prod ((indMap (ofE φ hφ) (R.d j)).coprod (LinearMap.id - Tmap φ hφ R Φ j))
    (-((dQ φ hφ R j).comp (LinearMap.snd _ _ _)))

theorem coneD_apply (j : ℕ) (x : FreeMod (ascHNN φ hφ) (R.c (j + 1)))
    (y : FreeMod (ascHNN φ hφ) (R.c j)) :
    coneD φ hφ R Φ j (x, y) =
      (indMap (ofE φ hφ) (R.d j) x + (y - Tmap φ hφ R Φ j y), -(dQ φ hφ R j y)) := rfl

/-- The top differential, with `u_a = (ι n_a, 0)` and `v_b = ((1 - T) e_b, -d e_b)` (5.7)–(5.8). -/
noncomputable def coneTop {q : ℕ} (n : Fin q → FreeMod B (R.c (k + 1))) :
    FreeMod (ascHNN φ hφ) q × FreeMod (ascHNN φ hφ) (R.c (k + 1)) →ₗ[ZG (ascHNN φ hφ)]
      ConeX φ hφ R (k + 1) :=
  LinearMap.prod ((matMap fun a => ρV (ofE φ hφ) (n a)).coprod
      (LinearMap.id - Tmap φ hφ R Φ (k + 1)))
    (-((indMap (ofE φ hφ) (R.d k)).comp (LinearMap.snd _ _ _)))

theorem coneTop_apply {q : ℕ} (n : Fin q → FreeMod B (R.c (k + 1)))
    (z : FreeMod (ascHNN φ hφ) q) (y : FreeMod (ascHNN φ hφ) (R.c (k + 1))) :
    coneTop φ hφ R Φ n (z, y) =
      (matMap (fun a => ρV (ofE φ hφ) (n a)) z + (y - Tmap φ hφ R Φ (k + 1) y),
        -(indMap (ofE φ hφ) (R.d k) y)) := rfl

/-- The augmentation of the cone. -/
noncomputable def coneε : ConeX φ hφ R 0 →+ ℤ :=
  (εA (ofE φ hφ) R).comp (LinearMap.fst (ZG (ascHNN φ hφ)) _ _).toAddMonoidHom

variable {φ hφ R Φ}

theorem indMap_d_d (i : ℕ) (hi : i < k) (x : FreeMod (ascHNN φ hφ) (R.c (i + 2))) :
    indMap (ofE φ hφ) (R.d i) (indMap (ofE φ hφ) (R.d (i + 1)) x) = 0 := by
  rw [indMap_eq_zero_iff (ofE φ hφ) (ascHNN_of_injective φ hφ)]
  intro q
  rw [compV_indMap, R.d_d i hi]

theorem indMap_exact' (i : ℕ) (hi : i < k) (x : FreeMod (ascHNN φ hφ) (R.c (i + 1)))
    (hx : indMap (ofE φ hφ) (R.d i) x = 0) :
    x ∈ LinearMap.range (indMap (ofE φ hφ) (R.d (i + 1))) := by
  rw [← indMap_exact (ofE φ hφ) (ascHNN_of_injective φ hφ) _ _ (R.exact i hi)]
  exact hx

/-- Exactness at `C_0`. -/
theorem cone_exact0 (hΦ : IsChainLift R φ Φ) (x : ConeX φ hφ R 0) :
    coneε φ hφ R x = 0 ↔ x ∈ LinearMap.range (coneD φ hφ R Φ 0) := by
  obtain ⟨x, y⟩ := x
  have hy : y = 0 := funext fun j => Fin.elim0 j
  subst hy
  constructor
  · intro hx
    have hx' : augM (ofE φ hφ) (εM (ofE φ hφ) R x) = 0 := hx
    obtain ⟨w, hw⟩ := exists_oneSubTM φ hφ _ hx'
    obtain ⟨y', rfl⟩ := εM_surjective (ofE φ hφ) (ascHNN_of_injective φ hφ) R w
    have : εM (ofE φ hφ) R (x - (y' - Tmap φ hφ R Φ 0 y')) = 0 := by
      rw [map_sub, map_sub, εM_Tmap hΦ, hw, sub_self]
    obtain ⟨x', hx'⟩ := ker_εM (ofE φ hφ) (ascHNN_of_injective φ hφ) R _ this
    refine ⟨(x', y'), ?_⟩
    rw [coneD_apply]
    refine Prod.ext ?_ (funext fun j => Fin.elim0 j)
    simp only
    rw [hx']; abel
  · rintro ⟨⟨x', y'⟩, h⟩
    rw [coneD_apply] at h
    have h1 := congrArg Prod.fst h
    simp only at h1
    show εA (ofE φ hφ) R x = 0
    rw [← h1, map_add, map_sub, εA_Tmap hΦ, sub_self, add_zero]
    show augM _ (εM _ R _) = 0
    rw [indMap_d0_εM (ofE φ hφ) (ascHNN_of_injective φ hφ), map_zero]

theorem coneD_coneD (hΦ : IsChainLift R φ Φ) (i : ℕ) (hi : i < k)
    (x : ConeX φ hφ R (i + 2)) : coneD φ hφ R Φ i (coneD φ hφ R Φ (i + 1) x) = 0 := by
  obtain ⟨x, y⟩ := x
  rw [coneD_apply, coneD_apply]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_zero]
    rw [map_add, map_sub, indMap_d_d i hi, Tmap_comm hΦ i (by omega)]
    cases i with
    | zero =>
      simp only [dQ, map_neg]
      funext j
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply]
      abel
    | succ i =>
      simp only [dQ, map_neg]
      funext j
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply]
      abel
  · simp only [Prod.snd_zero]
    cases i with
    | zero => simp [dQ]
    | succ i =>
      simp only [dQ, map_neg, neg_neg]
      exact indMap_d_d i (by omega) y

/-- Exactness at `C_{i+1}` for `i < k`. -/
theorem cone_exact (hΦ : IsChainLift R φ Φ) (i : ℕ) (hi : i < k) (x : ConeX φ hφ R (i + 1)) :
    coneD φ hφ R Φ i x = 0 ↔ x ∈ LinearMap.range (coneD φ hφ R Φ (i + 1)) := by
  constructor
  · obtain ⟨x, y⟩ := x
    intro h
    rw [coneD_apply] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_zero, Prod.snd_zero, neg_eq_zero] at h1 h2
    -- `y` is a boundary
    obtain ⟨z, rfl⟩ : y ∈ LinearMap.range (indMap (ofE φ hφ) (R.d i)) := by
      cases i with
      | zero =>
        apply ker_εM (ofE φ hφ) (ascHNN_of_injective φ hφ) R
        apply oneSubTM_injective φ hφ
        have := congrArg (εM (ofE φ hφ) R) h1
        rw [map_add, map_sub, εM_Tmap hΦ, map_zero,
          indMap_d0_εM (ofE φ hφ) (ascHNN_of_injective φ hφ), zero_add] at this
        exact this
      | succ i' =>
        exact indMap_exact' i' (by omega) y h2
    have hw : x + (z - Tmap φ hφ R Φ (i + 1) z) ∈
        LinearMap.range (indMap (ofE φ hφ) (R.d (i + 1))) := by
      apply indMap_exact' i hi
      rw [map_add, map_sub, Tmap_comm hΦ i (by omega)]
      exact h1
    obtain ⟨w, hw⟩ := hw
    refine ⟨(w, -z), ?_⟩
    rw [coneD_apply, hw]
    refine Prod.ext ?_ ?_
    · simp only [map_neg]; abel
    · simp only [dQ, map_neg, neg_neg]
  · rintro ⟨w, rfl⟩
    exact coneD_coneD hΦ i hi w

/-- The top differential lands in the cycles and maps onto them. -/
theorem cone_top (hΦ : IsChainLift R φ Φ) (hk : 1 ≤ k) {q : ℕ}
    (n : Fin q → FreeMod B (R.c (k + 1)))
    (hnS : ∀ a, n a ∈ R.S)
    (hΦS : ∀ s ∈ R.S, Φ (k + 1) s ∈ Submodule.span (ZG B) (Set.range n))
    (x : ConeX φ hφ R (k + 1)) :
    coneD φ hφ R Φ k x = 0 ↔ x ∈ LinearMap.range (coneTop φ hφ R Φ n) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  constructor
  · obtain ⟨x, y⟩ := x
    intro h
    rw [coneD_apply] at h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_zero, Prod.snd_zero, neg_eq_zero] at h1 h2
    obtain ⟨z, rfl⟩ := indMap_exact' k' (by omega) y h2
    -- `x + (1 - T) z` is a cycle, hence in the span of `ι(S)`
    have hc : indMap (ofE φ hφ) (R.d (k' + 1)) (x + (z - Tmap φ hφ R Φ (k' + 2) z)) = 0 := by
      rw [map_add, map_sub, Tmap_comm hΦ (k' + 1) le_rfl]
      exact h1
    have hspan := mem_span_of_compV (ofE φ hφ) (ascHNN_of_injective φ hφ) R.S _
      (fun q => ((indMap_eq_zero_iff (ofE φ hφ) (ascHNN_of_injective φ hφ) _ _).1 hc q))
    -- elements `(v, 0)` with `v` in that span are in the range of the top map
    have key : Submodule.span (ZG (ascHNN φ hφ)) (ρV (ofE φ hφ) '' (R.S : Set _)) ≤
        (LinearMap.range (coneTop φ hφ R Φ n)).comap
          (LinearMap.inl (ZG (ascHNN φ hφ)) _ (FreeMod (ascHNN φ hφ) (R.c (k' + 1)))) := by
      rw [Submodule.span_le]
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZG B)).1 (hΦS s hs)
      refine ⟨(fun a => MonoidAlgebra.single (sE φ hφ) (1 : ℤ) * ρ (ofE φ hφ) (l a),
        ρV (ofE φ hφ) s), ?_⟩
      rw [coneTop_apply]
      refine Prod.ext ?_ ?_
      · simp only [LinearMap.inl_apply]
        rw [Tmap_ρV hΦ, ← hl]
        simp only [matMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum, ρV_smul, Finset.smul_sum,
          smul_smul]
        abel
      · have : R.d (k' + 1) s = 0 := hs
        simp [indMap_ρV, this]
    obtain ⟨⟨z1, y1⟩, hz1⟩ := key hspan
    refine ⟨(z1, y1 - z), ?_⟩
    have := congrArg Prod.fst hz1
    have h' := congrArg Prod.snd hz1
    change matMap (fun a => ρV (ofE φ hφ) (n a)) z1 +
      (y1 - Tmap φ hφ R Φ (k' + 2) y1) = x + (z - Tmap φ hφ R Φ (k' + 2) z) at this
    change -(indMap (ofE φ hφ) (R.d (k' + 1)) y1) = 0 at h'
    change (matMap (fun a => ρV (ofE φ hφ) (n a)) z1 +
      ((y1 - z) - Tmap φ hφ R Φ (k' + 2) (y1 - z)),
      -(indMap (ofE φ hφ) (R.d (k' + 1)) (y1 - z))) =
      (x, indMap (ofE φ hφ) (R.d (k' + 1)) z)
    refine Prod.ext ?_ ?_
    · simp only [map_sub]
      rw [show matMap (fun a => ρV (ofE φ hφ) (n a)) z1 = x + (z - Tmap φ hφ R Φ (k' + 2) z)
        - (y1 - Tmap φ hφ R Φ (k' + 2) y1) by rw [← this]; abel]
      abel
    · simp only [map_sub, neg_sub]
      rw [neg_eq_zero] at h'
      rw [h', sub_zero]
  · rintro ⟨⟨z, y⟩, rfl⟩
    rw [coneTop_apply, coneD_apply]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_zero]
      have hn0 : indMap (ofE φ hφ) (R.d (k' + 1)) (matMap (fun a => ρV (ofE φ hφ) (n a)) z) = 0 := by
        simp only [matMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, indMap_ρV]
        refine Finset.sum_eq_zero fun a _ => ?_
        have : R.d (k' + 1) (n a) = 0 := hnS a
        simp [this]
      rw [map_add, map_sub, hn0, Tmap_comm hΦ (k' + 1) le_rfl]
      simp only [map_neg]; abel
    · simp only [Prod.snd_zero, dQ, map_neg, neg_neg]
      exact indMap_d_d k' (by omega) y

end TheoremA

namespace TheoremA

universe u'

/-- `ℤ[G]^a × ℤ[G]^b ≃ ℤ[G]^{a+b}`. -/
noncomputable def prodEquiv (G : Type*) [Group G] (a b : ℕ) :
    (FreeMod G a × FreeMod G b) ≃ₗ[ZG G] FreeMod G (a + b) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) (ZG G) (ZG G)).symm ≪≫ₗ
    LinearEquiv.funCongrLeft (ZG G) (ZG G) finSumFinEquiv.symm

/-- **Proposition 5.1.** -/
theorem prop51 : Prop51.{u'} := by
  intro k hk B _ R φ hφ Φ hΦ N hNfg hNS hSN
  obtain ⟨q, n, hn⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hNfg
  have hnS : ∀ a, n a ∈ R.S := fun a => hNS (hn ▸ Submodule.subset_span ⟨a, rfl⟩)
  have hΦS : ∀ s ∈ R.S, Φ (k + 1) s ∈ Submodule.span (ZG B) (Set.range n) :=
    fun s hs => hn.symm ▸ hSN s hs
  have hsurj : Function.Surjective (coneε φ hφ R) := by
    intro z
    obtain ⟨x, hx⟩ := εM_surjective (ofE φ hφ) (ascHNN_of_injective φ hφ) R
      (Finsupp.single (cosetOf (ofE φ hφ) 1) z)
    refine ⟨(x, 0), ?_⟩
    show augM _ (εM _ R x) = z
    rw [hx, augM_single]
  let FD : FPData (ascHNN φ hφ) (k + 1) :=
    FPData.ofEquiv (ConeX φ hφ R) (fun j => R.c j + cm R.c j) (fun j => prodEquiv _ _ _)
      (coneD φ hφ R Φ) (coneε φ hφ R)
      (fun g x => εA_inv (ofE φ hφ) R g x.1) hsurj
      (fun _ x => cone_exact0 hΦ x) (fun i hi x => cone_exact hΦ i (by omega) x)
  refine FD.isFP_succ (q + R.c (k + 1))
    ((prodEquiv _ _ _).toLinearMap ∘ₗ coneTop φ hφ R Φ n ∘ₗ (prodEquiv _ _ _).symm.toLinearMap) ?_
  ext y
  simp only [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, FD, FPData.ofEquiv, LinearEquiv.map_eq_zero_iff]
  rw [cone_top hΦ hk n hnS hΦS]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨(prodEquiv _ _ _).symm w, by simp⟩
  · rintro ⟨w, hw⟩
    refine ⟨prodEquiv _ _ _ w, ?_⟩
    simp [hw]

end TheoremA
