module

public import RequestProject.TheoremA.Groups.HNNPres

/-!
# Direct products and amalgamated free products: presentations, `C_R`, `FP₂`

Both are finite relative presentations over the free product `B₀ ∗ B₁` (no new generators):

* the direct product `B₀ × B₁` adds the commutators of the displayed generators of the two
  factors (`prodPresEquiv`, `ClassCR.prod`, `isFP_two_prod`);
* the amalgam `B₀ ∗_D B₁` over a finitely generated `D` (Mathlib's `Monoid.PushoutI` over
  `Bool`, `Amalg f₀ f₁`) adds, for a finite generating tuple of `D`, the equality of the two
  image words (`amalgPresEquiv`, `ClassCR.amalg`, `isFP_two_amalg`).  `D` need not be finitely
  presented.

Structural facts for amalgams of injective maps: `Amalg.inl_injective`, `Amalg.inr_injective`,
`Amalg.base_injective`, `Amalg.range_inl_inf_range_inr`.
-/

@[expose] public section

namespace TheoremA.RelPres

open PresentedGroup

universe u v

/-! ### Direct products -/

section Prod

variable {B₀ : Type u} [Group B₀] {B₁ : Type u} [Group B₁] {n₀ n₁ : ℕ}
  {S₀ : Set (FreeGroup (Fin n₀))} {S₁ : Set (FreeGroup (Fin n₁))}
  (ψ₀ : PresentedGroup S₀ ≃* B₀) (ψ₁ : PresentedGroup S₁ ≃* B₁)

/-- The letter of the `j`-th generator of the left factor in `Fin (n₀ + n₁ + 0)`. -/
def lftL (n₀ n₁ : ℕ) (j : Fin n₀) : Fin (n₀ + n₁ + 0) := Fin.castAdd 0 (Fin.castAdd n₁ j)

/-- The letter of the `j`-th generator of the right factor in `Fin (n₀ + n₁ + 0)`. -/
def rgtL (n₀ n₁ : ℕ) (j : Fin n₁) : Fin (n₀ + n₁ + 0) := Fin.castAdd 0 (Fin.natAdd n₀ j)

/-- The commutator relators. -/
def prodRelators (n₀ n₁ : ℕ) : List (RawWord (Fin (n₀ + n₁ + 0))) :=
  (List.finRange n₀).flatMap fun j₀ => (List.finRange n₁).map fun j₁ =>
    commRel (lftL n₀ n₁ j₀) (rgtL n₀ n₁ j₁)

/-- The comparison map `B₀ ∗ B₁ → B₀ × B₁`. -/
def coprodToProd : Monoid.Coprod B₀ B₁ →* B₀ × B₁ :=
  Monoid.Coprod.lift (MonoidHom.inl B₀ B₁) (MonoidHom.inr B₀ B₁)

theorem coprodToProd_surjective : Function.Surjective (coprodToProd (B₀ := B₀) (B₁ := B₁)) := by
  rintro ⟨x, y⟩
  exact ⟨Monoid.Coprod.inl x * Monoid.Coprod.inr y, by simp [coprodToProd]⟩

/-- The presented group. -/
abbrev ProdPres := PresentedGroup (relExt (coprodRels S₀ S₁) 0 (prodRelators n₀ n₁))

/-- The base map from the free product. -/
noncomputable def prodBase : Monoid.Coprod B₀ B₁ →* ProdPres (S₀ := S₀) (S₁ := S₁) :=
  relBase (coprodPresEquiv ψ₀ ψ₁) 0 (prodRelators n₀ n₁)

theorem prodBase_inl_gen (j : Fin n₀) :
    prodBase ψ₀ ψ₁ (Monoid.Coprod.inl (ψ₀ (of j))) = of (lftL n₀ n₁ j) := by
  rw [← coprodPresEquiv_of_castAdd ψ₀ ψ₁ j, prodBase, relBase_gen]; rfl

theorem prodBase_inr_gen (j : Fin n₁) :
    prodBase ψ₀ ψ₁ (Monoid.Coprod.inr (ψ₁ (of j))) = of (rgtL n₀ n₁ j) := by
  rw [← coprodPresEquiv_of_natAdd ψ₀ ψ₁ j, prodBase, relBase_gen]; rfl

theorem prodBase_commute (x : B₀) (y : B₁) :
    Commute (prodBase ψ₀ ψ₁ (Monoid.Coprod.inl x)) (prodBase ψ₀ ψ₁ (Monoid.Coprod.inr y)) := by
  have h0 := closure_range_presentation ψ₀
  have h1 := closure_range_presentation ψ₁
  have key2 : ∀ x ∈ Set.range fun j => ψ₀ (of j), ∀ y : B₁,
      Commute (prodBase ψ₀ ψ₁ (Monoid.Coprod.inl x)) (prodBase ψ₀ ψ₁ (Monoid.Coprod.inr y)) := by
    rintro _ ⟨j₀, rfl⟩ y
    have hy : y ∈ Subgroup.closure (Set.range fun j => ψ₁ (of j)) := h1 ▸ Subgroup.mem_top y
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j₁, rfl⟩ := hy
      rw [prodBase_inl_gen, prodBase_inr_gen]
      have hmem : (commRel (lftL n₀ n₁ j₀) (rgtL n₀ n₁ j₁)).eval ∈
          relExt (coprodRels S₀ S₁) 0 (prodRelators n₀ n₁) :=
        Or.inr ⟨_, List.mem_flatMap.2 ⟨j₀, List.mem_finRange _,
          List.mem_map.2 ⟨j₁, List.mem_finRange _, rfl⟩⟩, rfl⟩
      have h := PresentedGroup.one_of_mem hmem
      rw [eval_commRel, map_commutatorElement] at h
      exact commutatorElement_eq_one_iff_commute.1 h
    | one => simp only [map_one]; exact Commute.one_right _
    | mul y z _ _ ihy ihz => rw [map_mul, map_mul]; exact ihy.mul_right ihz
    | inv y _ ih => rw [map_inv, map_inv]; exact ih.inv_right
  have hx : x ∈ Subgroup.closure (Set.range fun j => ψ₀ (of j)) := h0 ▸ Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact key2 x hx y
  | one => simp only [map_one]; exact Commute.one_left _
  | mul x z _ _ ihx ihz => rw [map_mul, map_mul]; exact ihx.mul_left ihz
  | inv x _ ih => rw [map_inv, map_inv]; exact ih.inv_left

/-- Backward map from the actual direct product. -/
noncomputable def prodBwd : B₀ × B₁ →* ProdPres (S₀ := S₀) (S₁ := S₁) :=
  MonoidHom.noncommCoprod ((prodBase ψ₀ ψ₁).comp Monoid.Coprod.inl)
    ((prodBase ψ₀ ψ₁).comp Monoid.Coprod.inr) (prodBase_commute ψ₀ ψ₁)

/-- **Presentation of a direct product.** -/
noncomputable def prodPresEquiv : ProdPres (S₀ := S₀) (S₁ := S₁) ≃* B₀ × B₁ :=
  relPresEquiv (coprodPresEquiv ψ₀ ψ₁) coprodToProd Fin.elim0 (prodRelators n₀ n₁)
    (by
      intro u hu
      simp only [prodRelators, List.mem_flatMap, List.mem_map] at hu
      obtain ⟨j₀, -, j₁, -, rfl⟩ := hu
      rw [eval_commRel, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      simp only [FreeGroup.lift_apply_of, relGens, lftL, rgtL, Fin.append_left,
        coprodPresEquiv_of_castAdd, coprodPresEquiv_of_natAdd, coprodToProd,
        Monoid.Coprod.lift_apply_inl, Monoid.Coprod.lift_apply_inr]
      exact Prod.ext (by simp) (by simp))
    (prodBwd ψ₀ ψ₁)
    (by
      intro x
      have : (prodBwd ψ₀ ψ₁).comp coprodToProd = prodBase ψ₀ ψ₁ := by
        apply Monoid.Coprod.hom_ext
        · ext b; simp [prodBwd, coprodToProd]
        · ext b; simp [prodBwd, coprodToProd]
      exact DFunLike.congr_fun this x)
    (fun l => l.elim0)
    (by
      intro f hf _
      ext p
      · obtain ⟨x, rfl⟩ := coprodToProd_surjective p
        have := DFunLike.congr_fun hf x
        simp only [MonoidHom.comp_apply] at this
        rw [this]; rfl
      · obtain ⟨x, rfl⟩ := coprodToProd_surjective p
        have := DFunLike.congr_fun hf x
        simp only [MonoidHom.comp_apply] at this
        rw [this]; rfl)

end Prod

/-- **`C_R` is closed under direct products** (same oracle). -/
theorem ClassCR.prod {R : Set ℕ} {B₀ B₁ : Type u} [Group B₀] [Group B₁] (h₀ : ClassCR R B₀)
    (h₁ : ClassCR R B₁) : ClassCR R (B₀ × B₁) := by
  obtain ⟨n₀, e₀, he₀, ⟨ψ₀⟩⟩ := h₀
  obtain ⟨n₁, e₁, he₁, ⟨ψ₁⟩⟩ := h₁
  exact classCR_of_relPres' (he₀.coprodEnum he₁) (enumRelators_coprodEnum e₀ e₁) _
    (prodPresEquiv ψ₀ ψ₁)

/-- **`FP₂` is closed under direct products** (for finite-alphabet presentations). -/
theorem isFP_two_prod_of_pres {B₀ B₁ : Type u} [Group B₀] [Group B₁] {n₀ n₁ : ℕ}
    {S₀ : Set (FreeGroup (Fin n₀))} {S₁ : Set (FreeGroup (Fin n₁))}
    (ψ₀ : PresentedGroup S₀ ≃* B₀) (ψ₁ : PresentedGroup S₁ ≃* B₁) (h₀ : IsFP 2 B₀)
    (h₁ : IsFP 2 B₁) : IsFP 2 (B₀ × B₁) :=
  isFP_two_of_relPres (coprodPresEquiv ψ₀ ψ₁) (isFP_two_coprod_of_pres ψ₀ ψ₁ h₀ h₁) _
    (prodPresEquiv ψ₀ ψ₁)

theorem classCR_isFP_two_prod {R : Set ℕ} {B₀ B₁ : Type u} [Group B₀] [Group B₁]
    (h₀ : ClassCR R B₀) (h₀' : IsFP 2 B₀) (h₁ : ClassCR R B₁) (h₁' : IsFP 2 B₁) :
    ClassCR R (B₀ × B₁) ∧ IsFP 2 (B₀ × B₁) := by
  refine ⟨h₀.prod h₁, ?_⟩
  obtain ⟨n₀, e₀, he₀, ⟨ψ₀⟩⟩ := h₀
  obtain ⟨n₁, e₁, he₁, ⟨ψ₁⟩⟩ := h₁
  exact isFP_two_prod_of_pres ψ₀ ψ₁ h₀' h₁'

theorem classCR_isFP_two_coprod {R : Set ℕ} {B₀ B₁ : Type u} [Group B₀] [Group B₁]
    (h₀ : ClassCR R B₀) (h₀' : IsFP 2 B₀) (h₁ : ClassCR R B₁) (h₁' : IsFP 2 B₁) :
    ClassCR R (Monoid.Coprod B₀ B₁) ∧ IsFP 2 (Monoid.Coprod B₀ B₁) := by
  refine ⟨h₀.coprod h₁, ?_⟩
  obtain ⟨n₀, e₀, he₀, ⟨ψ₀⟩⟩ := h₀
  obtain ⟨n₁, e₁, he₁, ⟨ψ₁⟩⟩ := h₁
  exact isFP_two_coprod_of_pres ψ₀ ψ₁ h₀' h₁'

/-! ### Amalgamated free products of two groups -/

section Amalg

variable {B₀ B₁ : Type u} [Group B₀] [Group B₁] {D : Type v} [Group D]

/-- The two-member family `false ↦ B₀`, `true ↦ B₁`. -/
def amalgFam (B₀ B₁ : Type u) : Bool → Type u
  | true => B₁
  | false => B₀

instance amalgFam.instGroup [Group B₀] [Group B₁] : ∀ b, Group (amalgFam B₀ B₁ b)
  | true => ‹Group B₁›
  | false => ‹Group B₀›

/-- The two maps of the diagram. -/
def amalgHom (f₀ : D →* B₀) (f₁ : D →* B₁) : ∀ b, D →* amalgFam B₀ B₁ b
  | true => f₁
  | false => f₀

/-- **The amalgamated free product** `B₀ ∗_D B₁`. -/
abbrev Amalg (f₀ : D →* B₀) (f₁ : D →* B₁) : Type _ := Monoid.PushoutI (amalgHom f₀ f₁)

variable (f₀ : D →* B₀) (f₁ : D →* B₁)

/-- The left vertex map. -/
def Amalg.inl : B₀ →* Amalg f₀ f₁ := Monoid.PushoutI.of (φ := amalgHom f₀ f₁) false

/-- The right vertex map. -/
def Amalg.inr : B₁ →* Amalg f₀ f₁ := Monoid.PushoutI.of (φ := amalgHom f₀ f₁) true

/-- The edge map. -/
def Amalg.base : D →* Amalg f₀ f₁ := Monoid.PushoutI.base (amalgHom f₀ f₁)

theorem Amalg.inl_comp : (Amalg.inl f₀ f₁).comp f₀ = Amalg.base f₀ f₁ :=
  Monoid.PushoutI.of_comp_eq_base (φ := amalgHom f₀ f₁) false

theorem Amalg.inr_comp : (Amalg.inr f₀ f₁).comp f₁ = Amalg.base f₀ f₁ :=
  Monoid.PushoutI.of_comp_eq_base (φ := amalgHom f₀ f₁) true

theorem Amalg.inl_apply (d : D) : Amalg.inl f₀ f₁ (f₀ d) = Amalg.base f₀ f₁ d :=
  DFunLike.congr_fun (Amalg.inl_comp f₀ f₁) d

theorem Amalg.inr_apply (d : D) : Amalg.inr f₀ f₁ (f₁ d) = Amalg.base f₀ f₁ d :=
  DFunLike.congr_fun (Amalg.inr_comp f₀ f₁) d

/-- The family of maps out of the two vertex groups. -/
def amalgLiftFam {K : Type*} [Group K] (g₀ : B₀ →* K) (g₁ : B₁ →* K) :
    ∀ b, amalgFam B₀ B₁ b →* K
  | true => g₁
  | false => g₀

/-- Universal property. -/
def Amalg.lift {K : Type*} [Group K] (g₀ : B₀ →* K) (g₁ : B₁ →* K)
    (h : g₀.comp f₀ = g₁.comp f₁) : Amalg f₀ f₁ →* K :=
  Monoid.PushoutI.lift (amalgLiftFam g₀ g₁) (g₀.comp f₀)
    (fun b => match b with | true => h.symm | false => rfl)

@[simp] theorem Amalg.lift_inl {K : Type*} [Group K] (g₀ : B₀ →* K) (g₁ : B₁ →* K)
    (h : g₀.comp f₀ = g₁.comp f₁) (x : B₀) :
    Amalg.lift f₀ f₁ g₀ g₁ h (Amalg.inl f₀ f₁ x) = g₀ x :=
  Monoid.PushoutI.lift_of (φ := amalgHom f₀ f₁) (amalgLiftFam g₀ g₁) (g₀.comp f₀) _
    (i := false) x

@[simp] theorem Amalg.lift_inr {K : Type*} [Group K] (g₀ : B₀ →* K) (g₁ : B₁ →* K)
    (h : g₀.comp f₀ = g₁.comp f₁) (x : B₁) :
    Amalg.lift f₀ f₁ g₀ g₁ h (Amalg.inr f₀ f₁ x) = g₁ x :=
  Monoid.PushoutI.lift_of (φ := amalgHom f₀ f₁) (amalgLiftFam g₀ g₁) (g₀.comp f₀) _
    (i := true) x

theorem Amalg.hom_ext {K : Type*} [Group K] {g g' : Amalg f₀ f₁ →* K}
    (h₀ : g.comp (Amalg.inl f₀ f₁) = g'.comp (Amalg.inl f₀ f₁))
    (h₁ : g.comp (Amalg.inr f₀ f₁) = g'.comp (Amalg.inr f₀ f₁)) : g = g' :=
  Monoid.PushoutI.hom_ext_nonempty (fun b => match b with | true => h₁ | false => h₀)

variable {f₀ f₁}

theorem amalgHom_injective (h₀ : Function.Injective f₀) (h₁ : Function.Injective f₁) :
    ∀ b, Function.Injective (amalgHom f₀ f₁ b)
  | true => h₁
  | false => h₀

theorem Amalg.inl_injective (h₀ : Function.Injective f₀) (h₁ : Function.Injective f₁) :
    Function.Injective (Amalg.inl f₀ f₁) :=
  Monoid.PushoutI.of_injective (amalgHom_injective h₀ h₁) false

theorem Amalg.inr_injective (h₀ : Function.Injective f₀) (h₁ : Function.Injective f₁) :
    Function.Injective (Amalg.inr f₀ f₁) :=
  Monoid.PushoutI.of_injective (amalgHom_injective h₀ h₁) true

theorem Amalg.base_injective (h₀ : Function.Injective f₀) (h₁ : Function.Injective f₁) :
    Function.Injective (Amalg.base f₀ f₁) :=
  Monoid.PushoutI.base_injective (amalgHom_injective h₀ h₁)

/-- **The two vertex groups intersect exactly in the edge group.** -/
theorem Amalg.range_inl_inf_range_inr (h₀ : Function.Injective f₀)
    (h₁ : Function.Injective f₁) :
    (Amalg.inl f₀ f₁).range ⊓ (Amalg.inr f₀ f₁).range = (Amalg.base f₀ f₁).range :=
  Monoid.PushoutI.inf_of_range_eq_base_range (amalgHom_injective h₀ h₁) Bool.false_ne_true

end Amalg

section AmalgPres

variable {B₀ B₁ : Type u} [Group B₀] [Group B₁] {D : Type v} [Group D]
  (f₀ : D →* B₀) (f₁ : D →* B₁) {n₀ n₁ : ℕ}
  {S₀ : Set (FreeGroup (Fin n₀))} {S₁ : Set (FreeGroup (Fin n₁))}
  (ψ₀ : PresentedGroup S₀ ≃* B₀) (ψ₁ : PresentedGroup S₁ ≃* B₁) {m : ℕ} (d : Fin m → D)

/-- The comparison map `B₀ ∗ B₁ → B₀ ∗_D B₁`. -/
def coprodToAmalg : Monoid.Coprod B₀ B₁ →* Amalg f₀ f₁ :=
  Monoid.Coprod.lift (Amalg.inl f₀ f₁) (Amalg.inr f₀ f₁)

/-- The extra relator `u_j v_j⁻¹` identifying the two images of `d_j`. -/
noncomputable def amalgRelator (j : Fin m) : RawWord (Fin (n₀ + n₁ + 0)) :=
  RawWord.rename (Fin.castAdd 0) (RawWord.rename (Fin.castAdd n₁) (wordFor ψ₀ (f₀ (d j))) ++
    RawWord.inv (RawWord.rename (Fin.natAdd n₀) (wordFor ψ₁ (f₁ (d j)))))

/-- The finite list of extra relators. -/
noncomputable def amalgRelators : List (RawWord (Fin (n₀ + n₁ + 0))) :=
  List.ofFn (amalgRelator f₀ f₁ ψ₀ ψ₁ d)

/-- The presented group. -/
abbrev AmalgPres := PresentedGroup (relExt (coprodRels S₀ S₁) 0 (amalgRelators f₀ f₁ ψ₀ ψ₁ d))

theorem coprodPres_mk_castAdd (x : FreeGroup (Fin n₀)) :
    coprodPresEquiv ψ₀ ψ₁ (PresentedGroup.mk _ (FreeGroup.map (Fin.castAdd n₁) x)) =
      Monoid.Coprod.inl (ψ₀ (PresentedGroup.mk S₀ x)) := by
  have : ((coprodPresEquiv ψ₀ ψ₁ : _ →* Monoid.Coprod B₀ B₁).comp
      ((PresentedGroup.mk (coprodRels S₀ S₁)).comp (FreeGroup.map (Fin.castAdd n₁)))) =
      (Monoid.Coprod.inl : B₀ →* _).comp ((ψ₀ : _ →* B₀).comp (PresentedGroup.mk S₀)) :=
    FreeGroup.ext_hom _ _ fun j => by
      simpa using coprodPresEquiv_of_castAdd ψ₀ ψ₁ j
  exact DFunLike.congr_fun this x

theorem coprodPres_mk_natAdd (x : FreeGroup (Fin n₁)) :
    coprodPresEquiv ψ₀ ψ₁ (PresentedGroup.mk _ (FreeGroup.map (Fin.natAdd n₀) x)) =
      Monoid.Coprod.inr (ψ₁ (PresentedGroup.mk S₁ x)) := by
  have : ((coprodPresEquiv ψ₀ ψ₁ : _ →* Monoid.Coprod B₀ B₁).comp
      ((PresentedGroup.mk (coprodRels S₀ S₁)).comp (FreeGroup.map (Fin.natAdd n₀)))) =
      (Monoid.Coprod.inr : B₁ →* _).comp ((ψ₁ : _ →* B₁).comp (PresentedGroup.mk S₁)) :=
    FreeGroup.ext_hom _ _ fun j => by
      simpa using coprodPresEquiv_of_natAdd ψ₀ ψ₁ j
  exact DFunLike.congr_fun this x

theorem eval_amalgRelator (j : Fin m) :
    (amalgRelator f₀ f₁ ψ₀ ψ₁ d j).eval = FreeGroup.map (Fin.castAdd 0)
      (FreeGroup.map (Fin.castAdd n₁) (wordFor ψ₀ (f₀ (d j))).eval *
        (FreeGroup.map (Fin.natAdd n₀) (wordFor ψ₁ (f₁ (d j))).eval)⁻¹) := by
  simp only [amalgRelator, RawWord.eval_rename, RawWord.eval_append, RawWord.eval_inv, map_mul,
    map_inv]

/-- The base map from the free product. -/
noncomputable def amalgBase : Monoid.Coprod B₀ B₁ →* AmalgPres f₀ f₁ ψ₀ ψ₁ d :=
  relBase (coprodPresEquiv ψ₀ ψ₁) 0 (amalgRelators f₀ f₁ ψ₀ ψ₁ d)

theorem amalgBase_gen_eq (j : Fin m) :
    amalgBase f₀ f₁ ψ₀ ψ₁ d (Monoid.Coprod.inl (f₀ (d j))) =
      amalgBase f₀ f₁ ψ₀ ψ₁ d (Monoid.Coprod.inr (f₁ (d j))) := by
  have hmem : (amalgRelator f₀ f₁ ψ₀ ψ₁ d j).eval ∈
      relExt (coprodRels S₀ S₁) 0 (amalgRelators f₀ f₁ ψ₀ ψ₁ d) :=
    Or.inr ⟨_, List.mem_ofFn.2 ⟨j, rfl⟩, rfl⟩
  have h := PresentedGroup.one_of_mem hmem
  rw [eval_amalgRelator, ← relBase_mk (coprodPresEquiv ψ₀ ψ₁)] at h
  simp only [map_mul, map_inv, coprodPres_mk_castAdd, coprodPres_mk_natAdd, wordFor_spec] at h
  exact mul_inv_eq_one.1 h

/-- Backward map from the actual amalgam. -/
noncomputable def amalgBwd (hd : Subgroup.closure (Set.range d) = ⊤) :
    Amalg f₀ f₁ →* AmalgPres f₀ f₁ ψ₀ ψ₁ d :=
  Amalg.lift f₀ f₁ ((amalgBase f₀ f₁ ψ₀ ψ₁ d).comp Monoid.Coprod.inl)
    ((amalgBase f₀ f₁ ψ₀ ψ₁ d).comp Monoid.Coprod.inr)
    (MonoidHom.eq_of_eqOn_dense hd (by
      rintro _ ⟨j, rfl⟩
      simp only [MonoidHom.comp_apply]
      exact amalgBase_gen_eq f₀ f₁ ψ₀ ψ₁ d j))

/-- **Presentation of an amalgam over a finitely generated group.** -/
noncomputable def amalgPresEquiv (hd : Subgroup.closure (Set.range d) = ⊤) :
    AmalgPres f₀ f₁ ψ₀ ψ₁ d ≃* Amalg f₀ f₁ :=
  relPresEquiv (coprodPresEquiv ψ₀ ψ₁) (coprodToAmalg f₀ f₁) Fin.elim0
    (amalgRelators f₀ f₁ ψ₀ ψ₁ d)
    (by
      intro u hu
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hu
      rw [eval_amalgRelator, lift_map']
      simp only [relGens, Fin.append_left]
      rw [lift_presentation (coprodPresEquiv ψ₀ ψ₁) (coprodToAmalg f₀ f₁)]
      simp only [map_mul, map_inv, coprodPres_mk_castAdd, coprodPres_mk_natAdd, wordFor_spec,
        coprodToAmalg, Monoid.Coprod.lift_apply_inl, Monoid.Coprod.lift_apply_inr,
        Amalg.inl_apply, Amalg.inr_apply, mul_inv_cancel])
    (amalgBwd f₀ f₁ ψ₀ ψ₁ d hd)
    (by
      intro x
      have : (amalgBwd f₀ f₁ ψ₀ ψ₁ d hd).comp (coprodToAmalg f₀ f₁) =
          amalgBase f₀ f₁ ψ₀ ψ₁ d := by
        apply Monoid.Coprod.hom_ext
        · ext b; simp [amalgBwd, coprodToAmalg]
        · ext b; simp [amalgBwd, coprodToAmalg]
      exact DFunLike.congr_fun this x)
    (fun l => l.elim0)
    (by
      intro f hf _
      apply Amalg.hom_ext
      · ext b
        have := DFunLike.congr_fun hf (Monoid.Coprod.inl b)
        simpa [coprodToAmalg] using this
      · ext b
        have := DFunLike.congr_fun hf (Monoid.Coprod.inr b)
        simpa [coprodToAmalg] using this)

end AmalgPres

/-- **`C_R` is closed under amalgams over finitely generated groups** (same oracle). -/
theorem ClassCR.amalg {R : Set ℕ} {B₀ B₁ : Type u} [Group B₀] [Group B₁] {D : Type v} [Group D]
    (h₀ : ClassCR R B₀) (h₁ : ClassCR R B₁) (hD : Group.FG D) (f₀ : D →* B₀) (f₁ : D →* B₁) :
    ClassCR R (Amalg f₀ f₁) := by
  obtain ⟨n₀, e₀, he₀, ⟨ψ₀⟩⟩ := h₀
  obtain ⟨n₁, e₁, he₁, ⟨ψ₁⟩⟩ := h₁
  obtain ⟨m, d, hd⟩ := exists_fin_generating_tuple hD
  exact classCR_of_relPres' (he₀.coprodEnum he₁) (enumRelators_coprodEnum e₀ e₁) _
    (amalgPresEquiv f₀ f₁ ψ₀ ψ₁ d hd)

/-- **`FP₂` is closed under amalgams over finitely generated groups.** -/
theorem isFP_two_amalg_of_pres {B₀ B₁ : Type u} [Group B₀] [Group B₁] {D : Type v} [Group D]
    {n₀ n₁ : ℕ} {S₀ : Set (FreeGroup (Fin n₀))} {S₁ : Set (FreeGroup (Fin n₁))}
    (ψ₀ : PresentedGroup S₀ ≃* B₀) (ψ₁ : PresentedGroup S₁ ≃* B₁) (h₀ : IsFP 2 B₀)
    (h₁ : IsFP 2 B₁) (hD : Group.FG D) (f₀ : D →* B₀) (f₁ : D →* B₁) :
    IsFP 2 (Amalg f₀ f₁) := by
  obtain ⟨m, d, hd⟩ := exists_fin_generating_tuple hD
  exact isFP_two_of_relPres (coprodPresEquiv ψ₀ ψ₁) (isFP_two_coprod_of_pres ψ₀ ψ₁ h₀ h₁) _
    (amalgPresEquiv f₀ f₁ ψ₀ ψ₁ d hd)

theorem classCR_isFP_two_amalg {R : Set ℕ} {B₀ B₁ : Type u} [Group B₀] [Group B₁] {D : Type v}
    [Group D] (h₀ : ClassCR R B₀) (h₀' : IsFP 2 B₀) (h₁ : ClassCR R B₁) (h₁' : IsFP 2 B₁)
    (hD : Group.FG D) (f₀ : D →* B₀) (f₁ : D →* B₁) :
    ClassCR R (Amalg f₀ f₁) ∧ IsFP 2 (Amalg f₀ f₁) := by
  refine ⟨h₀.amalg h₁ hD f₀ f₁, ?_⟩
  obtain ⟨n₀, e₀, he₀, ⟨ψ₀⟩⟩ := h₀
  obtain ⟨n₁, e₁, he₁, ⟨ψ₁⟩⟩ := h₁
  exact isFP_two_amalg_of_pres ψ₀ ψ₁ h₀' h₁' hD f₀ f₁

end TheoremA.RelPres
