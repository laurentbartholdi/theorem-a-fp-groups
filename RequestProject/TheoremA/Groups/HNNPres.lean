module

public import RequestProject.TheoremA.Groups.RelPresent

/-!
# HNN extensions along finitely generated subgroups: presentations, `C_R`, `FP₂`

Let `A, C ≤ B`, `φ : A ≃* C`, and let `a : Fin m → A` generate `A`.  For a presentation
`ψ : PresentedGroup S ≃* B` on `Fin n`, the actual Mathlib HNN extension
`HNNExtension B A C φ` (convention `t a t⁻¹ = φ a`) is presented on `Fin (n + 1)` by the old
relators and the `m` extra relators `T u_j T⁻¹ v_j⁻¹`, where `u_j`, `v_j` are (classically
chosen) raw words for `a_j` and `φ a_j`.  No algorithm for `φ` or for membership in `A` is
used, and `A` need not be finitely presented.

* `hnnGenPresEquiv` — the isomorphism with the actual HNN extension;
* `ClassCR.hnn` — `C_R` is preserved (same oracle);
* `isFP_two_hnn` — `FP₂` is preserved.
-/

@[expose] public section

namespace TheoremA.RelPres

open PresentedGroup HNNExtension

universe u

section Words

variable {B : Type*} [Group B] {n : ℕ} {S : Set (FreeGroup (Fin n))}

theorem exists_rawWord (ψ : PresentedGroup S ≃* B) (b : B) :
    ∃ w : RawWord (Fin n), ψ (PresentedGroup.mk S w.eval) = b := by
  obtain ⟨x, hx⟩ := PresentedGroup.mk_surjective S (ψ.symm b)
  obtain ⟨w, rfl⟩ := RawWord.eval_surjective x
  exact ⟨w, by rw [hx, MulEquiv.apply_symm_apply]⟩

/-- A chosen raw word representing `b`. -/
noncomputable def wordFor (ψ : PresentedGroup S ≃* B) (b : B) : RawWord (Fin n) :=
  (exists_rawWord ψ b).choose

theorem wordFor_spec (ψ : PresentedGroup S ≃* B) (b : B) :
    ψ (PresentedGroup.mk S (wordFor ψ b).eval) = b :=
  (exists_rawWord ψ b).choose_spec

end Words

section HNN

variable {B : Type u} [Group B] {n : ℕ} {S : Set (FreeGroup (Fin n))}
  {A C : Subgroup B} (φ : A ≃* C) {m : ℕ} (a : Fin m → A)
  (ψ : PresentedGroup S ≃* B)

/-- The stable letter `T = Fin.natAdd n 0` of `Fin (n + 1)`. -/
def stableLetter (n : ℕ) : Fin (n + 1) := Fin.natAdd n 0

/-- The extra relator `T u_j T⁻¹ v_j⁻¹`. -/
noncomputable def hnnGenRelator (j : Fin m) : RawWord (Fin (n + 1)) :=
  [(stableLetter n, true)] ++ RawWord.rename (Fin.castAdd 1) (wordFor ψ (a j : B)) ++
    [(stableLetter n, false)] ++
      RawWord.inv (RawWord.rename (Fin.castAdd 1) (wordFor ψ (φ (a j) : B)))

/-- The finite list of extra relators. -/
noncomputable def hnnGenRelators : List (RawWord (Fin (n + 1))) := List.ofFn (hnnGenRelator φ a ψ)

theorem eval_hnnGenRelator (j : Fin m) :
    (hnnGenRelator φ a ψ j).eval = FreeGroup.of (stableLetter n) *
      FreeGroup.map (Fin.castAdd 1) (wordFor ψ (a j : B)).eval *
        (FreeGroup.of (stableLetter n))⁻¹ *
          (FreeGroup.map (Fin.castAdd 1) (wordFor ψ (φ (a j) : B)).eval)⁻¹ := by
  simp only [hnnGenRelator, RawWord.eval_append, RawWord.eval_pos, RawWord.eval_neg,
    RawWord.eval_inv, RawWord.eval_rename]

/-- The new generator of the HNN extension. -/
def hnnY : Fin 1 → HNNExtension B A C φ := fun _ => t

theorem hnnGen_rels : ∀ u ∈ hnnGenRelators φ a ψ,
    FreeGroup.lift (relGens ψ (of : B →* HNNExtension B A C φ) (hnnY φ)) u.eval = 1 := by
  intro u hu
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hu
  rw [eval_hnnGenRelator]
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of, lift_relGens_castAdd, wordFor_spec]
  have hT : relGens ψ (of : B →* HNNExtension B A C φ) (hnnY φ) (stableLetter n) = t := by
    simp [relGens, stableLetter, hnnY]
  rw [hT, t_mul_of, mul_inv_cancel_right, mul_inv_cancel]

/-- The presented group. -/
abbrev HNNPres := PresentedGroup (relExt S 1 (hnnGenRelators φ a ψ))

/-- The image of the stable letter in the presented group. -/
noncomputable def hnnPresT : HNNPres φ a ψ := of (stableLetter n)

theorem hnnPres_conj_gen (j : Fin m) :
    hnnPresT φ a ψ * relBase ψ 1 (hnnGenRelators φ a ψ) (a j : B) * (hnnPresT φ a ψ)⁻¹ =
      relBase ψ 1 (hnnGenRelators φ a ψ) (φ (a j) : B) := by
  have h := PresentedGroup.one_of_mem (rels := relExt S 1 (hnnGenRelators φ a ψ))
    (Or.inr ⟨_, List.mem_ofFn.2 ⟨j, rfl⟩, rfl⟩ : (hnnGenRelator φ a ψ j).eval ∈ _)
  rw [eval_hnnGenRelator] at h
  simp only [map_mul, map_inv] at h
  rw [mul_inv_eq_one] at h
  rw [← wordFor_spec ψ (a j : B), ← wordFor_spec ψ (φ (a j) : B), relBase_mk, relBase_mk]
  exact h

/-- `T j(a) T⁻¹ = j(φ a)` for **all** `a ∈ A`. -/
theorem hnnPres_conj (ha : Subgroup.closure (Set.range a) = ⊤) (x : A) :
    hnnPresT φ a ψ * relBase ψ 1 (hnnGenRelators φ a ψ) (x : B) =
      relBase ψ 1 (hnnGenRelators φ a ψ) (φ x : B) * hnnPresT φ a ψ := by
  let f₁ : A →* HNNPres φ a ψ :=
    (MulAut.conj (hnnPresT φ a ψ)).toMonoidHom.comp ((relBase ψ 1 _).comp A.subtype)
  let f₂ : A →* HNNPres φ a ψ :=
    (relBase ψ 1 _).comp (C.subtype.comp φ.toMonoidHom)
  have hf : f₁ = f₂ := by
    apply MonoidHom.eq_of_eqOn_dense ha
    rintro _ ⟨j, rfl⟩
    simp only [f₁, f₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype]
    exact hnnPres_conj_gen φ a ψ j
  have := DFunLike.congr_fun hf x
  simp only [f₁, f₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_subtype] at this
  rw [← this, inv_mul_cancel_right]

/-- **Backward map** from the actual HNN extension, by its universal property. -/
noncomputable def hnnGenBwd (ha : Subgroup.closure (Set.range a) = ⊤) :
    HNNExtension B A C φ →* HNNPres φ a ψ :=
  HNNExtension.lift (relBase ψ 1 _) (hnnPresT φ a ψ) (hnnPres_conj φ a ψ ha)

/-- **The presentation of the HNN extension.** -/
noncomputable def hnnGenPresEquiv (ha : Subgroup.closure (Set.range a) = ⊤) :
    HNNPres φ a ψ ≃* HNNExtension B A C φ :=
  relPresEquiv ψ of (hnnY φ) (hnnGenRelators φ a ψ) (hnnGen_rels φ a ψ) (hnnGenBwd φ a ψ ha)
    (fun b => by simp [hnnGenBwd])
    (fun l => by
      simp only [hnnGenBwd, hnnY, lift_t, hnnPresT, stableLetter]
      congr 1
      exact congrArg _ (Subsingleton.elim _ _))
    (fun f hf ht => by
      apply HNNExtension.hom_ext
      · simpa using hf
      · simpa [hnnY] using ht 0)

theorem hnnGenPresEquiv_of_castAdd (ha : Subgroup.closure (Set.range a) = ⊤) (j : Fin n) :
    hnnGenPresEquiv φ a ψ ha (PresentedGroup.of (Fin.castAdd 1 j)) =
      HNNExtension.of (ψ (PresentedGroup.of j)) :=
  relPresEquiv_of_castAdd _ _ _ _ _ _ _ _ _ j

theorem hnnGenPresEquiv_of_stable (ha : Subgroup.closure (Set.range a) = ⊤) :
    hnnGenPresEquiv φ a ψ ha (PresentedGroup.of (stableLetter n)) = t :=
  relPresEquiv_of_natAdd _ _ _ _ _ _ _ _ _ 0

end HNN

/-- A finitely generated group admits a finite generating tuple. -/
theorem exists_fin_generating_tuple {A : Type*} [Group A] (hA : Group.FG A) :
    ∃ (m : ℕ) (a : Fin m → A), Subgroup.closure (Set.range a) = ⊤ := by
  obtain ⟨s, hs⟩ := Group.isMulFG_iff.mp hA
  refine ⟨s.card, fun i => (s.equivFin.symm i : A), ?_⟩
  rw [← hs]
  congr 1
  ext x
  simp only [Set.mem_range, Finset.mem_coe]
  constructor
  · rintro ⟨i, rfl⟩; exact (s.equivFin.symm i).2
  · intro hx; exact ⟨s.equivFin ⟨x, hx⟩, by simp⟩

/-- **`C_R` is closed under HNN extensions along finitely generated subgroups** (same oracle;
no hypothesis on `φ` beyond being an isomorphism of subgroups). -/
theorem ClassCR.hnn {R : Set ℕ} {B : Type u} [Group B] (hB : ClassCR R B) {A C : Subgroup B}
    (φ : A ≃* C) (hA : Group.FG A) : ClassCR R (HNNExtension B A C φ) := by
  obtain ⟨n, e, he, ⟨ψ⟩⟩ := hB
  obtain ⟨m, a, ha⟩ := exists_fin_generating_tuple hA
  exact classCR_of_relPres he _ (hnnGenPresEquiv φ a ψ ha)

/-- **`FP₂` is preserved by HNN extensions along finitely generated subgroups**, for a base with
a finite-alphabet presentation. -/
theorem isFP_two_hnn_of_pres {B : Type u} [Group B] {n : ℕ} {S : Set (FreeGroup (Fin n))}
    (ψ : PresentedGroup S ≃* B) (hB : IsFP 2 B) {A C : Subgroup B} (φ : A ≃* C)
    (hA : Group.FG A) : IsFP 2 (HNNExtension B A C φ) := by
  obtain ⟨m, a, ha⟩ := exists_fin_generating_tuple hA
  exact isFP_two_of_relPres ψ hB _ (hnnGenPresEquiv φ a ψ ha)

/-- Both conclusions for a base in `C_R` of type `FP₂`. -/
theorem classCR_isFP_two_hnn {R : Set ℕ} {B : Type u} [Group B] (hB : ClassCR R B)
    (hB2 : IsFP 2 B) {A C : Subgroup B} (φ : A ≃* C) (hA : Group.FG A) :
    ClassCR R (HNNExtension B A C φ) ∧ IsFP 2 (HNNExtension B A C φ) := by
  refine ⟨hB.hnn φ hA, ?_⟩
  obtain ⟨n, e, he, ⟨ψ⟩⟩ := hB
  exact isFP_two_hnn_of_pres ψ hB2 φ hA

end TheoremA.RelPres
