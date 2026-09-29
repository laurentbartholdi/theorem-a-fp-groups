module

public import RequestProject.TheoremA.RelPres.Class
public import RequestProject.TheoremA.Defs

/-!
# `C_R` is closed under ascending HNN extensions

Let `ψ : PresentedGroup S ≃* B` be a presentation on the generators `Fin n`, and `φ : B →* B`
injective.  Write `x_i = ψ (of i)`.

**Stable-letter convention.**  `ascHNN φ hφ` is Mathlib's `HNNExtension` with
`t * of a = of (φ a) * t`, i.e. `t b t⁻¹ = φ(b)`.  We keep this convention: the new letter
`Fin.last n` of the extended alphabet `Fin (n+1)` is sent to Mathlib's `HNNExtension.t` itself,
the old letters are renamed along `Fin.castSucc`, and the extra relators are
`h_i = T x_i T⁻¹ w_i⁻¹`, where `w_i` is a (classically chosen) raw word with value `φ(x_i)`.

`hnnPresentationEquiv` is the isomorphism between the presented group with relators
`castSucc(S) ∪ {h_i}` and `ascHNN φ hφ`; `ClassCR.ascHNN` is the closure theorem.  Only the
finitely many words `w_i` are used; no effectivity of `φ` is assumed.
-/

@[expose] public section

namespace TheoremA.RelPres

open HNNExtension

universe u

variable {B : Type u} [Group B] {n : ℕ} {S : Set (FreeGroup (Fin n))}

/-- Evaluating along the generator images of a presentation factors through the presentation. -/
theorem lift_presentation {H : Type*} [Group H] (ψ : PresentedGroup S ≃* B) (χ : B →* H)
    (x : FreeGroup (Fin n)) :
    FreeGroup.lift (fun i => χ (ψ (PresentedGroup.of i))) x = χ (ψ (PresentedGroup.mk S x)) := by
  have : FreeGroup.lift (fun i => χ (ψ (PresentedGroup.of i))) =
      χ.comp ((ψ : PresentedGroup S →* B).comp (PresentedGroup.mk S)) :=
    FreeGroup.ext_hom _ _ fun i => by simp [PresentedGroup.of]
  exact congrArg (fun F : FreeGroup (Fin n) →* H => F x) this

/-- Two homomorphisms out of `B` agreeing on the generator images agree. -/
theorem hom_ext_presentation {H : Type*} [Group H] (ψ : PresentedGroup S ≃* B)
    {f g : B →* H} (h : ∀ i, f (ψ (PresentedGroup.of i)) = g (ψ (PresentedGroup.of i))) :
    f = g := by
  have : f.comp (ψ : PresentedGroup S →* B) = g.comp (ψ : PresentedGroup S →* B) :=
    PresentedGroup.ext fun i => h i
  ext b
  have := congrArg (fun F : PresentedGroup S →* H => F (ψ.symm b)) this
  simpa using this

/-- Existence of a raw word representing `φ (x_i)`. -/
theorem exists_hnnWord (ψ : PresentedGroup S ≃* B) (φ : B →* B) (i : Fin n) :
    ∃ w : RawWord (Fin n), ψ (PresentedGroup.mk S w.eval) = φ (ψ (PresentedGroup.of i)) := by
  obtain ⟨x, hx⟩ := PresentedGroup.mk_surjective S (ψ.symm (φ (ψ (PresentedGroup.of i))))
  obtain ⟨w, rfl⟩ := RawWord.eval_surjective x
  exact ⟨w, by rw [hx, MulEquiv.apply_symm_apply]⟩

/-- A chosen raw word `w_i` with value `φ(x_i)`. -/
noncomputable def hnnWord (ψ : PresentedGroup S ≃* B) (φ : B →* B) (i : Fin n) :
    RawWord (Fin n) :=
  (exists_hnnWord ψ φ i).choose

theorem hnnWord_spec (ψ : PresentedGroup S ≃* B) (φ : B →* B) (i : Fin n) :
    ψ (PresentedGroup.mk S (hnnWord ψ φ i).eval) = φ (ψ (PresentedGroup.of i)) :=
  (exists_hnnWord ψ φ i).choose_spec

/-- The extra relator `h_i = T x_i T⁻¹ w_i⁻¹` on the alphabet `Fin (n+1)`, `T = Fin.last n`. -/
noncomputable def hnnRelator (ψ : PresentedGroup S ≃* B) (φ : B →* B) (i : Fin n) :
    RawWord (Fin (n + 1)) :=
  [(Fin.last n, true), (Fin.castSucc i, true), (Fin.last n, false)] ++
    RawWord.inv (RawWord.rename Fin.castSucc (hnnWord ψ φ i))

/-- The finite list of extra relators. -/
noncomputable def hnnRelators (ψ : PresentedGroup S ≃* B) (φ : B →* B) :
    List (RawWord (Fin (n + 1))) :=
  List.ofFn (hnnRelator ψ φ)

theorem eval_hnnRelator (ψ : PresentedGroup S ≃* B) (φ : B →* B) (i : Fin n) :
    (hnnRelator ψ φ i).eval = FreeGroup.of (Fin.last n) * FreeGroup.of (Fin.castSucc i) *
      (FreeGroup.of (Fin.last n))⁻¹ *
        (FreeGroup.map Fin.castSucc (hnnWord ψ φ i).eval)⁻¹ := by
  simp only [hnnRelator, RawWord.eval_append, RawWord.eval_inv, RawWord.eval_rename]
  rw [show ([(Fin.last n, true), (Fin.castSucc i, true), (Fin.last n, false)] :
      RawWord (Fin (n + 1))) = [(Fin.last n, true)] ++ [(Fin.castSucc i, true)] ++
        [(Fin.last n, false)] from rfl]
  simp only [RawWord.eval_append, RawWord.eval_pos, RawWord.eval_neg]

/-- The relator set of the extended presentation `P'`. -/
noncomputable def hnnRelSet (ψ : PresentedGroup S ≃* B) (φ : B →* B) :
    Set (FreeGroup (Fin (n + 1))) :=
  FreeGroup.map Fin.castSucc '' S ∪ RawWord.eval '' {w | w ∈ hnnRelators ψ φ}

variable (ψ : PresentedGroup S ≃* B) (φ : B →* B) (hφ : Function.Injective φ)

theorem hnnRelator_mem (i : Fin n) : (hnnRelator ψ φ i).eval ∈ hnnRelSet ψ φ :=
  Or.inr ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, rfl⟩

/-- The ascending HNN relation `t b t⁻¹ = φ b` in the project's `ascHNN`. -/
theorem ascHNN_conj (b : B) :
    (t : ascHNN φ hφ) * of b * t⁻¹ = of (φ b) := by
  have h := t_mul_of (G := B) (A := ⊤) (B := φ.range)
    (φ := Subgroup.topEquiv.trans (MonoidHom.ofInjective hφ)) ⟨b, Subgroup.mem_top b⟩
  rw [h, mul_inv_cancel_right]
  rfl

/-- Generator assignment for the forward map. -/
noncomputable def hnnFwdGen : Fin (n + 1) → ascHNN φ hφ :=
  Fin.lastCases t fun i => of (ψ (PresentedGroup.of i))

theorem lift_hnnFwdGen_castSucc (x : FreeGroup (Fin n)) :
    FreeGroup.lift (hnnFwdGen ψ φ hφ) (FreeGroup.map Fin.castSucc x) =
      of (ψ (PresentedGroup.mk S x)) := by
  have : (FreeGroup.lift (hnnFwdGen ψ φ hφ)).comp (FreeGroup.map Fin.castSucc) =
      FreeGroup.lift fun i => (of : B →* ascHNN φ hφ) (ψ (PresentedGroup.of i)) :=
    FreeGroup.ext_hom _ _ fun i => by simp [hnnFwdGen]
  rw [← MonoidHom.comp_apply, this, lift_presentation]

/-- **Forward map** `P' → ascHNN φ hφ`. -/
noncomputable def hnnFwd : PresentedGroup (hnnRelSet ψ φ) →* ascHNN φ hφ :=
  PresentedGroup.toGroup (f := hnnFwdGen ψ φ hφ) (rels := hnnRelSet ψ φ) (by
    rintro r (⟨s, hs, rfl⟩ | ⟨w, hw, rfl⟩)
    · rw [lift_hnnFwdGen_castSucc, PresentedGroup.one_of_mem hs, map_one, map_one]
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
      rw [eval_hnnRelator]
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, lift_hnnFwdGen_castSucc,
        hnnWord_spec]
      simp only [hnnFwdGen, Fin.lastCases_last, Fin.lastCases_castSucc]
      rw [ascHNN_conj, mul_inv_cancel])

/-- The old relators vanish in `P'`: the homomorphism `PresentedGroup S → P'`. -/
noncomputable def hnnBaseAux : PresentedGroup S →* PresentedGroup (hnnRelSet ψ φ) :=
  PresentedGroup.toGroup (f := fun i => PresentedGroup.of (Fin.castSucc i)) (by
    intro r hr
    have : FreeGroup.lift (fun i => (PresentedGroup.of (Fin.castSucc i) :
        PresentedGroup (hnnRelSet ψ φ))) =
        (PresentedGroup.mk (hnnRelSet ψ φ)).comp (FreeGroup.map Fin.castSucc) :=
      FreeGroup.ext_hom _ _ fun i => by simp [PresentedGroup.of]
    rw [this, MonoidHom.comp_apply]
    exact PresentedGroup.one_of_mem (Or.inl ⟨r, hr, rfl⟩))

theorem hnnBaseAux_mk (x : FreeGroup (Fin n)) :
    hnnBaseAux ψ φ (PresentedGroup.mk S x) =
      PresentedGroup.mk (hnnRelSet ψ φ) (FreeGroup.map Fin.castSucc x) := by
  have : (hnnBaseAux ψ φ).comp (PresentedGroup.mk S) =
      (PresentedGroup.mk (hnnRelSet ψ φ)).comp (FreeGroup.map Fin.castSucc) :=
    FreeGroup.ext_hom _ _ fun i => by
      simp [hnnBaseAux, ← PresentedGroup.of.eq_def, PresentedGroup.toGroup.of]
  exact congrArg (fun F : FreeGroup (Fin n) →* _ => F x) this

/-- The homomorphism `j : B → P'`. -/
noncomputable def hnnBase : B →* PresentedGroup (hnnRelSet ψ φ) :=
  (hnnBaseAux ψ φ).comp (ψ.symm : B →* PresentedGroup S)

theorem hnnBase_gen (i : Fin n) :
    hnnBase ψ φ (ψ (PresentedGroup.of i)) = PresentedGroup.of (Fin.castSucc i) := by
  simp [hnnBase, hnnBaseAux, PresentedGroup.toGroup.of]

/-- The image `τ` of the new letter in `P'`. -/
noncomputable def hnnStable : PresentedGroup (hnnRelSet ψ φ) := PresentedGroup.of (Fin.last n)

/-- The finitely many extra relators give `τ j(b) τ⁻¹ = j(φ b)` for **all** `b`. -/
theorem hnnStable_conj (b : B) :
    hnnStable ψ φ * hnnBase ψ φ b * (hnnStable ψ φ)⁻¹ = hnnBase ψ φ (φ b) := by
  have key : (MulAut.conj (hnnStable ψ φ)).toMonoidHom.comp (hnnBase ψ φ) =
      (hnnBase ψ φ).comp φ := by
    apply hom_ext_presentation ψ
    intro i
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hnnBase_gen]
    rw [← hnnWord_spec ψ φ i]
    simp only [hnnBase, MonoidHom.comp_apply, MonoidHom.coe_coe, MulEquiv.symm_apply_apply,
      hnnBaseAux_mk]
    have h := PresentedGroup.one_of_mem (hnnRelator_mem ψ φ i)
    rw [eval_hnnRelator] at h
    simp only [map_mul, map_inv] at h
    rw [mul_inv_eq_one] at h
    exact h
  have := congrArg (fun F : B →* PresentedGroup (hnnRelSet ψ φ) => F b) key
  simpa using this

/-- **Backward map** `ascHNN φ hφ → P'`, via the HNN universal property. -/
noncomputable def hnnBwd : ascHNN φ hφ →* PresentedGroup (hnnRelSet ψ φ) :=
  HNNExtension.lift (hnnBase ψ φ) (hnnStable ψ φ) (by
    intro a
    have e : ((Subgroup.topEquiv.trans (MonoidHom.ofInjective hφ)) a : B) = φ a := rfl
    rw [e, ← hnnStable_conj ψ φ a, inv_mul_cancel_right])

theorem hnnBwd_of (b : B) : hnnBwd ψ φ hφ (of b) = hnnBase ψ φ b := by
  simp [hnnBwd]

theorem hnnBwd_t : hnnBwd ψ φ hφ t = hnnStable ψ φ := by
  simp [hnnBwd]

theorem hnnFwd_of (x : Fin (n + 1)) :
    hnnFwd ψ φ hφ (PresentedGroup.of x) = hnnFwdGen ψ φ hφ x := by
  simp [hnnFwd, PresentedGroup.toGroup.of]

theorem hnnFwd_hnnBase (b : B) : hnnFwd ψ φ hφ (hnnBase ψ φ b) = of b := by
  have : (hnnFwd ψ φ hφ).comp (hnnBase ψ φ) = of := by
    apply hom_ext_presentation ψ
    intro i
    simp [hnnBase_gen, hnnFwd, PresentedGroup.toGroup.of, hnnFwdGen]
  exact congrArg (fun F : B →* ascHNN φ hφ => F b) this

/-- **`P'` is the ascending HNN extension.** -/
noncomputable def hnnPresentationEquiv : PresentedGroup (hnnRelSet ψ φ) ≃* ascHNN φ hφ :=
  MonoidHom.toMulEquiv (hnnFwd ψ φ hφ) (hnnBwd ψ φ hφ)
    (by
      apply PresentedGroup.ext
      intro x
      refine Fin.lastCases ?_ (fun i => ?_) x
      · simp [hnnFwd_of, hnnFwdGen, hnnBwd_t, hnnStable]
      · simp [hnnFwd_of, hnnFwdGen, hnnBwd_of, hnnBase_gen])
    (by
      apply HNNExtension.hom_ext
      · ext b
        simp [hnnBwd_of, hnnFwd_hnnBase]
      · simp [hnnBwd_t, hnnStable, hnnFwd_of, hnnFwdGen])

/-- Compatibility with the old generators. -/
theorem hnnPresentationEquiv_of_castSucc (i : Fin n) :
    hnnPresentationEquiv ψ φ hφ (PresentedGroup.of (Fin.castSucc i)) =
      of (ψ (PresentedGroup.of i)) := by
  simp [hnnPresentationEquiv, hnnFwd_of, hnnFwdGen]

/-- Compatibility with the stable letter. -/
theorem hnnPresentationEquiv_of_last :
    hnnPresentationEquiv ψ φ hφ (PresentedGroup.of (Fin.last n)) = t := by
  simp [hnnPresentationEquiv, hnnFwd_of, hnnFwdGen]

/-- Compatibility with the base homomorphism. -/
theorem hnnPresentationEquiv_symm_of (b : B) :
    (hnnPresentationEquiv ψ φ hφ).symm (of b) = hnnBase ψ φ b := by
  rw [MulEquiv.symm_apply_eq]
  exact (hnnFwd_hnnBase ψ φ hφ b).symm

/-- **`C_R` is closed under ascending HNN extensions**, with the same oracle `R`, for every
injective endomorphism `φ` (no effectivity hypothesis on `φ`). -/
theorem ClassCR.ascHNN {R : Set ℕ} {X : Type u} [Group X] (h : ClassCR R X) (φ : X →* X)
    (hφ : Function.Injective φ) : ClassCR R (TheoremA.ascHNN φ hφ) := by
  obtain ⟨n, e, he, ⟨ψ⟩⟩ := h
  refine ⟨n + 1, extendEnum e Fin.castSucc (hnnRelators ψ φ), he.extendEnum _ _, ⟨?_⟩⟩
  rw [enumRelators_extendEnum]
  exact hnnPresentationEquiv ψ φ hφ

/-- The closure statement in exactly the shape of the third conjunct of `UniversalBases`,
for the class `ClassCR R` with a fixed oracle `R`. -/
theorem classCR_ascHNN_closure (R : Set ℕ) :
    ∀ (X : Type u) [Group X], ClassCR R X →
      ∀ (φ : X →* X) (hφ : Function.Injective φ), ClassCR R (TheoremA.ascHNN φ hφ) :=
  fun _ _ h φ hφ => h.ascHNN φ hφ

end TheoremA.RelPres
