module

public import RequestProject.TheoremA.RelPres.TwoGenWord
public import RequestProject.TheoremA.RelPres.OmegaGroup

/-!
# Effective two-generator embedding with the same oracle

Fix a natural-alphabet partial enumerator `E` and put `S = enumRelatorsNat E`,
`G = PresentedGroup S` with generators `x_n = of n`, `H = HX x` (Checkpoint I) and
`P₂ = PresentedGroup (enumRelators (twoGenEnum E))` on the letters `B = 0`, `T = 1`.

* `twoGenFwd E : P₂ →* H` (`B ↦ b`, `T ↦ t`) and `twoGenBwd E : H →* P₂` (HNN universal
  property with stable letter `T`, `x_n ↦ W_n`, `a ↦ T B T⁻¹`, `b ↦ B`).
* `twoGenEquiv E : P₂ ≃* H`, with the images of `B`, `T` and every `W_n`.
* `twoGenEmb E : G →* P₂`, injective, with `twoGenEmb E (of n) = value (W_n)`.
* `CountablyPresentedIn.exists_twoGen_embedding` — every countably `R`-presented group (in any
  universe) embeds in a group with an explicit `R`-enumerated presentation on `Fin 2`.
* `VR R := P₂` for `E = omegaEnum R`: `classCR_VR`, `VR.closure_gens`, `Omega.exists_injective_VR`
  and `ClassCR.exists_injective_hom_VR` (`V_R` is universal for `C_R`).
-/

@[expose] public section

namespace TheoremA.RelPres

open HNNExtension RawWord

universe u

theorem toGroup_mk {α K : Type*} [Group K] {rels : Set (FreeGroup α)} {f : α → K}
    (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (r : FreeGroup α) :
    PresentedGroup.toGroup h (PresentedGroup.mk rels r) = FreeGroup.lift f r := by
  have : (PresentedGroup.toGroup h).comp (PresentedGroup.mk rels) = FreeGroup.lift f :=
    FreeGroup.ext_hom _ _ fun a => by
      simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      exact PresentedGroup.toGroup.of h
  exact DFunLike.congr_fun this r

variable (E : ℕ →. RawWord ℕ)

/-- The presented group `G = ⟨ℕ | S⟩`, `S = enumRelatorsNat E`. -/
abbrev GE : Type := PresentedGroup (enumRelatorsNat E)

/-- Its canonical generators `x_n`. -/
def xE : ℕ → GE E := PresentedGroup.of

/-- The general HNN extension `H` for `x = xE E`. -/
abbrev HE : Type := HX (xE E)

/-- The two-generator presented group `P₂`. -/
abbrev P2 : Type := PresentedGroup (enumRelators (twoGenEnum E))

/-! ### `P₂ →* H` -/

/-- Generator images `B ↦ b`, `T ↦ t`. -/
noncomputable def fwdGens : Fin 2 → HE E := ![bHX (xE E), t]

theorem lift_fwdGens_wWord (n : ℕ) :
    FreeGroup.lift (fwdGens E) (eval (wWord n)) = baseHX (xE E) (xE E n) := by
  rw [eval_wWord, map_wVal, HX_x_eq]
  simp [fwdGens]

theorem lift_fwdGens_thetaWord (y : FreeGroup ℕ) :
    FreeGroup.lift (fwdGens E) (thetaWord y) =
      baseHX (xE E) (PresentedGroup.mk (enumRelatorsNat E) y) := by
  have : (FreeGroup.lift (fwdGens E)).comp thetaWord =
      (baseHX (xE E)).comp (PresentedGroup.mk (enumRelatorsNat E)) :=
    FreeGroup.ext_hom _ _ fun n => by
      simp only [MonoidHom.comp_apply, thetaWord, FreeGroup.lift_apply_of]
      exact lift_fwdGens_wWord E n
  exact DFunLike.congr_fun this y

theorem fwdGens_rels : ∀ r ∈ enumRelators (twoGenEnum E), FreeGroup.lift (fwdGens E) r = 1 := by
  rw [enumRelators_twoGenEnum]
  rintro _ ⟨s, hs, rfl⟩
  rw [lift_fwdGens_thetaWord, PresentedGroup.one_of_mem hs, map_one]

/-- **The forward map** `F : P₂ →* H`. -/
noncomputable def twoGenFwd : P2 E →* HE E := PresentedGroup.toGroup (fwdGens_rels E)

/-! ### `H →* P₂` -/

/-- The letter `B` in `P₂`. -/
noncomputable def bP : P2 E := PresentedGroup.of 0
/-- The letter `T` in `P₂`. -/
noncomputable def tP : P2 E := PresentedGroup.of 1

/-- The value of `W_n` in `P₂`. -/
noncomputable def wP (n : ℕ) : P2 E := PresentedGroup.mk _ (eval (wWord n))

theorem wP_eq (n : ℕ) : wP E n = wVal (bP E) (tP E) (n + 1) := by
  rw [wP, eval_wWord, map_wVal]; rfl

theorem lift_wP (y : FreeGroup ℕ) :
    FreeGroup.lift (wP E) y = PresentedGroup.mk _ (thetaWord y) := by
  have : FreeGroup.lift (wP E) = (PresentedGroup.mk _).comp thetaWord :=
    FreeGroup.ext_hom _ _ fun n => by simp [wP, thetaWord]
  exact DFunLike.congr_fun this y

theorem wP_rels : ∀ r ∈ enumRelatorsNat E, FreeGroup.lift (wP E) r = 1 := by
  intro r hr
  rw [lift_wP]
  apply PresentedGroup.one_of_mem
  rw [enumRelators_twoGenEnum]
  exact ⟨r, hr, rfl⟩

/-- `g : G →* P₂`, `x_n ↦ value(W_n)`. -/
noncomputable def gP : GE E →* P2 E := PresentedGroup.toGroup (wP_rels E)

/-- `F(a,b) →* P₂`, `a ↦ T B T⁻¹`, `b ↦ B`. -/
noncomputable def fabP : FreeGroup (Fin 2) →* P2 E := FreeGroup.lift ![tP E * bP E * (tP E)⁻¹, bP E]

/-- `q : Q →* P₂`. -/
noncomputable def qP : QGrp (GE E) →* P2 E := Monoid.Coprod.lift (gP E) (fabP E)

theorem qP_conj (w : FreeGroup ℕ) :
    tP E * qP E (uHom (GE E) w) * (tP E)⁻¹ = qP E (vHom (xE E) w) := by
  have : (MulAut.conj (tP E)).toMonoidHom.comp ((qP E).comp (uHom (GE E))) =
      (qP E).comp (vHom (xE E)) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    cases i with
    | zero => simp [qP, fabP, vGen]
    | succ n =>
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      simp only [uHom_of, vHom_of, vGen, map_mul, map_inv, map_pow, qP, Monoid.Coprod.lift_apply_inr,
        Monoid.Coprod.lift_apply_inl, fabP, FreeGroup.lift_apply_of]
      simp only [gP, xE, PresentedGroup.toGroup.of, wP_eq]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, wVal]
      generalize tP E * bP E * (tP E)⁻¹ = A
      group
  exact DFunLike.congr_fun this w

theorem qP_hnn (c : (uHom (GE E)).range) :
    tP E * qP E c = qP E (thetaEquiv (xE E) c) * tP E := by
  obtain ⟨_, w, rfl⟩ := c
  rw [thetaEquiv_apply, ← qP_conj, inv_mul_cancel_right]

/-- **The backward map** `D : H →* P₂`, via the HNN universal property. -/
noncomputable def twoGenBwd : HE E →* P2 E := HNNExtension.lift (qP E) (tP E) (qP_hnn E)

/-! ### Inverse laws -/

theorem twoGenFwd_of (i : Fin 2) : twoGenFwd E (PresentedGroup.of i) = fwdGens E i :=
  PresentedGroup.toGroup.of _

theorem twoGenFwd_wP (n : ℕ) : twoGenFwd E (wP E n) = baseHX (xE E) (xE E n) := by
  rw [wP, twoGenFwd, toGroup_mk, lift_fwdGens_wWord]

theorem twoGenBwd_comp_twoGenFwd : (twoGenBwd E).comp (twoGenFwd E) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  fin_cases i
  · simp [twoGenFwd_of, fwdGens, twoGenBwd, bHX, qP, fabP, bP]
  · simp [twoGenFwd_of, fwdGens, twoGenBwd, tP]

theorem twoGenFwd_comp_twoGenBwd : (twoGenFwd E).comp (twoGenBwd E) = MonoidHom.id _ := by
  apply HNNExtension.hom_ext
  · apply Monoid.Coprod.hom_ext
    · apply PresentedGroup.ext
      intro n
      simp only [MonoidHom.comp_apply, twoGenBwd, HNNExtension.lift_of, qP,
        Monoid.Coprod.lift_apply_inl, gP, PresentedGroup.toGroup.of, twoGenFwd_wP,
        MonoidHom.id_apply]
      rfl
    · refine FreeGroup.ext_hom _ _ fun i => ?_
      fin_cases i
      · simp only [MonoidHom.comp_apply, twoGenBwd, HNNExtension.lift_of, qP,
          Monoid.Coprod.lift_apply_inr, fabP, FreeGroup.lift_apply_of, MonoidHom.id_apply]
        simp [bP, tP, twoGenFwd_of, fwdGens, HX_a_eq]
      · simp [twoGenBwd, qP, fabP, bP, twoGenFwd_of, fwdGens, bHX]
  · simp [twoGenBwd, tP, twoGenFwd_of, fwdGens]

/-- **`P₂ ≅ H`.** -/
noncomputable def twoGenEquiv : P2 E ≃* HE E :=
  MonoidHom.toMulEquiv (twoGenFwd E) (twoGenBwd E) (twoGenBwd_comp_twoGenFwd E)
    (twoGenFwd_comp_twoGenBwd E)

@[simp] theorem twoGenEquiv_B : twoGenEquiv E (PresentedGroup.of 0) = bHX (xE E) :=
  twoGenFwd_of E 0

@[simp] theorem twoGenEquiv_T : twoGenEquiv E (PresentedGroup.of 1) = t :=
  twoGenFwd_of E 1

theorem twoGenEquiv_wP (n : ℕ) : twoGenEquiv E (wP E n) = baseHX (xE E) (xE E n) :=
  twoGenFwd_wP E n

/-- The injective embedding `G →* P₂`. -/
noncomputable def twoGenEmb : GE E →* P2 E := (twoGenEquiv E).symm.toMonoidHom.comp (baseHX (xE E))

theorem twoGenEmb_injective : Function.Injective (twoGenEmb E) :=
  (twoGenEquiv E).symm.injective.comp (baseHX_injective _)

/-- **Compatibility:** `x_n ↦ value(W_n)`. -/
theorem twoGenEmb_of (n : ℕ) : twoGenEmb E (PresentedGroup.of n) = wP E n := by
  rw [twoGenEmb, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq,
    twoGenEquiv_wP]
  rfl

/-- `P₂` is generated by the two displayed letters. -/
theorem P2.closure_gens :
    Subgroup.closure (Set.range (PresentedGroup.of : Fin 2 → P2 E)) = ⊤ :=
  PresentedGroup.closure_range_of _

variable {R : Set ℕ}

/-- `P₂` is in `C_R`, with the explicit two-letter enumerator. -/
theorem classCR_P2 (hE : IsNatEnumerator R E) : ClassCR R (P2 E) :=
  ⟨2, twoGenEnum E, hE.twoGenEnum, ⟨MulEquiv.refl _⟩⟩

/-- **Two-generator embedding from an enumerator witness.** -/
theorem IsNatEnumerator.exists_twoGen_embedding (hE : IsNatEnumerator R E) :
    IsEnumerator R (TheoremA.RelPres.twoGenEnum E) ∧
      ∃ f : GE E →* P2 E, Function.Injective f ∧ ∀ n, f (PresentedGroup.of n) = wP E n :=
  ⟨hE.twoGenEnum, twoGenEmb E, twoGenEmb_injective E, twoGenEmb_of E⟩

/-- Transport along a presentation equivalence. -/
theorem exists_injective_P2_of_equiv {X : Type u} [Group X] (ψ : GE E ≃* X) :
    ∃ f : X →* P2 E, Function.Injective f :=
  ⟨(twoGenEmb E).comp ψ.symm.toMonoidHom, (twoGenEmb_injective E).comp ψ.symm.injective⟩

/-- **Effective two-generator embedding.**  Every countably `R`-presented group `X` (in any
universe) embeds in a group with an explicit presentation on `Fin 2` whose relators are
enumerated relative to the same oracle `R`. -/
theorem CountablyPresentedIn.exists_twoGen_embedding {X : Type u} [Group X]
    (h : CountablyPresentedIn R X) :
    ∃ e₂ : ℕ →. RawWord (Fin 2), IsEnumerator R e₂ ∧
      ∃ f : X →* PresentedGroup (enumRelators e₂), Function.Injective f := by
  obtain ⟨E, hE, ⟨ψ⟩⟩ := h
  exact ⟨twoGenEnum E, hE.twoGenEnum, exists_injective_P2_of_equiv E ψ⟩

/-- The same result in the form: a two-generated member of `C_R` containing `X`. -/
theorem CountablyPresentedIn.exists_twoGen_classCR {X : Type u} [Group X]
    (h : CountablyPresentedIn R X) :
    ∃ (Y : Type) (_ : Group Y) (y : Fin 2 → Y), ClassCR R Y ∧
      Subgroup.closure (Set.range y) = ⊤ ∧ ∃ f : X →* Y, Function.Injective f := by
  obtain ⟨E, hE, ⟨ψ⟩⟩ := h
  exact ⟨P2 E, inferInstance, PresentedGroup.of, classCR_P2 E hE, P2.closure_gens E,
    exists_injective_P2_of_equiv E ψ⟩

/-! ### Application to `Ω_R` -/

/-- **The group `V_R`**: the explicit two-generator presentation obtained from `E_Ω`. -/
abbrev VR (R : Set ℕ) : Type := P2 (omegaEnum R)

theorem classCR_VR (R : Set ℕ) : ClassCR R (VR R) := classCR_P2 _ isNatEnumerator_omegaEnum

theorem VR.closure_gens (R : Set ℕ) :
    Subgroup.closure (Set.range (PresentedGroup.of : Fin 2 → VR R)) = ⊤ :=
  P2.closure_gens _

/-- **`Ω_R` embeds in `V_R`.** -/
theorem Omega.exists_injective_VR (R : Set ℕ) : ∃ f : Omega R →* VR R, Function.Injective f := by
  have : Nonempty (GE (omegaEnum R) ≃* Omega R) := by
    unfold GE; rw [enumRelatorsNat_omegaEnum]; exact ⟨MulEquiv.refl _⟩
  exact exists_injective_P2_of_equiv _ this.some

/-- **`V_R` is universal for `C_R`**: every member of `C_R` embeds in `V_R`. -/
theorem ClassCR.exists_injective_hom_VR {X : Type u} [Group X] (h : ClassCR R X) :
    ∃ f : X →* VR R, Function.Injective f := by
  obtain ⟨g, hg⟩ := h.exists_injective_hom_omega
  obtain ⟨f, hf⟩ := Omega.exists_injective_VR R
  exact ⟨f.comp g, hf.comp hg⟩

end TheoremA.RelPres
