module

public import RequestProject.TheoremA.Proved
public import RequestProject.TheoremA.RelPres.InputOracle
public import RequestProject.TheoremA.RelPres.Diagram

/-!
# Theorem A from one explicit relative Leary hypothesis

* `RelativeLearyFP2` — the relative Leary statement, stated here as a `Prop`: every
  member of `C_R` embeds in an `FP₂` member of the **same** class `C_R`.
* `universalBases_of_relativeLeary : RelativeLearyFP2 → UniversalBases`, proved directly from
  its components (the input oracle, `V_R`, the closure theorems) and the explicit argument.
* `theoremA_of_relativeLeary : RelativeLearyFP2 → TheoremAStatement`, via the proved conditional
  Theorem A `theoremA_of_lemma31_universalBases` and the proved `lemma_3_1`.

Neither theorem uses the unconditional `universalBases` or `theoremA`.  `RelativeLearyFP2` is not
proved in this file; it is proved as `relativeLearyFP2` in `Kernel/Unconditional.lean`, from
`Leary.flagSeparation`.
-/

@[expose] public section

namespace TheoremA

open RelPres

universe u

/-- **The relative Leary `FP₂` embedding statement** (proved as `relativeLearyFP2` in
`Kernel/Unconditional.lean`): for every oracle `R ⊆ ℕ` and every group `H` in `C_R`, there is an
`FP₂` group `B`, again in `C_R` for the same `R`, into which `H` embeds. -/
def RelativeLearyFP2 : Prop :=
  ∀ (R : Set ℕ) (H : Type u) [Group H], ClassCR R H →
    ∃ (B : Type u) (_ : Group B), ClassCR R B ∧ IsFP 2 B ∧ ∃ f : H →* B, Function.Injective f

/-- The universe lift of `V_R` is in `C_R`. -/
theorem classCR_ULift_VR (R : Set ℕ) : ClassCR R (ULift.{u} (VR R)) := by
  obtain ⟨n, e, he, ⟨ψ⟩⟩ := classCR_VR R
  exact ⟨n, e, he, ⟨ψ.trans MulEquiv.ulift.symm⟩⟩

/-- **Universal bases from the relative Leary hypothesis** (conditional; the hypothesis is an
explicit argument). -/
theorem universalBases_of_relativeLeary (hLeary : RelativeLearyFP2.{u}) :
    UniversalBases.{u} := by
  intro r T G _ _
  obtain ⟨R, f, hf⟩ := exists_oracle_injective_hom_VR G
  obtain ⟨B, _, hBC, hBFP, j, hj⟩ := hLeary R (ULift.{u} (VR R)) (classCR_ULift_VR R)
  let up : VR R →* ULift.{u} (VR R) := MulEquiv.ulift.symm.toMonoidHom
  have hup : Function.Injective up := MulEquiv.ulift.symm.injective
  refine ⟨fun X _ => ClassCR R X, ⟨B, inferInstance, hBC, hBFP,
    ⟨(j.comp up).comp f, (hj.comp hup).comp hf⟩, ?_⟩,
    classCR_diagramGroup_closure R r T, classCR_ascHNN_closure R⟩
  intro Y _ hY
  obtain ⟨g, hg⟩ := hY.exists_injective_hom_VR
  exact ⟨(j.comp up).comp g, (hj.comp hup).comp hg⟩

/-- **Theorem A from the relative Leary hypothesis** (conditional; the hypothesis is an
explicit argument). -/
theorem theoremA_of_relativeLeary (hLeary : RelativeLearyFP2.{u}) : TheoremAStatement.{u} :=
  theoremA_of_lemma31_universalBases lemma_3_1 (universalBases_of_relativeLeary hLeary)

/-- The same conclusion, with the statement of Theorem A written out. -/
theorem theoremA_of_relativeLeary' (hLeary : RelativeLearyFP2.{u}) (n : ℕ) (hn : 2 ≤ n)
    (G : Type u) [Group G] [Countable G] :
    ∃ (E : Type u) (_ : Group E), IsFP n E ∧ ∃ f : G →* E, Function.Injective f :=
  theoremA_of_relativeLeary hLeary n hn G

end TheoremA
