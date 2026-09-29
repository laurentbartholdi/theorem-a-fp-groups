module

public import RequestProject.TheoremA.FP2.FiniteRelative
public import RequestProject.TheoremA.RelPres.Class

/-!
# Oracle bridge: renaming and finitely many extra relators preserve `C_R` and `FP₂`

For an `R`-enumerator `e` on `Fin n`, an alphabet renaming `ρ : Fin n → Fin m` and a finite
list `hs` of raw words on `Fin m`, the existing extended enumerator `extendEnum e ρ hs` presents
a group in `ClassCR R` (same oracle `R`), and that group is `FP₂` whenever
`PresentedGroup (enumRelators e)` is.  No totality assumption on `e` is made.
-/

@[expose] public section

namespace TheoremA

open RelPres

/-- **Oracle bridge.** If `e` is an `R`-enumerator whose presented group is `FP₂`, then for every
renaming `ρ : Fin n → Fin m` and finite list `hs` of raw words, the explicitly presented group
`PresentedGroup (enumRelators (extendEnum e ρ hs))` is in `ClassCR R` and is `FP₂`. -/
theorem classCR_isFP_two_extendEnum {R : Set ℕ} {n m : ℕ} {e : ℕ →. RawWord (Fin n)}
    (he : IsEnumerator R e) (hFP : IsFP 2 (PresentedGroup (enumRelators e)))
    (ρ : Fin n → Fin m) (hs : List (RawWord (Fin m))) :
    ClassCR R (PresentedGroup (enumRelators (extendEnum e ρ hs))) ∧
      IsFP 2 (PresentedGroup (enumRelators (extendEnum e ρ hs))) := by
  refine ⟨⟨m, extendEnum e ρ hs, he.extendEnum ρ hs, ⟨MulEquiv.refl _⟩⟩, ?_⟩
  rw [enumRelators_extendEnum]
  exact isFP_two_presentedGroup_subst_union_finite _ (FreeGroup.map ρ) _
    ((List.finite_toSet hs).image _) hFP

end TheoremA
