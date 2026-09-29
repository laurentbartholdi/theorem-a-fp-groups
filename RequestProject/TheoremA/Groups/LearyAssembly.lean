module

public import RequestProject.TheoremA.Conditional
public import RequestProject.TheoremA.Groups.RopePres

/-!
# Relative Leary theorem from benignness of two-generator kernels

`KernelHB` is the statement that for every oracle `R` and every `R`-enumerator `e` on the
alphabet `Fin 2`, the normal closure of the enumerated relators is `HB_R` in `FreeGroup (Fin 2)`.

`relativeLeary_of_kernelHB : KernelHB → RelativeLearyFP2` is proved: embed `H` in `V_R`
(an explicit two-letter `R`-enumerated presentation), then apply the same-oracle rope trick.
`KernelHB` itself is the relative form of [Leary 2018, Corollary 2.6]; it is **not** proved here.
-/

@[expose] public section

namespace TheoremA

open RelPres

universe u

/-- **Benignness of two-generator kernels** (a hypothesis in this module). -/
def KernelHB : Prop :=
  ∀ (R : Set ℕ) (e : ℕ →. RawWord (Fin 2)), IsEnumerator R e →
    HB R (Subgroup.normalClosure (enumRelators e))

/-- `V_R` embeds in a group of `C_R` of type `FP₂` in universe `0`, given benignness of its
kernel. -/
theorem exists_suitable_VR (R : Set ℕ)
    (h : HB R (Subgroup.normalClosure (enumRelators (twoGenEnum (omegaEnum R))))) :
    ∃ (K : Type) (_ : Group K), ClassCR R K ∧ IsFP 2 K ∧
      ∃ g : VR R →* K, Function.Injective g :=
  rope_trick _ h

/-- **The relative Leary theorem from `KernelHB`.** -/
theorem relativeLeary_of_kernelHB (h : KernelHB) : RelativeLearyFP2.{u} := by
  intro R H _ hH
  obtain ⟨f, hf⟩ := hH.exists_injective_hom_VR
  obtain ⟨K, _, hKC, hKF, g, hg⟩ :=
    exists_suitable_VR R (h R _ (isNatEnumerator_omegaEnum.twoGenEnum))
  obtain ⟨n, e, he, ⟨ψ⟩⟩ := hKC
  let up : K →* ULift.{u} K := MulEquiv.ulift.symm.toMonoidHom
  exact ⟨ULift.{u} K, inferInstance, ⟨n, e, he, ⟨ψ.trans MulEquiv.ulift.symm⟩⟩,
    IsFP.of_mulEquiv MulEquiv.ulift.symm hKF, (up.comp g).comp f,
    (MulEquiv.ulift.symm.injective.comp hg).comp hf⟩

end TheoremA
