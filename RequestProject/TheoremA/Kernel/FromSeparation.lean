module

public import RequestProject.TheoremA.Kernel.Enum
public import RequestProject.TheoremA.Groups.LearyAssembly

/-!
# The conditional checkpoint: `FlagSeparation → KernelHB → Theorem A`

* `kernelHB_of_flagSeparation : FlagSeparation → KernelHB` — the exact existing `KernelHB`;
* `relativeLeary_of_flagSeparation`, `universalBases_of_flagSeparation`,
  `theoremA_of_flagSeparation` — via the already proved `relativeLeary_of_kernelHB`,
  `universalBases_of_relativeLeary` and `theoremA_of_relativeLeary`.

None of these calls the constants `universalBases` or `theoremA` of `Main.lean`.  `FlagSeparation`
is an explicit hypothesis here; it is proved as `Leary.flagSeparation` in `Leary/Detection.lean`,
and the unconditional instances are in `Kernel/Unconditional.lean`.
-/

@[expose] public section

namespace TheoremA

open RelPres Kernel Leary

universe u

/-- **Benignness of two-generator kernels from separation.** -/
theorem kernelHB_of_flagSeparation (hSep : FlagSeparation) : KernelHB := by
  intro R e he
  haveI : (Subgroup.normalClosure (enumRelators e)).Normal := Subgroup.normalClosure_normal
  exact hb_of_codeSet hSep _ (intEnumerable_codeSet he)

/-- **The relative Leary theorem from separation.** -/
theorem relativeLeary_of_flagSeparation (hSep : FlagSeparation) : RelativeLearyFP2.{u} :=
  relativeLeary_of_kernelHB (kernelHB_of_flagSeparation hSep)

/-- **Universal bases from separation.** -/
theorem universalBases_of_flagSeparation (hSep : FlagSeparation) : UniversalBases.{u} :=
  universalBases_of_relativeLeary (relativeLeary_of_flagSeparation hSep)

/-- **Theorem A from separation.** -/
theorem theoremA_of_flagSeparation (hSep : FlagSeparation) : TheoremAStatement.{u} :=
  theoremA_of_relativeLeary (relativeLeary_of_flagSeparation hSep)

end TheoremA
