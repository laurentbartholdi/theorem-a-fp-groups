module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Data.Countable.Defs
public import Mathlib.GroupTheory.GroupAction.Ring

set_option backward.isDefEq.respectTransparency false

@[expose] public section

/-!
# Theorem A

For every finite integer `n >= 2`, every countable group embeds in a group of
type `FP_n` over the integers. The definition below spells out `FP_n` as a
finite-rank free partial resolution of the trivial integral module; it is
duplicated verbatim from the proof project so this claim has only an approved
Mathlib import.
-/

universe u

namespace TheoremA

/-- The free left `ℤ[G]`-module of rank `k`. -/
abbrev FreeMod (G : Type*) [Group G] (k : ℕ) := Fin k → MonoidAlgebra ℤ G

/-- Type `FP_n` over `ℤ`, expressed by an exact finite-rank free partial resolution. -/
def IsFP (n : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ (c : ℕ → ℕ)
    (d : ∀ i, FreeMod G (c (i + 1)) →ₗ[MonoidAlgebra ℤ G] FreeMod G (c i))
    (ε : FreeMod G (c 0) →+ ℤ),
    (∀ (g : G) (x : FreeMod G (c 0)), ε (MonoidAlgebra.of ℤ G g • x) = ε x) ∧
    Function.Surjective ε ∧
    (0 < n → ε.ker = (LinearMap.range (d 0)).toAddSubgroup) ∧
    (∀ i, i + 1 < n → LinearMap.ker (d i) = LinearMap.range (d (i + 1)))

/-- **Theorem A.** Every countable group embeds in a group of type `FP_n` for each finite `n >= 2`. -/
theorem palomarStatement (n : ℕ) (hn : 2 ≤ n)
    (G : Type u) [Group G] [Countable G] :
    ∃ (E : Type u) (_ : Group E),
      IsFP n E ∧ ∃ f : G →* E, Function.Injective f := by
  sorry

end TheoremA
