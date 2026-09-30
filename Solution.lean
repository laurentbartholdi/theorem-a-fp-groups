module

public import RequestProject.TheoremA.Fano

set_option backward.isDefEq.respectTransparency false

@[expose] public section

/-!
# Theorem A solution

This module exposes the proved version of the Challenge declaration. Its
statement is definitionally the same as the project's existing `IsFP` result.
-/

universe u

/-- The proved solution to `TheoremA.palomarStatement`. -/
theorem TheoremA.palomarStatement (n : ℕ) (hn : 2 ≤ n)
    (G : Type u) [Group G] [Countable G] :
    ∃ (E : Type u) (_ : Group E),
      TheoremA.IsFP n E ∧ ∃ f : G →* E, Function.Injective f :=
  TheoremA.Fano.theoremA n hn G
