module

public import RequestProject.TheoremA.Homological.L42.Lemma42
public import RequestProject.TheoremA.Homological.Prop51
public import RequestProject.TheoremA.Lemma31.Geometric

/-!
# Proved ingredients of Theorem A

`lemma_3_1`, `lemma_4_2`, `proposition_5_1`, `corollary_5_2` and the conditional assembly
`theoremA_of_lemma31_universalBases` (all proved without `sorry`).  They are kept in this module,
below `Conditional.lean`, so that the final assembly in `Main.lean` can import the relative Leary
theorem without an import cycle.
-/

@[expose] public section

namespace TheoremA

universe u

/-- **Lemma 3.1** (proved: `lemma31`, from the nonexistence of nonidentity defect pictures in
non-positively curved cone complexes of groups). -/
theorem lemma_3_1 : Lemma31.{u} :=
  lemma31

/-- **Lemma 4.2** (proved: `lemma42`). -/
theorem lemma_4_2 : Lemma42.{u} := lemma42

/-- **Proposition 5.1** (proved: `prop51`). -/
theorem proposition_5_1 : Prop51.{u} := prop51

/-- **Corollary 5.2**, from Lemma 4.2 (via Corollary 4.3) and Proposition 5.1 (proved). -/
theorem corollary_5_2 : Corollary52.{u} :=
  corollary52_of (cor43_of_lemma42 lemma_4_2) proposition_5_1

/-- **Theorem A, conditional form** (proved without `sorry`): Theorem A holds as soon as Lemma 3.1
and the universal-bases statement hold.  All other ingredients (Proposition 2.1, Corollary 5.2,
Proposition 7.1 and §7) are proved. -/
theorem theoremA_of_lemma31_universalBases (h31 : Lemma31.{u}) (hU : UniversalBases.{u}) :
    TheoremAStatement.{u} :=
  theoremA_of_ingredients h31 corollary_5_2 hU

end TheoremA
