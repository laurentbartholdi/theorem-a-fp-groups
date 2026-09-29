module

public import RequestProject.TheoremA.FP2.WordBoundary

/-!
# Exactness of the presentation complex at degree one

Let `S ⊆ F = FreeGroup (Fin n)` be an arbitrary set of relators, `G = PresentedGroup S` and
`x_i = PresentedGroup.of i`.  With `D = wordBoundary x`, `d = genBoundary x` and
`N = relatorSpan S = span_Λ {D r | r ∈ S}`, we prove

  `ker d = N`   (`ker_genBoundary_eq_span_relatorBoundary`).

The easy inclusion `N ≤ ker d` uses `d (D r) = [q r] - 1 = 0`.  For the converse, let
`Q = M ⧸ N` and `π` the quotient map.  The free-group homomorphism `a_i ↦ (π e_i, x_i)` into the
semidirect product `Q ⋊ G` sends `u ↦ (π (D u), q u)`, hence kills `S`, and so factors through a
group homomorphism `σ : G → Q ⋊ G` (`relSection`).  Its second coordinate is the identity, so
`σ g = (δ g, g)` with a crossed homomorphism `δ : G → Q` (`relCocycle`):
`δ(g h) = δ g + [g] • δ h`, `δ x_i = π e_i`.  The `ℤ`-linear (not `Λ`-linear!) extension
`b : ℤ[G] →+ Q` of `δ` satisfies `b (d z) = π z` for all `z` (`relCocycleLin_genBoundary`),
so `d z = 0` forces `π z = 0`, i.e. `z ∈ N`.
-/

@[expose] public section

namespace TheoremA

universe u

variable {n : ℕ} (S : Set (FreeGroup (Fin n)))

/-- The canonical generators of `PresentedGroup S`. -/
abbrev presGens : Fin n → PresentedGroup S := PresentedGroup.of

/-- `FreeGroup.lift` of the canonical generators is the canonical projection. -/
theorem lift_presGens : FreeGroup.lift (presGens S) = PresentedGroup.mk S := by
  ext i; rfl

/-- The relator boundary `D r` of a relator (or any word) `r`, computed in `PresentedGroup S`. -/
noncomputable abbrev relBoundary (r : FreeGroup (Fin n)) : FreeMod (PresentedGroup S) n :=
  wordBoundary (presGens S) r

/-- `N = span_Λ {D r | r ∈ S}`, the submodule of `ℤ[G]^n` spanned by the relator boundaries. -/
noncomputable def relatorSpan : Submodule (ZG (PresentedGroup S)) (FreeMod (PresentedGroup S) n) :=
  Submodule.span (ZG (PresentedGroup S)) (relBoundary S '' S)

/-- The easy inclusion `N ≤ ker d`. -/
theorem relatorSpan_le_ker : relatorSpan S ≤ LinearMap.ker (genBoundary (presGens S)) := by
  rw [relatorSpan, Submodule.span_le]
  rintro _ ⟨r, hr, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, genBoundary_wordBoundary, lift_presGens,
    PresentedGroup.one_of_mem hr, gm1, map_one, sub_self]

/-- The quotient module `Q = ℤ[G]^n ⧸ N`. -/
abbrev RelQuot := FreeMod (PresentedGroup S) n ⧸ relatorSpan S

/-- The free-group homomorphism `a_i ↦ (π e_i, x_i)` into `Q ⋊ G`. -/
noncomputable def relQuotHom : FreeGroup (Fin n) →* BdExt (PresentedGroup S) (RelQuot S) :=
  FreeGroup.lift fun i =>
    ⟨Multiplicative.ofAdd ((relatorSpan S).mkQ (stdBasis (PresentedGroup S) i)), presGens S i⟩

/-- `relQuotHom` is the composite of `Φ` with the map induced by `π`. -/
theorem relQuotHom_eq : relQuotHom S = (BdExt.map (relatorSpan S).mkQ).comp (wordHom (presGens S)) := by
  ext i
  · simp [relQuotHom, wordHom]
  · simp [relQuotHom, wordHom]

/-- `relQuotHom u = (π (D u), q u)`. -/
theorem relQuotHom_left (u : FreeGroup (Fin n)) :
    (relQuotHom S u).left.toAdd = (relatorSpan S).mkQ (relBoundary S u) := by
  rw [relQuotHom_eq]; rfl

theorem relQuotHom_right (u : FreeGroup (Fin n)) :
    (relQuotHom S u).right = PresentedGroup.mk S u := by
  rw [relQuotHom_eq, MonoidHom.comp_apply, BdExt.map_right, right_wordHom, lift_presGens]

/-- `relQuotHom` kills every relator. -/
theorem relQuotHom_rel : ∀ r ∈ S, FreeGroup.lift (fun i =>
    (⟨Multiplicative.ofAdd ((relatorSpan S).mkQ (stdBasis (PresentedGroup S) i)), presGens S i⟩ :
      BdExt (PresentedGroup S) (RelQuot S))) r = 1 := by
  intro r hr
  change relQuotHom S r = 1
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd (relQuotHom S r).left.toAdd = Multiplicative.ofAdd 0
    rw [relQuotHom_left, Submodule.mkQ_apply]
    congr 1
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨r, hr, rfl⟩
  · rw [relQuotHom_right, PresentedGroup.one_of_mem hr]; rfl

/-- **The section** `σ : G →* Q ⋊ G`, obtained from the universal property of the presentation. -/
noncomputable def relSection : PresentedGroup S →* BdExt (PresentedGroup S) (RelQuot S) :=
  PresentedGroup.toGroup (relQuotHom_rel S)

/-- The second coordinate of `σ` is the identity. -/
theorem relSection_right (g : PresentedGroup S) : (relSection S g).right = g := by
  have : SemidirectProduct.rightHom.comp (relSection S) = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro i
    simp [relSection, PresentedGroup.toGroup.of]
  exact DFunLike.congr_fun this g

/-- **The crossed homomorphism** `δ : G → Q`, the first coordinate of `σ`. -/
noncomputable def relCocycle (g : PresentedGroup S) : RelQuot S :=
  (relSection S g).left.toAdd

/-- `δ(g h) = δ g + [g] • δ h`. -/
theorem relCocycle_mul (g h : PresentedGroup S) :
    relCocycle S (g * h) = relCocycle S g + MonoidAlgebra.of ℤ _ g • relCocycle S h := by
  simp only [relCocycle, map_mul, BdExt.left_mul, relSection_right]

theorem relCocycle_one : relCocycle S 1 = 0 := by
  simp [relCocycle]

/-- `δ x_i = π e_i`. -/
theorem relCocycle_gen (i : Fin n) :
    relCocycle S (presGens S i) = (relatorSpan S).mkQ (stdBasis (PresentedGroup S) i) := by
  simp [relCocycle, relSection, PresentedGroup.toGroup.of]

/-- The `ℤ`-linear extension `b : ℤ[G] →+ Q` of `δ`.  It is **not** `ℤ[G]`-linear in general. -/
noncomputable def relCocycleLin : ZG (PresentedGroup S) →+ RelQuot S :=
  Finsupp.liftAddHom fun g => (zmultiplesHom (RelQuot S) (relCocycle S g))

theorem relCocycleLin_single (g : PresentedGroup S) (m : ℤ) :
    relCocycleLin S (MonoidAlgebra.single g m) = m • relCocycle S g := by
  exact (Finsupp.liftAddHom_apply_single _ g m).trans (zmultiplesHom_apply _ _ m)

/-- **Key identity** `b (d z) = π z`. -/
theorem relCocycleLin_genBoundary (z : FreeMod (PresentedGroup S) n) :
    relCocycleLin S (genBoundary (presGens S) z) = (relatorSpan S).mkQ z := by
  classical
  have hz : z = ∑ i, Pi.single i (z i) := (Finset.univ_sum_single z).symm
  rw [hz, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  induction z i using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a c ha hc =>
    rw [Pi.single_add, map_add, map_add, map_add, ha, hc]
  | single g m =>
    have hsingle : (Pi.single i (MonoidAlgebra.single g m) : FreeMod (PresentedGroup S) n) =
        (MonoidAlgebra.single g m : ZG (PresentedGroup S)) • stdBasis (PresentedGroup S) i := by
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    have hd : genBoundary (presGens S) (Pi.single i (MonoidAlgebra.single g m)) =
        MonoidAlgebra.single (g * presGens S i) m - MonoidAlgebra.single g m := by
      rw [hsingle, map_smul, genBoundary_single, gm1, smul_eq_mul, mul_sub, mul_one,
        MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one]
    have hsm : (MonoidAlgebra.single g m : ZG (PresentedGroup S)) =
        m • MonoidAlgebra.of ℤ _ g := by
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
    rw [hd, map_sub, relCocycleLin_single, relCocycleLin_single, relCocycle_mul, relCocycle_gen,
      hsingle, map_smul, hsm, smul_assoc, smul_add, add_sub_cancel_left]

/-- **Exactness at degree one.** For `G = PresentedGroup S` with its canonical generators,
`ker (genBoundary x) = span_Λ {D r | r ∈ S}`. -/
theorem ker_genBoundary_eq_span_relatorBoundary :
    LinearMap.ker (genBoundary (presGens S)) =
      Submodule.span (ZG (PresentedGroup S)) (wordBoundary (presGens S) '' S) := by
  refine le_antisymm (fun z hz => ?_) (relatorSpan_le_ker S)
  have h := relCocycleLin_genBoundary S z
  rw [LinearMap.mem_ker.mp hz, map_zero, eq_comm, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at h
  exact h

end TheoremA
