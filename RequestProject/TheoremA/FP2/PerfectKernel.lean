module

public import RequestProject.TheoremA.FP2.FiniteRelative

/-!
# Quotients by perfect normal subgroups preserve `FP₂`

For `F = FreeGroup (Fin n)`, relators `S ⊆ F`, `G = PresentedGroup S` and word boundaries
`D = wordBoundary x` computed in `G`:

* `wordBoundary_mem_span_of_mem_normalClosure` — if every word of `T` is trivial in `G`, then
  `D u ∈ span (D '' T)` for every `u` in the normal closure of `T`;
* `wordBoundary_eq_zero_of_mem_commutator` — `D u = 0` for every `u ∈ ⁅K, K⁆`, where `K` is the
  kernel of `F → G`;
* `isFP_two_presentedGroup_of_subset_sup_commutator` — if `T ⊆ S` is finite and every relator of
  `S` lies in `⟨⟨T⟩⟩ ⊔ ⁅⟨⟨S⟩⟩, ⟨⟨S⟩⟩⁆`, then `PresentedGroup S` is `FP₂`;
* `isFP_two_presentedGroup_of_perfect_extension` — relative form: if `S₀ ⊆ S`,
  `PresentedGroup S₀` is `FP₂` and every relator of `S` lies in `⟨⟨S₀⟩⟩ ⊔ ⁅⟨⟨S⟩⟩, ⟨⟨S⟩⟩⁆`, then
  `PresentedGroup S` is `FP₂`;

The group form (`isFP_two_quotient_of_perfect`) is in `PerfectQuotient.lean`.
-/

@[expose] public section

namespace TheoremA

variable {n : ℕ}

section Boundary

variable {G : Type*} [Group G] (x : Fin n → G)

theorem wordBoundary_mul_of_lift_eq_one {u : FreeGroup (Fin n)} (w : FreeGroup (Fin n))
    (hu : FreeGroup.lift x u = 1) :
    wordBoundary x (u * w) = wordBoundary x u + wordBoundary x w := by
  rw [wordBoundary_mul, hu, map_one, one_smul]

theorem wordBoundary_inv_of_lift_eq_one {u : FreeGroup (Fin n)} (hu : FreeGroup.lift x u = 1) :
    wordBoundary x u⁻¹ = -wordBoundary x u := by
  rw [wordBoundary_inv, hu, inv_one, map_one, one_smul]

/-- The boundary of a commutator of two words that are trivial in `G` vanishes. -/
theorem wordBoundary_commutator_of_lift_eq_one {u w : FreeGroup (Fin n)}
    (hu : FreeGroup.lift x u = 1) (hw : FreeGroup.lift x w = 1) :
    wordBoundary x ⁅u, w⁆ = 0 := by
  have hu' : FreeGroup.lift x u⁻¹ = 1 := by rw [map_inv, hu, inv_one]
  have hw' : FreeGroup.lift x w⁻¹ = 1 := by rw [map_inv, hw, inv_one]
  have huw : FreeGroup.lift x (u * w) = 1 := by rw [map_mul, hu, hw, one_mul]
  have huwu : FreeGroup.lift x (u * w * u⁻¹) = 1 := by rw [map_mul, huw, hu', one_mul]
  rw [commutatorElement_def, wordBoundary_mul_of_lift_eq_one x _ huwu,
    wordBoundary_mul_of_lift_eq_one x _ huw, wordBoundary_mul_of_lift_eq_one x _ hu,
    wordBoundary_inv_of_lift_eq_one x hu, wordBoundary_inv_of_lift_eq_one x hw]
  abel

/-- If every word of `T` is trivial in `G`, the boundary of any element of the normal closure of
`T` lies in the span of the boundaries of `T`. -/
theorem wordBoundary_mem_span_of_mem_normalClosure (T : Set (FreeGroup (Fin n)))
    (hT : ∀ r ∈ T, FreeGroup.lift x r = 1) {u : FreeGroup (Fin n)}
    (hu : u ∈ Subgroup.normalClosure T) :
    wordBoundary x u ∈ Submodule.span (ZG G) (wordBoundary x '' T) := by
  have hker : Subgroup.normalClosure T ≤ (FreeGroup.lift x).ker :=
    Subgroup.normalClosure_le_normal (fun r hr => (FreeGroup.lift x).mem_ker.2 (hT r hr))
  rw [Subgroup.normalClosure] at hu hker
  induction hu using Subgroup.closure_induction with
  | mem v hv =>
    obtain ⟨r, hr, hc⟩ := Group.mem_conjugatesOfSet_iff.1 hv
    obtain ⟨c, rfl⟩ := isConj_iff.1 hc
    rw [wordBoundary_conj x c (hT r hr)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, hr, rfl⟩)
  | one => simp
  | mul a b ha hb iha ihb =>
    rw [wordBoundary_mul_of_lift_eq_one x _ ((FreeGroup.lift x).mem_ker.1 (hker ha))]
    exact Submodule.add_mem _ iha ihb
  | inv a ha iha =>
    rw [wordBoundary_inv_of_lift_eq_one x ((FreeGroup.lift x).mem_ker.1 (hker ha))]
    exact Submodule.neg_mem _ iha

theorem commutator_le_ker (K : Subgroup (FreeGroup (Fin n)))
    (hK : K ≤ (FreeGroup.lift x).ker) : ⁅K, K⁆ ≤ (FreeGroup.lift x).ker :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [MonoidHom.mem_ker, map_commutatorElement, (FreeGroup.lift x).mem_ker.1 (hK ha),
      (FreeGroup.lift x).mem_ker.1 (hK hb), commutatorElement_one_left]

/-- The boundary vanishes on the commutator subgroup `⁅K, K⁆` of any subgroup `K` of words that
are trivial in `G`. -/
theorem wordBoundary_eq_zero_of_mem_commutator (K : Subgroup (FreeGroup (Fin n)))
    (hK : K ≤ (FreeGroup.lift x).ker) {u : FreeGroup (Fin n)} (hu : u ∈ ⁅K, K⁆) :
    wordBoundary x u = 0 := by
  have hle : ⁅K, K⁆ ≤ (FreeGroup.lift x).ker := commutator_le_ker x K hK
  rw [Subgroup.commutator_def] at hu hle
  induction hu using Subgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hv
    exact wordBoundary_commutator_of_lift_eq_one x ((FreeGroup.lift x).mem_ker.1 (hK ha))
      ((FreeGroup.lift x).mem_ker.1 (hK hb))
  | one => simp
  | mul a b ha hb iha ihb =>
    rw [wordBoundary_mul_of_lift_eq_one x _ ((FreeGroup.lift x).mem_ker.1 (hle ha)), iha, ihb,
      add_zero]
  | inv a ha iha =>
    rw [wordBoundary_inv_of_lift_eq_one x ((FreeGroup.lift x).mem_ker.1 (hle ha)), iha, neg_zero]

/-- If every word of `T` is trivial in `G` and `K` consists of words trivial in `G`, then the
boundary of every element of `⟨⟨T⟩⟩ ⊔ ⁅K, K⁆` lies in the span of the boundaries of `T`. -/
theorem wordBoundary_mem_span_of_mem_sup_commutator (T : Set (FreeGroup (Fin n)))
    (hT : ∀ r ∈ T, FreeGroup.lift x r = 1) (K : Subgroup (FreeGroup (Fin n)))
    (hK : K ≤ (FreeGroup.lift x).ker) {u : FreeGroup (Fin n)}
    (hu : u ∈ Subgroup.normalClosure T ⊔ ⁅K, K⁆) :
    wordBoundary x u ∈ Submodule.span (ZG G) (wordBoundary x '' T) := by
  let W : Subgroup (FreeGroup (Fin n)) :=
    { carrier := {u | FreeGroup.lift x u = 1 ∧
        wordBoundary x u ∈ Submodule.span (ZG G) (wordBoundary x '' T)}
      one_mem' := ⟨map_one _, by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul, ha.1, hb.1, one_mul], by
        rw [wordBoundary_mul_of_lift_eq_one x _ ha.1]; exact Submodule.add_mem _ ha.2 hb.2⟩
      inv_mem' := fun {a} ha => ⟨by rw [map_inv, ha.1, inv_one], by
        rw [wordBoundary_inv_of_lift_eq_one x ha.1]; exact Submodule.neg_mem _ ha.2⟩ }
  have h1 : Subgroup.normalClosure T ≤ W := fun v hv =>
    ⟨(FreeGroup.lift x).mem_ker.1 (Subgroup.normalClosure_le_normal
        (fun r hr => (FreeGroup.lift x).mem_ker.2 (hT r hr)) hv),
      wordBoundary_mem_span_of_mem_normalClosure x T hT hv⟩
  have h2 : ⁅K, K⁆ ≤ W := fun v hv =>
    ⟨(FreeGroup.lift x).mem_ker.1 (commutator_le_ker x K hK hv), by
      rw [wordBoundary_eq_zero_of_mem_commutator x K hK hv]; exact Submodule.zero_mem _⟩
  exact (sup_le h1 h2 hu).2

end Boundary

/-- The kernel of `F → PresentedGroup S` is the normal closure of `S`. -/
theorem ker_lift_presGens (S : Set (FreeGroup (Fin n))) :
    (FreeGroup.lift (presGens S)).ker = Subgroup.normalClosure S := by
  rw [lift_presGens]
  exact QuotientGroup.ker_mk' _

/-- **Perfect-kernel criterion for `FP₂`.** If `T ⊆ S` is finite and every relator of `S` lies in
`⟨⟨T⟩⟩ ⊔ ⁅⟨⟨S⟩⟩, ⟨⟨S⟩⟩⁆` (i.e. the image of `⟨⟨S⟩⟩` in `PresentedGroup T` is perfect), then
`PresentedGroup S` is `FP₂`. -/
theorem isFP_two_presentedGroup_of_subset_sup_commutator (S T : Set (FreeGroup (Fin n)))
    (hT : T.Finite) (hTS : T ⊆ S)
    (h : S ⊆ (Subgroup.normalClosure T ⊔
      ⁅Subgroup.normalClosure S, Subgroup.normalClosure S⁆ : Subgroup (FreeGroup (Fin n)))) :
    IsFP 2 (PresentedGroup S) := by
  have hker := (ker_lift_presGens S).symm.le
  have hT1 : ∀ r ∈ T, FreeGroup.lift (presGens S) r = 1 := fun r hr =>
    (FreeGroup.lift (presGens S)).mem_ker.1 (hker (Subgroup.subset_normalClosure (hTS hr)))
  refine (isFP_two_iff_all_relator_boundaries_mem_finite_span S).2 ⟨T, hT, hTS, fun r hr => ?_⟩
  exact wordBoundary_mem_span_of_mem_sup_commutator _ T hT1 _ hker (h hr)

/-- **Quotients by perfect normal subgroups, relative form.** If `S₀ ⊆ S`, `PresentedGroup S₀`
is `FP₂`, and every relator of `S` lies in `⟨⟨S₀⟩⟩ ⊔ ⁅⟨⟨S⟩⟩, ⟨⟨S⟩⟩⁆`, then `PresentedGroup S`
is `FP₂`.  (Here `S₀` may be infinite.) -/
theorem isFP_two_presentedGroup_of_perfect_extension (S₀ S : Set (FreeGroup (Fin n)))
    (hS₀S : S₀ ⊆ S) (hS₀ : IsFP 2 (PresentedGroup S₀))
    (h : S ⊆ (Subgroup.normalClosure S₀ ⊔
      ⁅Subgroup.normalClosure S, Subgroup.normalClosure S⁆ : Subgroup (FreeGroup (Fin n)))) :
    IsFP 2 (PresentedGroup S) := by
  obtain ⟨T, hTfin, hTS₀, hT⟩ := (isFP_two_iff_all_relator_boundaries_mem_finite_span S₀).1 hS₀
  have hid : ∀ r ∈ S₀, (MonoidHom.id (FreeGroup (Fin n))) r ∈ S := fun r hr => hS₀S hr
  have hT' : ∀ r ∈ S₀, wordBoundary (presGens S) r ∈
      Submodule.span (ZG (PresentedGroup S)) (wordBoundary (presGens S) '' T) := by
    intro r hr
    have := relatorBoundary_subst_mem_span (MonoidHom.id _) hid T hT hr
    simpa using this
  have hker := (ker_lift_presGens S).symm.le
  have hS₀1 : ∀ r ∈ S₀, FreeGroup.lift (presGens S) r = 1 := fun r hr =>
    (FreeGroup.lift (presGens S)).mem_ker.1 (hker (Subgroup.subset_normalClosure (hS₀S hr)))
  refine (isFP_two_iff_all_relator_boundaries_mem_finite_span S).2
    ⟨T, hTfin, hTS₀.trans hS₀S, fun r hr => ?_⟩
  have h1 := wordBoundary_mem_span_of_mem_sup_commutator _ S₀ hS₀1 _ hker (h hr)
  refine Submodule.span_le.2 ?_ h1
  rintro _ ⟨s, hs, rfl⟩
  exact hT' s hs

end TheoremA
