module

public import RequestProject.TheoremA.Lemma31.Picture.Surgery

/-!
# Boundary consolidation

Let `d ≠ e` be consecutive darts at the marked vertex (`σ d = e`), with `e` not the base dart,
labelled `d : ⟨k, g₁⟩` and `e : ⟨k, g₂⟩` from the **same** local group `k`
(`RawPicture.MarkedPair`).  Put `u = α d`, `v = α e`; they are ordinary darts with labels
`⟨k, g₁⁻¹⟩`, `⟨k, g₂⁻¹⟩`.  In both moves the darts `e, v` (one edge) are deleted, `d` is relabelled
`⟨k, g₁ g₂⟩` and `u` is relabelled `⟨k, (g₁ g₂)⁻¹⟩`; all other labels are kept
(`MarkedPair.lab'`).  No assumption `g₁ g₂ ≠ 1` is made.

* **Distinct endpoints** (`MarkedPair.consolidate`, Section 2 of the task): if `u`, `v` lie at
  different vertices, the rotation is `erase_{e,v}(swap u v * σ)` (the two ordinary vertices are
  merged, then `e, v` erased).  `V' = V - 1`, `E' = E - 1`, `F' = F`, connected, `χ = 2`
  (`consolidate_numVertices`, `consolidate_numEdges`, `consolidate_numFaces`).
* **Marked digon** (`MarkedPair.consolidateDigon`, Section 3): if `σ v = u`, the rotation is
  `erase_{e,v}(σ)`.  `V' = V`, `E' = E - 1`, `F' = F - 1`, connected, `χ = 2`.

In both cases the result is a raw picture for the **same** element with the **same** base dart
(the marked word changes only by replacing the adjacent letters `g₁, g₂` by `g₁ g₂`).

The faces of the new map are given exactly by `CombMap.eraseEdge_φ_val`: the face permutation is
the first-return map of `swap e v * π * α` to the retained darts, `π` being the rotation before
erasure.
-/

@[expose] public section

namespace TheoremA

universe u w

namespace ConeComplex

open Picture Equiv Function

variable {V T : Type w} {C : ConeComplex.{u, w} V T} {x : Monoid.CoprodI C.loc}

/-- Two distinct consecutive darts `d, e = σ d` at the marked vertex, `e` not the base dart,
whose letters `⟨k, g₁⟩`, `⟨k, g₂⟩` lie in the same local group. -/
structure RawPicture.MarkedPair (R : C.RawPicture x) where
  d : R.M.D
  e : R.M.D
  k : V ⊕ T
  g₁ : C.loc k
  g₂ : C.loc k
  marked : R.M.σ.SameCycle R.base d
  next : R.M.σ d = e
  ne : d ≠ e
  ne_base : e ≠ R.base
  lab_d : R.lab d = ⟨k, g₁⟩
  lab_e : R.lab e = ⟨k, g₂⟩

namespace RawPicture.MarkedPair

variable {R : C.RawPicture x} (P : R.MarkedPair)

/-- The ordinary partner of `d`. -/
def u : R.M.D := R.M.α P.d

/-- The ordinary partner of `e`. -/
def v : R.M.D := R.M.α P.e

theorem α_e : R.M.α P.e = P.v := rfl

theorem α_v : R.M.α P.v = P.e := R.M.α_α _

theorem α_d : R.M.α P.d = P.u := rfl

theorem α_u : R.M.α P.u = P.d := R.M.α_α _

theorem marked_e : R.M.σ.SameCycle R.base P.e :=
  P.marked.trans ⟨1, by simpa using P.next⟩

theorem not_marked_u : ¬ R.M.σ.SameCycle R.base P.u := (R.edge_boundary P.d P.marked).1

theorem not_marked_v : ¬ R.M.σ.SameCycle R.base P.v := (R.edge_boundary P.e P.marked_e).1

theorem d_ne_u : P.d ≠ P.u := fun h => P.not_marked_u (h ▸ P.marked)

theorem d_ne_v : P.d ≠ P.v := fun h => P.not_marked_v (h ▸ P.marked)

theorem e_ne_u : P.e ≠ P.u := fun h => P.not_marked_u (h ▸ P.marked_e)

theorem e_ne_v : P.e ≠ P.v := fun h => P.not_marked_v (h ▸ P.marked_e)

theorem u_ne_v : P.u ≠ P.v := fun h => P.ne (R.M.α.injective h)

theorem ne_α_e : P.e ≠ R.M.α P.e := P.e_ne_v

theorem base_ne_u : R.base ≠ P.u := fun h => P.not_marked_u (h ▸ Perm.SameCycle.refl _ _)

theorem base_ne_v : R.base ≠ P.v := fun h => P.not_marked_v (h ▸ Perm.SameCycle.refl _ _)

theorem not_marked_of_u {z : R.M.D} (hz : R.M.σ.SameCycle P.u z) :
    ¬ R.M.σ.SameCycle R.base z := fun h => P.not_marked_u (h.trans hz.symm)

theorem not_marked_of_v {z : R.M.D} (hz : R.M.σ.SameCycle P.v z) :
    ¬ R.M.σ.SameCycle R.base z := fun h => P.not_marked_v (h.trans hz.symm)

theorem σe_ne_e : R.M.σ P.e ≠ P.e := fun h => P.ne (R.M.σ.injective (P.next.trans h.symm))

theorem marked_σ {z : R.M.D} (hz : R.M.σ.SameCycle R.base z) :
    R.M.σ.SameCycle R.base (R.M.σ z) := hz.trans ⟨1, by simp⟩

theorem lab_u : R.lab P.u = ⟨P.k, P.g₁⁻¹⟩ := by
  rw [u, (R.edge_boundary P.d P.marked).2, P.lab_d]; rfl

theorem lab_v : R.lab P.v = ⟨P.k, P.g₂⁻¹⟩ := by
  rw [v, (R.edge_boundary P.e P.marked_e).2, P.lab_e]; rfl

/-- The labels after consolidation. -/
def lab' : R.M.D → C.Letter := fun z =>
  if z = P.d then ⟨P.k, P.g₁ * P.g₂⟩ else if z = P.u then ⟨P.k, (P.g₁ * P.g₂)⁻¹⟩
  else if z = P.e ∨ z = P.v then ⟨P.k, 1⟩ else R.lab z

theorem lab'_d : P.lab' P.d = ⟨P.k, P.g₁ * P.g₂⟩ := by simp [lab']

theorem lab'_u : P.lab' P.u = ⟨P.k, (P.g₁ * P.g₂)⁻¹⟩ := by
  simp [lab', P.d_ne_u.symm]

theorem lab'_e : P.lab' P.e = ⟨P.k, 1⟩ := by
  simp [lab', P.ne.symm, P.e_ne_u]

theorem lab'_v : P.lab' P.v = ⟨P.k, 1⟩ := by
  simp [lab', P.d_ne_v.symm, P.u_ne_v.symm]

theorem lab'_of_ne {z : R.M.D} (h1 : z ≠ P.d) (h2 : z ≠ P.u) (h3 : z ≠ P.e) (h4 : z ≠ P.v) :
    P.lab' z = R.lab z := by
  simp [lab', h1, h2, h3, h4]

theorem lab'_fst (z : R.M.D) : (P.lab' z).1 = (R.lab z).1 := by
  by_cases h1 : z = P.d
  · rw [h1, lab'_d, P.lab_d]
  by_cases h2 : z = P.u
  · rw [h2, lab'_u, P.lab_u]
  by_cases h3 : z = P.e
  · rw [h3, lab'_e, P.lab_e]
  by_cases h4 : z = P.v
  · rw [h4, lab'_v, P.lab_v]
  rw [P.lab'_of_ne h1 h2 h3 h4]

theorem word_e : C.letterWord (P.lab' P.e) = 1 := by
  rw [lab'_e]; exact map_one _

theorem word_v : C.letterWord (P.lab' P.v) = 1 := by
  rw [lab'_v]; exact map_one _

/-- The marked word is unchanged by the relabelling (the adjacent letters `g₁, g₂` become
`g₁ g₂, 1`). -/
theorem cycleWord_lab'_base :
    cycleWord R.M.σ (C.letterWord ∘ P.lab') R.base = x := by
  refine Eq.trans ?_ R.boundary_word
  refine cycleWord_merge_consecutive (d := P.d) (by rw [P.next]; exact P.ne.symm)
    P.marked.symm (by rw [P.next]; exact P.ne_base.symm) (fun y hy hyd hye => ?_) ?_
  · rw [P.next] at hye
    have hym : R.M.σ.SameCycle R.base y := P.marked.trans hy
    simp only [Function.comp_apply]
    rw [P.lab'_of_ne hyd (fun h => P.not_marked_u (h ▸ hym)) hye
      (fun h => P.not_marked_v (h ▸ hym))]
  · simp only [Function.comp_apply, P.next]
    rw [P.lab'_d, P.lab'_e, P.lab_d, P.lab_e]
    simp [letterWord, map_mul]

/-- Boundary edges after relabelling (at a marked dart other than `e`). -/
theorem edge_boundary_lab' {z : R.M.D} (hz : R.M.σ.SameCycle R.base z) (hze : z ≠ P.e) :
    ¬ R.M.σ.SameCycle R.base (R.M.α z) ∧ P.lab' (R.M.α z) = (P.lab' z).inv := by
  refine ⟨(R.edge_boundary z hz).1, ?_⟩
  by_cases hzd : z = P.d
  · rw [hzd, α_d, lab'_u, lab'_d]; rfl
  have hzu : z ≠ P.u := fun h => P.not_marked_u (h ▸ hz)
  have hzv : z ≠ P.v := fun h => P.not_marked_v (h ▸ hz)
  have h1 : R.M.α z ≠ P.d := fun h => hzu (by rw [← R.M.α_α z, h]; rfl)
  have h2 : R.M.α z ≠ P.u := fun h => hzd (R.M.α.injective h)
  have h3 : R.M.α z ≠ P.e := fun h => hzv (by rw [← R.M.α_α z, h]; rfl)
  have h4 : R.M.α z ≠ P.v := fun h => hze (R.M.α.injective h)
  rw [P.lab'_of_ne h1 h2 h3 h4, P.lab'_of_ne hzd hzu hze hzv]
  exact (R.edge_boundary z hz).2

/-- Interior edges after relabelling. -/
theorem edge_interior_lab' {z : R.M.D} (hz : ¬ R.M.σ.SameCycle R.base z)
    (hz' : ¬ R.M.σ.SameCycle R.base (R.M.α z)) :
    C.RelEdge (P.lab' z) (P.lab' (R.M.α z)) ∨ C.RelEdge (P.lab' (R.M.α z)) (P.lab' z) := by
  have hzd : z ≠ P.d := fun h => hz (h ▸ P.marked)
  have hze : z ≠ P.e := fun h => hz (h ▸ P.marked_e)
  have hzu : z ≠ P.u := fun h => hz' (by rw [h, α_u]; exact P.marked)
  have hzv : z ≠ P.v := fun h => hz' (by rw [h, α_v]; exact P.marked_e)
  have h1 : R.M.α z ≠ P.d := fun h => hz' (h ▸ P.marked)
  have h2 : R.M.α z ≠ P.u := fun h => hzd (R.M.α.injective h)
  have h3 : R.M.α z ≠ P.e := fun h => hz' (h ▸ P.marked_e)
  have h4 : R.M.α z ≠ P.v := fun h => hze (R.M.α.injective h)
  rw [P.lab'_of_ne h1 h2 h3 h4, P.lab'_of_ne hzd hzu hze hzv]
  exact R.edge_interior z hz hz'

/-- The letter types at interior darts of the `u`-vertex and the `v`-vertex are `k`. -/
theorem type_of_u {z : R.M.D} (hz : R.M.σ.SameCycle P.u z) : (R.lab z).1 = P.k := by
  rw [R.type_eq_of_sameCycle P.not_marked_u hz, P.lab_u]

theorem type_of_v {z : R.M.D} (hz : R.M.σ.SameCycle P.v z) : (R.lab z).1 = P.k := by
  rw [R.type_eq_of_sameCycle P.not_marked_v hz, P.lab_v]

/-- The word around the `u`-vertex with the new labels, read from `u`. -/
theorem cycleWord_lab'_u (hv : ¬ R.M.σ.SameCycle P.u P.v) :
    cycleWord R.M.σ (C.letterWord ∘ P.lab') P.u =
      C.letterWord (P.lab' P.u) * (C.letterWord (R.lab P.u))⁻¹ := by
  rw [cycleWord_update_first (f := C.letterWord ∘ R.lab) R.M.σ, R.local_eq _ P.not_marked_u,
    mul_one]
  · rfl
  intro y hy hyu
  have hyd : y ≠ P.d := fun h => P.not_marked_of_u hy (h ▸ P.marked)
  have hye : y ≠ P.e := fun h => P.not_marked_of_u hy (h ▸ P.marked_e)
  have hyv : y ≠ P.v := fun h => hv (h ▸ hy)
  simp only [Function.comp_apply]
  rw [P.lab'_of_ne hyd hyu hye hyv]

theorem cycleWord_lab'_v (hv : ¬ R.M.σ.SameCycle P.u P.v) :
    cycleWord R.M.σ (C.letterWord ∘ P.lab') P.v =
      C.letterWord (P.lab' P.v) * (C.letterWord (R.lab P.v))⁻¹ := by
  rw [cycleWord_update_first (f := C.letterWord ∘ R.lab) R.M.σ, R.local_eq _ P.not_marked_v,
    mul_one]
  · rfl
  intro y hy hyv
  have hyd : y ≠ P.d := fun h => P.not_marked_of_v hy (h ▸ P.marked)
  have hye : y ≠ P.e := fun h => P.not_marked_of_v hy (h ▸ P.marked_e)
  have hyu : y ≠ P.u := fun h => hv (h ▸ hy).symm
  simp only [Function.comp_apply]
  rw [P.lab'_of_ne hyd hyu hye hyv]

theorem lab'_eq_of_not {z y : R.M.D} (hz : ¬ R.M.σ.SameCycle R.base z)
    (hu : ¬ R.M.σ.SameCycle P.u z) (hv : ¬ R.M.σ.SameCycle P.v z) (hy : R.M.σ.SameCycle z y) :
    P.lab' y = R.lab y := by
  refine P.lab'_of_ne ?_ ?_ ?_ ?_
  · exact fun h => hz ((h ▸ P.marked).trans hy.symm)
  · exact fun h => hu (h ▸ hy.symm)
  · exact fun h => hz ((h ▸ P.marked_e).trans hy.symm)
  · exact fun h => hv (h ▸ hy.symm)

/-! ### Consolidation at two distinct ordinary vertices -/

section Distinct

variable (hdist : ¬ R.M.σ.SameCycle P.u P.v)

/-- The rotation before erasure: the two ordinary vertices merged, `ρ * σ` with `ρ = (u v)`. -/
def πA : Perm R.M.D := swap P.u P.v * R.M.σ

include hdist

theorem πA_sameCycle_iff {y z : R.M.D} :
    P.πA.SameCycle y z ↔ R.M.σ.SameCycle y z ∨
      ((R.M.σ.SameCycle P.u y ∨ R.M.σ.SameCycle P.v y) ∧
        (R.M.σ.SameCycle P.u z ∨ R.M.σ.SameCycle P.v z)) :=
  sameCycle_swap_mul_iff hdist

theorem πA_marked_iff {z : R.M.D} :
    P.πA.SameCycle R.base z ↔ R.M.σ.SameCycle R.base z := by
  rw [P.πA_sameCycle_iff hdist]
  constructor
  · rintro (h | ⟨h | h, -⟩)
    · exact h
    · exact absurd h.symm P.not_marked_u
    · exact absurd h.symm P.not_marked_v
  · exact Or.inl

omit hdist in
theorem πA_apply_of_marked {z : R.M.D} (hz : R.M.σ.SameCycle R.base z) :
    P.πA z = R.M.σ z := by
  have h := marked_σ hz
  exact swap_apply_of_ne_of_ne (fun e => P.not_marked_u (e ▸ h)) (fun e => P.not_marked_v (e ▸ h))

theorem πA_v_ne : P.πA P.v ≠ P.e ∧ P.πA P.v ≠ P.v := by
  change swap P.u P.v (R.M.σ P.v) ≠ P.e ∧ swap P.u P.v (R.M.σ P.v) ≠ P.v
  by_cases hσv : R.M.σ P.v = P.v
  · rw [hσv, swap_apply_right]
    exact ⟨P.e_ne_u.symm, P.u_ne_v⟩
  · have h1 : R.M.σ P.v ≠ P.u := fun h => hdist (Perm.SameCycle.symm
      (show R.M.σ.SameCycle P.v P.u from ⟨1, by simpa using h⟩))
    rw [swap_apply_of_ne_of_ne h1 hσv]
    refine ⟨fun h => P.not_marked_of_v (⟨1, by simpa using h⟩ : R.M.σ.SameCycle P.v P.e)
      P.marked_e, hσv⟩

/-- The rotation after consolidation (on the full dart set; `e, v` are fixed). -/
abbrev σA : Perm R.M.D := erase2 P.πA P.e (R.M.α P.e)

omit hdist in
theorem σA_sameCycle_iff {y z : R.M.D} (hy : y ≠ P.e ∧ y ≠ P.v) (hz : z ≠ P.e ∧ z ≠ P.v) :
    (P.σA).SameCycle y z ↔ P.πA.SameCycle y z :=
  sameCycle_erase2_iff hy.1 hy.2 hz.1 hz.2

theorem cycleWord_σA_u : cycleWord P.σA (C.letterWord ∘ P.lab') P.u = 1 := by
  rw [cycleWord_erase2 (b := R.M.α P.e) _ P.e_ne_u.symm P.u_ne_v P.word_e P.word_v]
  change cycleWord (swap P.u P.v * R.M.σ) _ P.u = 1
  rw [cycleWord_swap_mul _ hdist, P.cycleWord_lab'_u hdist, P.cycleWord_lab'_v hdist, P.lab'_u,
    P.lab'_v, P.lab_u, P.lab_v]
  simp only [letterWord, map_inv, map_mul, map_one]
  group

/-- The consolidated labelled map, before connectivity and `χ`. -/
def consolidatePre : C.PrePicture x :=
  PrePicture.ofEraseEdge R.M P.πA P.e P.lab' R.base ⟨P.ne_base.symm, P.base_ne_v⟩
    (by
      intro z hz1 hz2 hz
      rw [P.lab'_fst, P.lab'_fst]
      have hw1 := erase2_apply_ne_left (π := P.πA) (P.ne_α_e) hz1
      have hw2 := erase2_apply_ne_right (π := P.πA) (a := P.e) hz2
      have hw : P.πA.SameCycle z (P.σA z) :=
        (P.σA_sameCycle_iff ⟨hz1, hz2⟩ ⟨hw1, hw2⟩).1 ⟨1, by simp⟩
      rw [P.πA_marked_iff hdist] at hz
      rcases (P.πA_sameCycle_iff hdist).1 hw with h | ⟨h1, h2⟩
      · exact R.type_eq_of_sameCycle hz h
      · rw [show (R.lab (P.σA z)).1 = P.k from h2.elim P.type_of_u P.type_of_v,
          h1.elim P.type_of_u P.type_of_v])
    (by
      intro z hz1 hz2 hz
      rw [P.πA_marked_iff hdist] at hz
      by_cases hU : R.M.σ.SameCycle P.u z ∨ R.M.σ.SameCycle P.v z
      · refine cycleWord_eq_one_of_sameCycle _ ?_ (P.cycleWord_σA_u hdist)
        refine (P.σA_sameCycle_iff ⟨P.e_ne_u.symm, P.u_ne_v⟩ ⟨hz1, hz2⟩).2 ?_
        exact (P.πA_sameCycle_iff hdist).2 (Or.inr ⟨Or.inl (Perm.SameCycle.refl _ _), hU⟩)
      push_neg at hU
      rw [cycleWord_erase2 (b := R.M.α P.e) _ hz1 hz2 P.word_e P.word_v]
      change cycleWord (swap P.u P.v * R.M.σ) _ z = 1
      rw [cycleWord_congr _ (swap_mul_pow_apply_of_not_sameCycle hU.1 hU.2)]
      rw [cycleWord_congr_fun (g := C.letterWord ∘ R.lab) fun y hy => by
        simp only [Function.comp_apply]; rw [P.lab'_eq_of_not hz hU.1 hU.2 hy]]
      exact R.local_eq z hz)
    (by
      intro z _ _ hz hz'
      rw [P.πA_marked_iff hdist] at hz hz'
      exact P.edge_interior_lab' hz hz')
    (by
      intro z hz1 _ hz
      rw [P.πA_marked_iff hdist] at hz ⊢
      exact P.edge_boundary_lab' hz hz1)
    (by
      rw [cycleWord_erase2 (b := R.M.α P.e) _ P.ne_base.symm P.base_ne_v P.word_e P.word_v]
      change cycleWord (swap P.u P.v * R.M.σ) _ R.base = x
      rw [cycleWord_congr _ (swap_mul_pow_apply_of_not_sameCycle
        (fun h => P.not_marked_u h.symm) (fun h => P.not_marked_v h.symm))]
      exact P.cycleWord_lab'_base)

theorem consolidatePre_M : (P.consolidatePre hdist).M = R.M.eraseEdge P.πA P.e := rfl

theorem consolidate_numVertices :
    (R.M.eraseEdge P.πA P.e).numVertices + 1 = R.M.numVertices := by
  have h1 := CombMap.eraseEdge_numVertices P.πA P.e
  have h2 := numOrbits_erase2 P.πA P.e (R.M.α P.e)
  have h3 : numOrbits R.M.σ = numOrbits P.πA + 1 := numOrbits_swap_mul hdist
  have h4 : P.πA P.e ≠ P.e := by rw [P.πA_apply_of_marked P.marked_e]; exact P.σe_ne_e
  have h5 : erasePt P.πA P.e (R.M.α P.e) ≠ R.M.α P.e := by
    change erasePt P.πA P.e P.v ≠ P.v
    rw [erasePt_apply_of_ne P.e_ne_v.symm (P.πA_v_ne hdist).1]
    exact (P.πA_v_ne hdist).2
  rw [if_neg h4, if_neg h5] at h2
  unfold CombMap.numVertices at *
  omega

omit hdist in
theorem consolidate_numEdges' : (R.M.eraseEdge P.πA P.e).numEdges + 1 = R.M.numEdges :=
  CombMap.eraseEdge_numEdges _ _

omit hdist in
theorem swap_identity :
    swap P.e P.v * swap P.u P.v = swap P.u P.v * swap P.e P.u := by
  have h1 := P.e_ne_u
  have h2 := P.e_ne_v
  have h3 := P.u_ne_v
  ext z
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

theorem consolidate_numFaces :
    (R.M.eraseEdge P.πA P.e).numFaces = R.M.numFaces := by
  have h1 := CombMap.eraseEdge_numFaces P.πA P.e
  have hφu : R.M.φ P.u = P.e := by
    change R.M.σ (R.M.α P.u) = P.e
    rw [α_u, P.next]
  have hχ : numOrbits (swap P.e (R.M.α P.e) * P.πA * R.M.α) = R.M.numFaces := by
    have e1 : swap P.e (R.M.α P.e) * P.πA * R.M.α =
        swap P.u P.v * (swap P.e P.u * R.M.φ) := by
      change swap P.e P.v * (swap P.u P.v * R.M.σ) * R.M.α = _
      rw [← mul_assoc, P.swap_identity]
      simp only [mul_assoc]
      rfl
    have e2 : numOrbits (swap P.e P.u * R.M.φ) = numOrbits R.M.φ + 1 :=
      numOrbits_swap_mul_split P.e_ne_u
        (Perm.SameCycle.symm (show R.M.φ.SameCycle P.u P.e from ⟨1, by simpa using hφu⟩))
    have hfix : (swap P.e P.u * R.M.φ) P.u = P.u := by
      rw [Perm.mul_apply, hφu, swap_apply_left]
    have e3 := numOrbits_swap_mul (π := swap P.e P.u * R.M.φ) (a := P.u) (b := P.v)
      (fun h => P.u_ne_v (h.eq_of_left hfix))
    rw [e1]
    unfold CombMap.numFaces
    omega
  have hχe : (swap P.e (R.M.α P.e) * P.πA * R.M.α) P.e = P.πA P.v := by
    change swap P.e P.v (P.πA (R.M.α P.e)) = _
    exact swap_apply_of_ne_of_ne (P.πA_v_ne hdist).1 (P.πA_v_ne hdist).2
  have hχv : (swap P.e (R.M.α P.e) * P.πA * R.M.α) (R.M.α P.e) = R.M.σ P.e := by
    change swap P.e P.v (P.πA (R.M.α P.v)) = _
    rw [α_v, P.πA_apply_of_marked P.marked_e]
    exact swap_apply_of_ne_of_ne P.σe_ne_e
      (fun h => P.not_marked_v (h ▸ marked_σ P.marked_e))
  have h2 := numOrbits_erase2 (Equiv.swap P.e (R.M.α P.e) * P.πA * R.M.α) P.e (R.M.α P.e)
  have h4 : (swap P.e (R.M.α P.e) * P.πA * R.M.α) P.e ≠ P.e := by
    rw [hχe]; exact (P.πA_v_ne hdist).1
  have h5 : erasePt (swap P.e (R.M.α P.e) * P.πA * R.M.α) P.e (R.M.α P.e) ≠ R.M.α P.e := by
    rw [erasePt_apply_of_ne (x := R.M.α P.e) P.e_ne_v.symm (by rw [hχv]; exact P.σe_ne_e), hχv]
    exact fun h => P.not_marked_v (by rw [v, ← h]; exact marked_σ P.marked_e)
  rw [if_neg h4, if_neg h5, hχ] at h2
  omega

theorem consolidate_euler : (R.M.eraseEdge P.πA P.e).euler = 2 := by
  have hV := P.consolidate_numVertices hdist
  have hE := P.consolidate_numEdges'
  have hF := P.consolidate_numFaces hdist
  have h := R.spherical
  unfold CombMap.euler at h ⊢
  omega

theorem consolidate_connected : (R.M.eraseEdge P.πA P.e).Connected := by
  classical
  have hSC : ∀ y z, (y ≠ P.e ∧ y ≠ P.v) → (z ≠ P.e ∧ z ≠ P.v) → P.πA.SameCycle y z →
      Relation.EqvGen (R.M.withσ P.σA).Step y z := fun y z hy hz h =>
    CombMap.withσ_eqvGen_of_sameCycle ((P.σA_sameCycle_iff hy hz).2 h)
  have hσ1 : ∀ y, R.M.σ.SameCycle y (R.M.σ y) := fun y => ⟨1, by simp⟩
  have hσe1 : R.M.σ P.e ≠ P.v := fun h => P.not_marked_v (h ▸ marked_σ P.marked_e)
  refine CombMap.eraseEdge_connected_of P.πA P.e R.connected
    (fun z => if z = P.e then P.d else if z = P.v then P.u else z)
    (fun y hy1 hy2 => by simp only [if_neg hy1, if_neg (show y ≠ P.v from hy2)]) ?_ ?_
  · intro y
    by_cases hye : y = P.e
    · subst hye
      simp only [if_neg P.σe_ne_e, if_neg hσe1]
      refine hSC _ _ ⟨P.ne, P.d_ne_v⟩ ⟨P.σe_ne_e, hσe1⟩ ((P.πA_sameCycle_iff hdist).2 (Or.inl ?_))
      exact (show R.M.σ.SameCycle P.d P.e from ⟨1, by simpa using P.next⟩).trans (hσ1 _)
    by_cases hyv : y = P.v
    · subst hyv
      simp only [if_neg P.e_ne_v.symm]
      by_cases hσv : R.M.σ P.v = P.v
      · rw [hσv]; simp only [if_neg P.e_ne_v.symm]; exact Relation.EqvGen.refl _
      have hσve : R.M.σ P.v ≠ P.e := fun h =>
        P.not_marked_of_v (show R.M.σ.SameCycle P.v P.e from ⟨1, by simpa using h⟩) P.marked_e
      simp only [if_neg hσve, if_neg hσv]
      exact hSC _ _ ⟨P.e_ne_u.symm, P.u_ne_v⟩ ⟨hσve, hσv⟩ ((P.πA_sameCycle_iff hdist).2
        (Or.inr ⟨Or.inl (Perm.SameCycle.refl _ _), Or.inr (hσ1 _)⟩))
    simp only [if_neg hye, if_neg hyv]
    by_cases h1 : R.M.σ y = P.e
    · have : y = P.d := R.M.σ.injective (h1.trans P.next.symm)
      rw [h1, if_pos rfl, this]
      exact Relation.EqvGen.refl _
    by_cases h2 : R.M.σ y = P.v
    · rw [h2, if_neg P.e_ne_v.symm, if_pos rfl]
      exact hSC _ _ ⟨hye, hyv⟩ ⟨P.e_ne_u.symm, P.u_ne_v⟩ ((P.πA_sameCycle_iff hdist).2
        (Or.inr ⟨Or.inr (Perm.SameCycle.symm (show R.M.σ.SameCycle y P.v from
          ⟨1, by simpa using h2⟩)), Or.inl (Perm.SameCycle.refl _ _)⟩))
    simp only [if_neg h1, if_neg h2]
    exact hSC _ _ ⟨hye, hyv⟩ ⟨h1, h2⟩ ((P.πA_sameCycle_iff hdist).2 (Or.inl (hσ1 _)))
  · intro y
    by_cases hye : y = P.e
    · subst hye
      rw [α_e]
      simp only [if_neg P.e_ne_v.symm]
      exact CombMap.withσ_eqvGen_α P.d
    by_cases hyv : y = P.v
    · subst hyv
      rw [α_v]
      simp only [if_neg P.e_ne_v.symm]
      exact (CombMap.withσ_eqvGen_α (σ' := P.σA) P.d).symm _ _
    have h1 : R.M.α y ≠ P.e := fun h => hyv (by rw [← R.M.α_α y, h]; rfl)
    have h2 : R.M.α y ≠ P.v := fun h => hye (R.M.α.injective h)
    simp only [if_neg hye, if_neg hyv, if_neg h1, if_neg h2]
    exact CombMap.withσ_eqvGen_α y

/-- **Consolidation at two distinct ordinary vertices.**  A raw picture for the same element
`x`, with the same base dart, on the darts other than `e, v`. -/
def consolidate : C.RawPicture x :=
  (P.consolidatePre hdist).toRaw (P.consolidate_connected hdist) (P.consolidate_euler hdist)

theorem consolidate_M : (P.consolidate hdist).M = R.M.eraseEdge P.πA P.e := rfl

/-- One edge fewer. -/
theorem consolidate_numEdges : (P.consolidate hdist).M.numEdges + 1 = R.M.numEdges :=
  P.consolidate_numEdges'

/-- The counts: `V' = V - 1`, `E' = E - 1`, `F' = F`. -/
theorem consolidate_counts :
    (P.consolidate hdist).M.numVertices + 1 = R.M.numVertices ∧
    (P.consolidate hdist).M.numEdges + 1 = R.M.numEdges ∧
    (P.consolidate hdist).M.numFaces = R.M.numFaces :=
  ⟨P.consolidate_numVertices hdist, P.consolidate_numEdges', P.consolidate_numFaces hdist⟩

/-- The base dart and all labels are as described: the base dart is the old one, `d` carries
`⟨k, g₁ g₂⟩`, `u` carries `⟨k, (g₁ g₂)⁻¹⟩`, and every other retained dart keeps its label. -/
theorem consolidate_base : ((P.consolidate hdist).base).val = R.base := rfl

theorem consolidate_lab (z : (P.consolidate hdist).M.D) :
    (P.consolidate hdist).lab z = P.lab' z.val := rfl

/-- The rotation of the consolidated picture is `erase_{e,v}(swap u v * σ)`. -/
theorem consolidate_σ_val (z : (P.consolidate hdist).M.D) :
    ((P.consolidate hdist).M.σ z).val = erase2 (swap P.u P.v * R.M.σ) P.e P.v z.val := rfl

end Distinct

/-! ### Consolidation of a marked digon -/

section Digon

variable (hdig : R.M.σ P.v = P.u)

/-- The rotation after digon consolidation (on the full dart set; `e, v` are fixed). -/
abbrev σB : Perm R.M.D := erase2 R.M.σ P.e (R.M.α P.e)

theorem σB_sameCycle_iff {y z : R.M.D} (hy : y ≠ P.e ∧ y ≠ P.v) (hz : z ≠ P.e ∧ z ≠ P.v) :
    (P.σB).SameCycle y z ↔ R.M.σ.SameCycle y z :=
  sameCycle_erase2_iff hy.1 hy.2 hz.1 hz.2

include hdig

theorem sameCycle_v_u : R.M.σ.SameCycle P.v P.u := ⟨1, by simpa using hdig⟩

theorem cycleWord_σB_u : cycleWord P.σB (C.letterWord ∘ P.lab') P.u = 1 := by
  rw [cycleWord_erase2 (b := R.M.α P.e) _ P.e_ne_u.symm P.u_ne_v P.word_e P.word_v, ← hdig,
    cycleWord_apply]
  simp only [Function.comp_apply, P.word_v, inv_one, one_mul, mul_one]
  have hvu : R.M.σ P.v ≠ P.v := by rw [hdig]; exact P.u_ne_v
  rw [cycleWord_merge_consecutive (f := C.letterWord ∘ R.lab) hvu (Perm.SameCycle.refl _ _)
    hvu.symm (fun y hy hyv hyu => ?_) ?_]
  · exact R.local_eq _ P.not_marked_v
  · simp only [Function.comp_apply, hdig]
    rw [P.lab'_v, P.lab'_u, P.lab_v, P.lab_u]
    simp only [letterWord, map_one, one_mul, map_inv, map_mul, mul_inv_rev]
  · rw [hdig] at hyu
    have hyd : y ≠ P.d := fun h => P.not_marked_of_v hy (h ▸ P.marked)
    have hye : y ≠ P.e := fun h => P.not_marked_of_v hy (h ▸ P.marked_e)
    simp only [Function.comp_apply]
    rw [P.lab'_of_ne hyd hyu hye hyv]

/-- The digon-consolidated labelled map, before connectivity and `χ`. -/
def consolidateDigonPre : C.PrePicture x :=
  PrePicture.ofEraseEdge R.M R.M.σ P.e P.lab' R.base ⟨P.ne_base.symm, P.base_ne_v⟩
    (by
      intro z hz1 hz2 hz
      rw [P.lab'_fst, P.lab'_fst]
      have hw1 := erase2_apply_ne_left (π := R.M.σ) (P.ne_α_e) hz1
      have hw2 := erase2_apply_ne_right (π := R.M.σ) (a := P.e) hz2
      have hw : R.M.σ.SameCycle z (P.σB z) :=
        (P.σB_sameCycle_iff ⟨hz1, hz2⟩ ⟨hw1, hw2⟩).1 ⟨1, by simp⟩
      exact R.type_eq_of_sameCycle hz hw)
    (by
      intro z hz1 hz2 hz
      by_cases hU : R.M.σ.SameCycle P.u z
      · refine cycleWord_eq_one_of_sameCycle _ ?_ (P.cycleWord_σB_u hdig)
        exact (P.σB_sameCycle_iff ⟨P.e_ne_u.symm, P.u_ne_v⟩ ⟨hz1, hz2⟩).2 hU
      have hV : ¬ R.M.σ.SameCycle P.v z := fun h => hU ((P.sameCycle_v_u hdig).symm.trans h)
      rw [cycleWord_erase2 (b := R.M.α P.e) _ hz1 hz2 P.word_e P.word_v]
      rw [cycleWord_congr_fun (g := C.letterWord ∘ R.lab) fun y hy => by
        simp only [Function.comp_apply]; rw [P.lab'_eq_of_not hz hU hV hy]]
      exact R.local_eq z hz)
    (fun z _ _ hz hz' => P.edge_interior_lab' hz hz')
    (fun z hz1 _ hz => P.edge_boundary_lab' hz hz1)
    (by
      rw [cycleWord_erase2 (b := R.M.α P.e) _ P.ne_base.symm P.base_ne_v P.word_e P.word_v]
      exact P.cycleWord_lab'_base)

theorem consolidateDigon_numVertices :
    (R.M.eraseEdge R.M.σ P.e).numVertices = R.M.numVertices := by
  have h1 := CombMap.eraseEdge_numVertices R.M.σ P.e
  have h2 := numOrbits_erase2 R.M.σ P.e (R.M.α P.e)
  have h5 : erasePt R.M.σ P.e (R.M.α P.e) ≠ R.M.α P.e := by
    change erasePt R.M.σ P.e P.v ≠ P.v
    rw [erasePt_apply_of_ne P.e_ne_v.symm (by rw [hdig]; exact P.e_ne_u.symm), hdig]
    exact P.u_ne_v
  rw [if_neg P.σe_ne_e, if_neg h5] at h2
  unfold CombMap.numVertices at *
  omega

omit hdig in
theorem consolidateDigon_numEdges' :
    (R.M.eraseEdge R.M.σ P.e).numEdges + 1 = R.M.numEdges :=
  CombMap.eraseEdge_numEdges _ _

theorem consolidateDigon_numFaces :
    (R.M.eraseEdge R.M.σ P.e).numFaces + 1 = R.M.numFaces := by
  have h1 := CombMap.eraseEdge_numFaces R.M.σ P.e
  have hφu : R.M.φ P.u = P.e := by
    change R.M.σ (R.M.α P.u) = P.e
    rw [α_u, P.next]
  have hφe : R.M.φ P.e = P.u := by
    change R.M.σ (R.M.α P.e) = P.u
    exact hdig
  have hcyc : ∀ n : ℕ, (R.M.φ ^ n) P.e = P.e ∨ (R.M.φ ^ n) P.e = P.u := by
    intro n
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      rcases ih with h | h <;> rw [h]
      · exact Or.inr hφe
      · exact Or.inl hφu
  have hnot : ¬ R.M.φ.SameCycle P.e P.v := by
    intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    rcases hcyc n with h' | h' <;> rw [h'] at hn
    · exact P.e_ne_v hn
    · exact P.u_ne_v hn
  have hχ : numOrbits (Equiv.swap P.e (R.M.α P.e) * R.M.σ * R.M.α) + 1 = R.M.numFaces := by
    have := numOrbits_swap_mul hnot
    rw [mul_assoc]
    unfold CombMap.numFaces
    exact this.symm
  have hχe : (Equiv.swap P.e (R.M.α P.e) * R.M.σ * R.M.α) P.e = P.u := by
    change swap P.e P.v (R.M.σ (R.M.α P.e)) = _
    change swap P.e P.v (R.M.σ P.v) = _
    rw [hdig]
    exact swap_apply_of_ne_of_ne P.e_ne_u.symm P.u_ne_v
  have hσev : R.M.σ P.e ≠ P.v := fun h => P.not_marked_v (h ▸ marked_σ P.marked_e)
  have hχv : (Equiv.swap P.e (R.M.α P.e) * R.M.σ * R.M.α) (R.M.α P.e) = R.M.σ P.e := by
    change swap P.e P.v (R.M.σ (R.M.α P.v)) = _
    rw [α_v]
    exact swap_apply_of_ne_of_ne P.σe_ne_e hσev
  have h2 := numOrbits_erase2 (Equiv.swap P.e (R.M.α P.e) * R.M.σ * R.M.α) P.e (R.M.α P.e)
  have h4 : (Equiv.swap P.e (R.M.α P.e) * R.M.σ * R.M.α) P.e ≠ P.e := by
    rw [hχe]; exact P.e_ne_u.symm
  have h5 : erasePt (Equiv.swap P.e (R.M.α P.e) * R.M.σ * R.M.α) P.e (R.M.α P.e) ≠
      R.M.α P.e := by
    rw [erasePt_apply_of_ne (x := R.M.α P.e) P.e_ne_v.symm (by rw [hχv]; exact P.σe_ne_e), hχv]
    exact hσev
  rw [if_neg h4, if_neg h5] at h2
  omega

theorem consolidateDigon_euler : (R.M.eraseEdge R.M.σ P.e).euler = 2 := by
  have hV := P.consolidateDigon_numVertices hdig
  have hE := P.consolidateDigon_numEdges'
  have hF := P.consolidateDigon_numFaces hdig
  have h := R.spherical
  unfold CombMap.euler at h ⊢
  omega

theorem consolidateDigon_connected : (R.M.eraseEdge R.M.σ P.e).Connected := by
  classical
  have hSC : ∀ y z, (y ≠ P.e ∧ y ≠ P.v) → (z ≠ P.e ∧ z ≠ P.v) → R.M.σ.SameCycle y z →
      Relation.EqvGen (R.M.withσ P.σB).Step y z := fun y z hy hz h =>
    CombMap.withσ_eqvGen_of_sameCycle ((P.σB_sameCycle_iff hy hz).2 h)
  have hσ1 : ∀ y, R.M.σ.SameCycle y (R.M.σ y) := fun y => ⟨1, by simp⟩
  have hσe1 : R.M.σ P.e ≠ P.v := fun h => P.not_marked_v (h ▸ marked_σ P.marked_e)
  refine CombMap.eraseEdge_connected_of R.M.σ P.e R.connected
    (fun z => if z = P.e then P.d else if z = P.v then P.u else z)
    (fun y hy1 hy2 => by simp only [if_neg hy1, if_neg (show y ≠ P.v from hy2)]) ?_ ?_
  · intro y
    by_cases hye : y = P.e
    · subst hye
      simp only [if_neg P.σe_ne_e, if_neg hσe1]
      refine hSC _ _ ⟨P.ne, P.d_ne_v⟩ ⟨P.σe_ne_e, hσe1⟩ ?_
      exact (show R.M.σ.SameCycle P.d P.e from ⟨1, by simpa using P.next⟩).trans (hσ1 _)
    by_cases hyv : y = P.v
    · subst hyv
      rw [hdig]
      simp only [if_neg P.e_ne_v.symm, if_neg P.e_ne_u.symm, if_neg P.u_ne_v]
      exact Relation.EqvGen.refl _
    simp only [if_neg hye, if_neg hyv]
    by_cases h1 : R.M.σ y = P.e
    · have : y = P.d := R.M.σ.injective (h1.trans P.next.symm)
      rw [h1, if_pos rfl, this]
      exact Relation.EqvGen.refl _
    by_cases h2 : R.M.σ y = P.v
    · rw [h2, if_neg P.e_ne_v.symm, if_pos rfl]
      refine hSC _ _ ⟨hye, hyv⟩ ⟨P.e_ne_u.symm, P.u_ne_v⟩ ?_
      exact (show R.M.σ.SameCycle y P.v from ⟨1, by simpa using h2⟩).trans
        (P.sameCycle_v_u hdig)
    simp only [if_neg h1, if_neg h2]
    exact hSC _ _ ⟨hye, hyv⟩ ⟨h1, h2⟩ (hσ1 _)
  · intro y
    by_cases hye : y = P.e
    · subst hye
      rw [α_e]
      simp only [if_neg P.e_ne_v.symm]
      exact CombMap.withσ_eqvGen_α (σ' := P.σB) P.d
    by_cases hyv : y = P.v
    · subst hyv
      rw [α_v]
      simp only [if_neg P.e_ne_v.symm]
      exact (CombMap.withσ_eqvGen_α (σ' := P.σB) P.d).symm _ _
    have h1 : R.M.α y ≠ P.e := fun h => hyv (by rw [← R.M.α_α y, h]; rfl)
    have h2 : R.M.α y ≠ P.v := fun h => hye (R.M.α.injective h)
    simp only [if_neg hye, if_neg hyv, if_neg h1, if_neg h2]
    exact CombMap.withσ_eqvGen_α y

/-- **Consolidation of a marked digon.**  A raw picture for the same element `x`, with the same
base dart, on the darts other than `e, v`, with rotation `erase_{e,v}(σ)`. -/
def consolidateDigon : C.RawPicture x :=
  (P.consolidateDigonPre hdig).toRaw (P.consolidateDigon_connected hdig)
    (P.consolidateDigon_euler hdig)

theorem consolidateDigon_M : (P.consolidateDigon hdig).M = R.M.eraseEdge R.M.σ P.e := rfl

/-- The counts: `V' = V`, `E' = E - 1`, `F' = F - 1`. -/
theorem consolidateDigon_counts :
    (P.consolidateDigon hdig).M.numVertices = R.M.numVertices ∧
    (P.consolidateDigon hdig).M.numEdges + 1 = R.M.numEdges ∧
    (P.consolidateDigon hdig).M.numFaces + 1 = R.M.numFaces :=
  ⟨P.consolidateDigon_numVertices hdig, P.consolidateDigon_numEdges',
    P.consolidateDigon_numFaces hdig⟩

theorem consolidateDigon_base : ((P.consolidateDigon hdig).base).val = R.base := rfl

theorem consolidateDigon_lab (z : (P.consolidateDigon hdig).M.D) :
    (P.consolidateDigon hdig).lab z = P.lab' z.val := rfl

theorem consolidateDigon_σ_val (z : (P.consolidateDigon hdig).M.D) :
    ((P.consolidateDigon hdig).M.σ z).val = erase2 R.M.σ P.e P.v z.val := rfl

end Digon

end RawPicture.MarkedPair

end ConeComplex

end TheoremA
