module

public import RequestProject.TheoremA.Lemma31.Picture.DefectData

/-!
# No repeated vertex on a face of a least defect (Section 1)

`ConeComplex.IsLeastDefect.sameVertex_sameFace_eq`: in a least defect, two darts lying in the same
vertex and in the same face are equal.  This covers ordinary and exceptional vertices alike and
uses neither `NPC` nor the girth.

Proof: splitting the vertex between two distinct such darts `a, b` disconnects the (spherical) map
into two spheres, the components of `a` and of `b` (`CombMap.split_sameFace_spherical`).  The two
new vertex products `P, Q` (read at `a`, `b`) satisfy `P * Q = ` old product.

* If the split vertex was exceptional, `P * Q ≠ 1`, so one of `P, Q` is nonidentity; its component
  is defect data (all its other vertices are old ordinary vertices).
* If the split vertex was ordinary, `P * Q = 1`.  Let `q` be the piece whose component contains
  the old exceptional vertex and `p` the other one.  If the product at `p` is nonidentity, the
  component of `p` (which does not contain the old exceptional vertex) is defect data with
  exceptional vertex `p`; otherwise both new products are `1` and the component of `q` is defect
  data with the old exceptional vertex.

Either component has strictly fewer edges than the whole map (the other one is nonempty), which
contradicts minimality.  No marked leaf and no cap are needed.
-/

@[expose] public section

namespace TheoremA

universe u w

open Picture Equiv Function

namespace ConeComplex

variable {V T : Type w} {C : ConeComplex.{u, w} V T}

open Classical in
theorem component_cycleWord_comp {G : Type*} [Monoid G] (N : CombMap) (c : N.D)
    (g : C.Letter → G) (lab : N.D → C.Letter) (y : (N.component c).D) :
    cycleWord (N.component c).σ (g ∘ lab ∘ Subtype.val) y = cycleWord N.σ (g ∘ lab) y.val :=
  CombMap.restrict_cycleWord (M := N) _ _ _ (g ∘ lab) y

open Classical in
theorem component_sameCycle_iff' (N : CombMap) (c : N.D) {x y : (N.component c).D} :
    (N.component c).σ.SameCycle x y ↔ N.σ.SameCycle x.val y.val :=
  CombMap.restrict_sameCycle_iff (M := N) _ _ _

/-- Defect data on a component of a labelled map. -/
theorem DefectData.of_component (N : CombMap) (lab : N.D → C.Letter)
    (htype : ∀ d, (lab (N.σ d)).1 = (lab d).1)
    (hedge : ∀ d, C.RelEdge (lab d) (lab (N.α d)) ∨ C.RelEdge (lab (N.α d)) (lab d))
    (c : N.D) (hχ : (N.component c).euler = 2) (x : N.D) (hx : Relation.EqvGen N.Step c x)
    (hwx : cycleWord N.σ (C.letterWord ∘ lab) x ≠ 1)
    (hrest : ∀ y, Relation.EqvGen N.Step c y → cycleWord N.σ (C.letterWord ∘ lab) y ≠ 1 →
      N.σ.SameCycle x y) :
    C.DefectData (N.component c) (lab ∘ Subtype.val) := by
  refine ⟨N.component_connected c, hχ, fun d => htype d.val, fun d => hedge d.val,
    ⟨⟨x, hx⟩, ?_, ?_⟩⟩
  · rw [component_cycleWord_comp]
    exact hwx
  · intro y hy
    rw [component_cycleWord_comp] at hy
    rw [component_sameCycle_iff']
    exact hrest y.val y.2 hy

namespace IsLeastDefect

variable {M : CombMap} {lab : M.D → C.Letter} (h : C.IsLeastDefect M lab)

include h

/-- **Section 1: no repeated vertex on one face.**  In a least defect, two darts lying in the
same vertex and in the same face are equal. -/
theorem sameVertex_sameFace_eq {a b : M.D} (hσ : M.σ.SameCycle a b) (hφ : M.φ.SameCycle a b) :
    a = b := by
  classical
  by_contra hab
  obtain ⟨b0, hb0, hexc⟩ := h.1.exc
  obtain ⟨hdis, -, hreach, -⟩ :=
    CombMap.split_sameFace_spherical h.1.connected h.1.spherical hab hσ hφ
  have hχ : ∀ c, ((M.split a b).component c).euler = 2 := fun c =>
    (CombMap.split_sameFace_component h.1.connected h.1.spherical hab hσ hφ c).1
  have htype : ∀ d, (lab ((M.split a b).σ d)).1 = (lab d).1 := by
    intro d
    have : M.σ.SameCycle d ((M.split a b).σ d) := by
      change M.σ.SameCycle d (swap a b (M.σ d))
      have h1 : M.σ.SameCycle d (M.σ d) := ⟨1, by simp⟩
      by_cases h2 : M.σ d = a
      · rw [h2, swap_apply_left]; exact (h2 ▸ h1).trans hσ
      by_cases h3 : M.σ d = b
      · rw [h3, swap_apply_right]; exact (h3 ▸ h1).trans hσ.symm
      rw [swap_apply_of_ne_of_ne h2 h3]; exact h1
    exact h.1.type_eq_of_sameCycle this
  have hpow : ∀ y, ¬ M.σ.SameCycle a y → ∀ n : ℕ,
      (((M.split a b).σ) ^ n) y = (M.σ ^ n) y :=
    fun y hy n => swap_mul_pow_apply_of_not_sameCycle hy (fun h' => hy (hσ.trans h')) n
  have hword : ∀ y, ¬ M.σ.SameCycle a y →
      cycleWord (M.split a b).σ (C.letterWord ∘ lab) y = cycleWord M.σ (C.letterWord ∘ lab) y :=
    fun y hy => cycleWord_congr _ (hpow y hy)
  have hsc : ∀ y z, ¬ M.σ.SameCycle a y → M.σ.SameCycle y z →
      (M.split a b).σ.SameCycle y z := by
    intro y z hy hyz
    obtain ⟨n, hn⟩ := hyz.exists_nat_pow_eq
    exact sameCycle_of_pow_eq n (by rw [hpow y hy n, hn])
  have hpiece : ∀ y, M.σ.SameCycle a y →
      (M.split a b).σ.SameCycle a y ∨ (M.split a b).σ.SameCycle b y := by
    intro y hy
    rcases (sameCycle_swap_mul_split_iff hab hσ).1 hy with h' | ⟨-, h'⟩
    · exact Or.inl h'
    · exact h'
  have hprod := CombMap.split_cycleWord (C.letterWord ∘ lab) hab hσ
  have hfew : ∀ c c', ¬ Relation.EqvGen (M.split a b).Step c c' →
      ((M.split a b).component c).numEdges < M.numEdges := by
    intro c c' hcc'
    have hadd := CombMap.numEdges_component_add (M.split a b) c
    have hpos := numOrbits_pos ((M.split a b).componentCompl c).α ⟨c', hcc'⟩
    rw [CombMap.split_numEdges] at hadd
    unfold CombMap.numEdges at *
    omega
  have finish : ∀ c c', ¬ Relation.EqvGen (M.split a b).Step c c' → ∀ x,
      Relation.EqvGen (M.split a b).Step c x →
      cycleWord (M.split a b).σ (C.letterWord ∘ lab) x ≠ 1 →
      (∀ y, Relation.EqvGen (M.split a b).Step c y →
        cycleWord (M.split a b).σ (C.letterWord ∘ lab) y ≠ 1 → (M.split a b).σ.SameCycle x y) →
      False := fun c c' hcc' x hx hwx hrest =>
    h.not_lt (DefectData.of_component (M.split a b) lab htype h.1.edge c (hχ c) x hx hwx hrest)
      (hfew c c' hcc')
  -- darts of the split vertex lying in the component of the piece `p`
  have inPiece : ∀ p q, ¬ Relation.EqvGen (M.split a b).Step p q →
      (∀ y, M.σ.SameCycle a y → (M.split a b).σ.SameCycle p y ∨
        (M.split a b).σ.SameCycle q y) →
      ∀ y, Relation.EqvGen (M.split a b).Step p y → M.σ.SameCycle a y →
        (M.split a b).σ.SameCycle p y := by
    intro p q hpq hpc y hy hay
    rcases hpc y hay with h' | h'
    · exact h'
    · exact absurd (hy.trans _ _ _ (((M.split a b).eqvGen_of_sameCycle h').symm _ _)) hpq
  have hpcab : ∀ y, M.σ.SameCycle a y → (M.split a b).σ.SameCycle b y ∨
      (M.split a b).σ.SameCycle a y := fun y hy => (hpiece y hy).symm
  have hdis' : ¬ Relation.EqvGen (M.split a b).Step b a := fun h' => hdis (h'.symm _ _)
  by_cases hWa : cycleWord M.σ (C.letterWord ∘ lab) a = 1
  · -- the split vertex was ordinary
    have hb0a : ¬ M.σ.SameCycle a b0 := fun h' =>
      hb0 (cycleWord_eq_one_of_sameCycle _ h' hWa)
    have caseB : ∀ p q, ¬ Relation.EqvGen (M.split a b).Step p q →
        (∀ y, M.σ.SameCycle a y → (M.split a b).σ.SameCycle p y ∨
          (M.split a b).σ.SameCycle q y) →
        Relation.EqvGen (M.split a b).Step q b0 →
        (cycleWord (M.split a b).σ (C.letterWord ∘ lab) p = 1 →
          cycleWord (M.split a b).σ (C.letterWord ∘ lab) q = 1) → False := by
      intro p q hpq hpc hqb0 hpq1
      by_cases hp1 : cycleWord (M.split a b).σ (C.letterWord ∘ lab) p = 1
      · have hq1 := hpq1 hp1
        refine finish q p (fun h' => hpq (h'.symm _ _)) b0 hqb0 (by rw [hword b0 hb0a]; exact hb0)
          fun y _ hwy => ?_
        by_cases hay : M.σ.SameCycle a y
        · exfalso
          rcases hpc y hay with h' | h'
          · exact hwy (cycleWord_eq_one_of_sameCycle _ h' hp1)
          · exact hwy (cycleWord_eq_one_of_sameCycle _ h' hq1)
        · rw [hword y hay] at hwy
          exact hsc b0 y hb0a (hexc y hwy)
      · refine finish p q hpq p (Relation.EqvGen.refl _) hp1 fun y hy hwy => ?_
        by_cases hay : M.σ.SameCycle a y
        · exact inPiece p q hpq hpc y hy hay
        · exfalso
          rw [hword y hay] at hwy
          have hb0y := (M.split a b).eqvGen_of_sameCycle (hsc b0 y hb0a (hexc y hwy))
          exact hpq (hy.trans _ _ _ ((hb0y.symm _ _).trans _ _ _ (hqb0.symm _ _)))
    rw [hWa] at hprod
    rcases hreach b0 with hab0 | hbb0
    · exact caseB b a hdis' hpcab hab0 fun hb1 => by rw [hb1, mul_one] at hprod; exact hprod.symm
    · exact caseB a b hdis hpiece hbb0 fun ha1 => by rw [ha1, one_mul] at hprod; exact hprod.symm
  · -- the split vertex was exceptional
    have hab0 : M.σ.SameCycle a b0 := by
      by_contra h'
      exact hWa (by_contra fun hne => h' ((hexc a hne).symm))
    have caseA : ∀ p q, ¬ Relation.EqvGen (M.split a b).Step p q →
        (∀ y, M.σ.SameCycle a y → (M.split a b).σ.SameCycle p y ∨
          (M.split a b).σ.SameCycle q y) →
        cycleWord (M.split a b).σ (C.letterWord ∘ lab) p ≠ 1 → False := by
      intro p q hpq hpc hp
      refine finish p q hpq p (Relation.EqvGen.refl _) hp fun y hy hwy => ?_
      by_cases hay : M.σ.SameCycle a y
      · exact inPiece p q hpq hpc y hy hay
      · rw [hword y hay] at hwy
        exact absurd (hab0.trans (hexc y hwy)) hay
    by_cases ha1 : cycleWord (M.split a b).σ (C.letterWord ∘ lab) a = 1
    · refine caseA b a hdis' hpcab fun hb1 => hWa ?_
      rw [hprod, ha1, hb1, one_mul]
    · exact caseA a b hdis hpiece ha1

end IsLeastDefect

end ConeComplex

end TheoremA
