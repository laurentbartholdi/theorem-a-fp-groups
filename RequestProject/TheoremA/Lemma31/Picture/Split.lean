module

public import RequestProject.TheoremA.Lemma31.Picture.CombMap
public import RequestProject.TheoremA.Lemma31.Picture.PermSplit

/-!
# Splitting a vertex of a combinatorial map

For darts `a ≠ b` of the same vertex of a `CombMap` `M`, `M.split a b` keeps the darts and the edge
involution `α` and replaces the rotation by `σ' = swap a b * σ`: the vertex
`(a, x₁, …, x_r, b, y₁, …, y_s)` is split into the two vertices `(a, x₁, …, x_r)` and
`(b, y₁, …, y_s)`.  No labels, `NPC`, girth or spherical assumption are involved.

## Results

* `split_numVertices`, `split_numEdges` : one more vertex, the same edges;
* `split_φ` : the new face permutation is `swap a b * φ`, so the faces are merged or split by the
  same transposition;
* `split_euler_of_not_sameCycle_face` : if `a`, `b` lie in **different** faces, `χ' = χ`
  (`V+1`, `E`, `F-1`);
* `split_euler_of_sameCycle_face` : if `a`, `b` lie in the **same** face, `χ' = χ + 2`
  (`V+1`, `E`, `F+1`).  In particular splitting a vertex does not always preserve `χ = 2`;
* `split_reach` : if `M` is connected, every dart of the split map is connected to `a` or to `b`
  (the split map has at most two components);
* `split_connected_of_eqvGen` : if moreover `a` and `b` are still connected, the split map is
  connected;
* `sameCycle_face_of_split_not_eqvGen` : if `a` and `b` become disconnected, they were in the
  same face of `M`;
* `split_connected` : if `M` is connected and `a`, `b` lie in different faces, the split map is
  connected.
-/

@[expose] public section

namespace TheoremA.Picture

open Equiv Function

namespace CombMap

variable (M : CombMap)

/-- One step along the face permutation is two steps along the map. -/
theorem eqvGen_φ (x : M.D) : Relation.EqvGen M.Step x (M.φ x) :=
  (Relation.EqvGen.rel x (M.α x) (Or.inr rfl)).trans _ _ _
    (Relation.EqvGen.rel (M.α x) (M.φ x) (Or.inl rfl))

/-- The faces lie inside the connected components. -/
theorem eqvGen_of_sameCycle_φ {x y : M.D} (h : M.φ.SameCycle x y) :
    Relation.EqvGen M.Step x y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact Relation.EqvGen.refl _
  | succ n ih =>
    refine ih.trans _ _ _ ?_
    rw [pow_succ', Perm.mul_apply]
    exact M.eqvGen_φ _

variable (a b : M.D)

/-- Split the vertex through `a` and `b`: `σ' = swap a b * σ`, `α' = α`. -/
def split : CombMap where
  D := M.D
  σ := swap a b * M.σ
  α := M.α
  α_α := M.α_α
  α_ne := M.α_ne

@[simp] theorem split_σ : (M.split a b).σ = swap a b * M.σ := rfl

@[simp] theorem split_α : (M.split a b).α = M.α := rfl

theorem split_φ : (M.split a b).φ = swap a b * M.φ := by
  simp only [φ, split, mul_assoc]

theorem split_numEdges : (M.split a b).numEdges = M.numEdges := rfl

variable {M a b}

theorem split_numVertices (hab : a ≠ b) (h : M.σ.SameCycle a b) :
    (M.split a b).numVertices = M.numVertices + 1 :=
  numOrbits_swap_mul_split hab h

theorem split_numFaces_of_not_sameCycle (h : ¬ M.φ.SameCycle a b) :
    (M.split a b).numFaces + 1 = M.numFaces := by
  unfold numFaces
  rw [split_φ]
  exact (numOrbits_swap_mul h).symm

theorem split_numFaces_of_sameCycle (hab : a ≠ b) (h : M.φ.SameCycle a b) :
    (M.split a b).numFaces = M.numFaces + 1 := by
  unfold numFaces
  rw [split_φ]
  exact numOrbits_swap_mul_split hab h

/-- **Splitting a vertex between two different faces preserves `χ`.** -/
theorem split_euler_of_not_sameCycle_face (hab : a ≠ b) (hσ : M.σ.SameCycle a b)
    (hφ : ¬ M.φ.SameCycle a b) : (M.split a b).euler = M.euler := by
  have hV := split_numVertices hab hσ
  have hE := split_numEdges M a b
  have hF := split_numFaces_of_not_sameCycle hφ
  unfold euler
  omega

/-- **Splitting a vertex inside one face raises `χ` by two.** -/
theorem split_euler_of_sameCycle_face (hab : a ≠ b) (hσ : M.σ.SameCycle a b)
    (hφ : M.φ.SameCycle a b) : (M.split a b).euler = M.euler + 2 := by
  have hV := split_numVertices hab hσ
  have hE := split_numEdges M a b
  have hF := split_numFaces_of_sameCycle hab hφ
  unfold euler
  omega

/-! ### Connectivity -/

/-- Rejoining `a` and `b` recovers every step of the original map. -/
theorem eqvGen_split_join_of_step {x y : M.D} (h : M.Step x y) :
    Relation.EqvGen (fun u v => (M.split a b).Step u v ∨ (u = a ∧ v = b)) x y := by
  have hs : ∀ u v, (M.split a b).Step u v →
      Relation.EqvGen (fun u v => (M.split a b).Step u v ∨ (u = a ∧ v = b)) u v :=
    fun u v huv => Relation.EqvGen.rel _ _ (Or.inl huv)
  have hab : Relation.EqvGen (fun u v => (M.split a b).Step u v ∨ (u = a ∧ v = b)) a b :=
    Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩)
  rcases h with rfl | rfl
  · by_cases ha : M.σ x = a
    · rw [ha]
      refine (hs x b (Or.inl ?_)).trans _ _ _ (hab.symm _ _)
      simp [split, ha]
    · by_cases hb : M.σ x = b
      · rw [hb]
        refine (hs x a (Or.inl ?_)).trans _ _ _ hab
        simp [split, hb]
      · exact hs _ _ (Or.inl (by simp [split, swap_apply_of_ne_of_ne ha hb]))
  · exact hs _ _ (Or.inr rfl)

/-- **At most two components.**  If `M` is connected, every dart of the split map is connected
to `a` or to `b`. -/
theorem split_reach (hM : M.Connected) (x : M.D) :
    Relation.EqvGen (M.split a b).Step a x ∨ Relation.EqvGen (M.split a b).Step b x := by
  obtain ⟨T, hT⟩ : ∃ T : M.D → Prop, ∀ x, T x ↔
      (Relation.EqvGen (M.split a b).Step a x ∨ Relation.EqvGen (M.split a b).Step b x) :=
    ⟨_, fun _ => Iff.rfl⟩
  rw [← hT]
  have key : ∀ u v, Relation.EqvGen (fun u v => (M.split a b).Step u v ∨ (u = a ∧ v = b)) u v →
      (T u ↔ T v) := by
    intro u v h
    induction h with
    | rel u v h =>
      rcases h with h | ⟨hu, hv⟩
      · have e := Relation.EqvGen.rel _ _ h
        rw [hT, hT]
        exact ⟨fun h' => h'.imp (·.trans _ _ _ e) (·.trans _ _ _ e),
          fun h' => h'.imp (·.trans _ _ _ (e.symm _ _)) (·.trans _ _ _ (e.symm _ _))⟩
      · rw [hT, hT, hu, hv]
        exact ⟨fun _ => Or.inr (Relation.EqvGen.refl _),
          fun _ => Or.inl (Relation.EqvGen.refl _)⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hjoin : ∀ u v, Relation.EqvGen M.Step u v →
      Relation.EqvGen (fun u v => (M.split a b).Step u v ∨ (u = a ∧ v = b)) u v := by
    intro u v h
    induction h with
    | rel u v h => exact eqvGen_split_join_of_step h
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂
  exact (key a x (hjoin a x (hM a x))).1 ((hT a).2 (Or.inl (Relation.EqvGen.refl _)))

/-- If `a` and `b` are still connected after the split, the split map is connected. -/
theorem split_connected_of_eqvGen (hM : M.Connected)
    (h : Relation.EqvGen (M.split a b).Step a b) : (M.split a b).Connected := by
  refine (M.split a b).connected_of_base a fun x => ?_
  rcases split_reach hM x with hx | hx
  · exact hx
  · exact h.trans _ _ _ hx

/-- If `a` and `b` become disconnected by the split, they were in the same face of `M`. -/
theorem sameCycle_face_of_split_not_eqvGen (h : ¬ Relation.EqvGen (M.split a b).Step a b) :
    M.φ.SameCycle a b := by
  have h' : ¬ (M.split a b).φ.SameCycle a b := fun hs => h ((M.split a b).eqvGen_of_sameCycle_φ hs)
  have := sameCycle_swap_mul_left_right h'
  rwa [split_φ, swap_mul_swap_mul] at this

/-- **A split between two different faces of a connected map is connected.** -/
theorem split_connected (hM : M.Connected) (hφ : ¬ M.φ.SameCycle a b) :
    (M.split a b).Connected :=
  split_connected_of_eqvGen hM (by_contra fun h => hφ (sameCycle_face_of_split_not_eqvGen h))

end CombMap

end TheoremA.Picture
