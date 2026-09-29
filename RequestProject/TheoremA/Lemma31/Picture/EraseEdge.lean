module

public import RequestProject.TheoremA.Lemma31.Picture.Erase

/-!
# Deleting an edge by erasing its two darts

For a combinatorial map `M`, a permutation `π` of its darts (the rotation before erasure, usually
`M.σ` or a modification of it) and a dart `a` with partner `b = α a`,
`M.eraseEdge π a` is the map on the retained darts `x ≠ a, b` with

* rotation `erase2 π a b` restricted to the retained darts (first return of `π`);
* edge involution `α` restricted (the edge `{a, b}` is removed; `α` preserves the retained darts).

Counts:

* `eraseEdge_numVertices` : `V' + 2 = #cycles (erase2 π a b)`;
* `eraseEdge_numEdges` : `E' + 1 = E`;
* `eraseEdge_φ_val`, `eraseEdge_numFaces` : the faces are the first-return map of
  `swap a b * π * α` (`φ' = erase_{a,b}(swap a b * π * α)` on retained darts), and
  `F' + 2 = #cycles (erase2 (swap a b * π * α) a b)`.

Connectivity is transported along a map `g` of darts into the retained darts
(`eraseEdge_connected_of`, `eqvGen_map`).
-/

@[expose] public section

namespace TheoremA.Picture

open Equiv Function

namespace CombMap

variable (M : CombMap)

/-- The same darts and edges with another rotation. -/
def withσ (σ' : Perm M.D) : CombMap where
  D := M.D
  σ := σ'
  α := M.α
  α_α := M.α_α
  α_ne := M.α_ne

theorem α_retained_iff (a : M.D) (x : M.D) :
    (M.α x ≠ a ∧ M.α x ≠ M.α a) ↔ (x ≠ a ∧ x ≠ M.α a) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => h2 (by rw [h]), fun h => h1 (by rw [h, M.α_α])⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => h2 (by rw [← h, M.α_α]), fun h => h1 (M.α.injective h)⟩

theorem ne_α (a : M.D) : a ≠ M.α a := fun h => M.α_ne a h.symm

/-- **Deleting the edge `{a, α a}`**: the rotation is `erase2 π a (α a)` (first return of `π` to
the retained darts), the edge involution is restricted. -/
def eraseEdge (π : Perm M.D) (a : M.D) : CombMap :=
  (M.withσ (erase2 π a (M.α a))).restrict (fun x => x ≠ a ∧ x ≠ M.α a)
    (erase2_retained_iff (M.ne_α a)) (M.α_retained_iff a)

variable {M} (π : Perm M.D) (a : M.D)

theorem eraseEdge_σ_val (x : (M.eraseEdge π a).D) :
    ((M.eraseEdge π a).σ x).val = erase2 π a (M.α a) x.val := rfl

theorem eraseEdge_α_val (x : (M.eraseEdge π a).D) :
    ((M.eraseEdge π a).α x).val = M.α x.val := rfl

theorem eraseEdge_numVertices :
    (M.eraseEdge π a).numVertices + 2 = numOrbits (erase2 π a (M.α a)) :=
  numOrbits_subtypePerm_fix2 (M.ne_α a) (erase2_apply_left (M.ne_α a)) erase2_apply_right
    (erase2_retained_iff (M.ne_α a))

theorem eraseEdge_numEdges : (M.eraseEdge π a).numEdges + 1 = M.numEdges := by
  unfold numEdges
  rw [numOrbits_subtypePerm_add M.α (fun x => x ≠ a ∧ x ≠ M.α a) (M.α_retained_iff a)]
  congr 1
  have hmem : ∀ z : {x // ¬ (x ≠ a ∧ x ≠ M.α a)}, z.val = a ∨ z.val = M.α a := by
    rintro ⟨z, hz⟩
    by_contra h'
    push_neg at h'
    exact hz h'
  rw [numOrbits_eq_of_iff _ (fun _ => ()), Nat.card_unique]
  · intro u; exact ⟨⟨a, by simp⟩, rfl⟩
  · intro z w
    simp only [true_iff]
    rw [Perm.sameCycle_subtypePerm]
    have key : M.α.SameCycle a (M.α a) := ⟨1, by simp⟩
    rcases hmem z with e1 | e1 <;> rcases hmem w with e2 | e2 <;> rw [e1, e2] <;>
      first | exact key | exact key.symm

/-- **The faces after deleting an edge**: the face permutation of `M.eraseEdge π a` is the
first-return map of `swap a b * π * α` to the retained darts. -/
theorem eraseEdge_φ_val (x : (M.eraseEdge π a).D) :
    ((M.eraseEdge π a).φ x).val = erase2 (swap a (M.α a) * π * M.α) a (M.α a) x.val :=
  erase2_apply_α M.α_α (M.ne_α a) rfl x.2.1 x.2.2

theorem eraseEdge_numFaces :
    (M.eraseEdge π a).numFaces + 2 =
      numOrbits (erase2 (swap a (M.α a) * π * M.α) a (M.α a)) := by
  have hφ : (M.eraseEdge π a).φ = (erase2 (swap a (M.α a) * π * M.α) a (M.α a)).subtypePerm
      (p := fun x => x ≠ a ∧ x ≠ M.α a) (erase2_retained_iff (M.ne_α a)) := by
    exact Equiv.ext fun x => Subtype.ext (eraseEdge_φ_val π a x)
  unfold numFaces
  rw [hφ]
  exact numOrbits_subtypePerm_fix2 (M.ne_α a) (erase2_apply_left (M.ne_α a)) erase2_apply_right
    (erase2_retained_iff (M.ne_α a))

theorem eraseEdge_euler :
    (M.eraseEdge π a).euler + 3 = (numOrbits (erase2 π a (M.α a)) : ℤ) - M.numEdges +
      numOrbits (erase2 (swap a (M.α a) * π * M.α) a (M.α a)) := by
  have hV := eraseEdge_numVertices π a
  have hE := eraseEdge_numEdges π a
  have hF := eraseEdge_numFaces π a
  unfold euler
  push_cast [← hV, ← hE, ← hF]
  ring

theorem eraseEdge_sameCycle_iff {x y : (M.eraseEdge π a).D} :
    (M.eraseEdge π a).σ.SameCycle x y ↔ π.SameCycle x.val y.val := by
  rw [show (M.eraseEdge π a).σ.SameCycle x y ↔ (erase2 π a (M.α a)).SameCycle x.val y.val from
    Perm.sameCycle_subtypePerm (h := erase2_retained_iff (M.ne_α a))]
  exact sameCycle_erase2_iff x.2.1 x.2.2 y.2.1 y.2.2

theorem eraseEdge_cycleWord {G : Type*} [Monoid G] (f : M.D → G) (x : (M.eraseEdge π a).D) :
    cycleWord (M.eraseEdge π a).σ (f ∘ Subtype.val) x = cycleWord (erase2 π a (M.α a)) f x.val :=
  restrict_cycleWord (M := M.withσ (erase2 π a (M.α a))) _ _ _ f x

/-! ### Connectivity -/

/-- Transporting a connection along a map of darts. -/
theorem eqvGen_map {r : M.D → M.D → Prop} (g : M.D → M.D)
    (hσ : ∀ y, Relation.EqvGen r (g y) (g (M.σ y)))
    (hα : ∀ y, Relation.EqvGen r (g y) (g (M.α y))) {u v : M.D}
    (h : Relation.EqvGen M.Step u v) : Relation.EqvGen r (g u) (g v) := by
  induction h with
  | rel u v h =>
    rcases h with rfl | rfl
    · exact hσ u
    · exact hα u
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

/-- Connections through retained darts in the full dart set give connections in `eraseEdge`. -/
theorem eraseEdge_eqvGen {u v : M.D}
    (h : Relation.EqvGen (M.withσ (erase2 π a (M.α a))).Step u v)
    (hu : u ≠ a ∧ u ≠ M.α a) (hv : v ≠ a ∧ v ≠ M.α a) :
    Relation.EqvGen (M.eraseEdge π a).Step ⟨u, hu⟩ ⟨v, hv⟩ := by
  have hσ := erase2_retained_iff (π := π) (M.ne_α a)
  have hα := M.α_retained_iff a
  induction h with
  | rel u v h =>
    refine Relation.EqvGen.rel _ _ ?_
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  | refl => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact (ih hv hu).symm
  | trans u w v huw _ ih₁ ih₂ =>
    have hw : w ≠ a ∧ w ≠ M.α a :=
      (invariant_of_eqvGen (M := M.withσ (erase2 π a (M.α a))) (fun x => x ≠ a ∧ x ≠ M.α a)
        hσ hα huw).1 hu
    exact (ih₁ hu hw).trans _ _ _ (ih₂ hw hv)

/-- **Connectivity after deleting an edge**, transported along `g : D → D` with values in the
retained darts, identity on retained darts, and sending every old step to a connection in the
new map. -/
theorem eraseEdge_connected_of (hM : M.Connected) (g : M.D → M.D) (hgid : ∀ y, y ≠ a → y ≠ M.α a → g y = y)
    (hσ : ∀ y, Relation.EqvGen (M.withσ (erase2 π a (M.α a))).Step (g y) (g (M.σ y)))
    (hα : ∀ y, Relation.EqvGen (M.withσ (erase2 π a (M.α a))).Step (g y) (g (M.α y))) :
    (M.eraseEdge π a).Connected := by
  intro x y
  have hx := eqvGen_map g hσ hα (hM x.val y.val)
  rw [hgid _ x.2.1 x.2.2, hgid _ y.2.1 y.2.2] at hx
  exact eraseEdge_eqvGen π a hx x.2 y.2

/-- A step of the rotation `erase2 π a b` in the full dart set. -/
theorem withσ_eqvGen_of_sameCycle {σ' : Perm M.D} {x y : M.D} (h : σ'.SameCycle x y) :
    Relation.EqvGen (M.withσ σ').Step x y :=
  (M.withσ σ').eqvGen_of_sameCycle h

theorem withσ_eqvGen_α {σ' : Perm M.D} (x : M.D) :
    Relation.EqvGen (M.withσ σ').Step x (M.α x) :=
  Relation.EqvGen.rel _ _ (Or.inr rfl)

/-- A connected map has no darts outside the component of any dart; its component has the same
number of edges. -/
theorem numEdges_component_of_connected (N : CombMap) (hN : N.Connected) (c : N.D) :
    (N.component c).numEdges = N.numEdges := by
  have h := N.numEdges_component_add c
  have h0 : (N.componentCompl c).numEdges = 0 := by
    haveI : IsEmpty (N.componentCompl c).D := ⟨fun x => x.2 (hN c x.1)⟩
    unfold numEdges numOrbits
    simp
  omega

end CombMap

end TheoremA.Picture
