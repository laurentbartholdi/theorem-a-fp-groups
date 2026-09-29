module

public import RequestProject.TheoremA.Lemma31.Picture.Split
public import RequestProject.TheoremA.Lemma31.Picture.EulerBound

/-!
# Components of combinatorial maps and the spherical split

* `numOrbits_subtypePerm_add` : orbits of a permutation are counted separately on an invariant
  subset and on its complement;
* `CombMap.restrict` : the submap on a set of darts invariant under `σ` and `α`, with
  `CombMap.euler_restrict_add` : `χ` is additive over an invariant set and its complement;
* `CombMap.component c`, `CombMap.componentCompl c` : the connected component of the dart `c`
  and the rest of the map; the component is connected (`component_connected`);
* `CombMap.split_sameFace_spherical` : **if `M` is connected with `χ(M) = 2` and `a ≠ b` are darts
  of the same vertex and of the same face, then the split map is disconnected, and it consists
  of exactly two components — the component of `a` and the component of `b` — each connected
  with `χ = 2`.**
-/

@[expose] public section

namespace TheoremA.Picture

open Equiv Function

/-- Orbits of a permutation are counted separately on an invariant set and its complement. -/
theorem numOrbits_subtypePerm_add {D : Type*} [Finite D] (π : Perm D) (p : D → Prop)
    (h : ∀ x, p (π x) ↔ p x) :
    numOrbits π = numOrbits (π.subtypePerm h) +
      numOrbits (π.subtypePerm (p := fun x => ¬ p x) fun x => not_congr (h x)) := by
  classical
  rw [← numOrbits_sumCongr]
  have hinv : ∀ {x y}, π.SameCycle x y → (p x ↔ p y) := fun hxy =>
    (SameCycle.eq_of_invariant (f := p) (fun x => propext (h x)) hxy) ▸ Iff.rfl
  let g : D → {x // p x} ⊕ {x // ¬ p x} := fun x => if hx : p x then .inl ⟨x, hx⟩ else .inr ⟨x, hx⟩
  refine numOrbits_eq_of_iff π (fun x => (⟦g x⟧ : Quotient (Perm.SameCycle.setoid _))) ?_ ?_
  · rintro ⟨(⟨x, hx⟩ | ⟨x, hx⟩)⟩
    · exact ⟨x, by simp [g, hx]; rfl⟩
    · exact ⟨x, by simp [g, hx]; rfl⟩
  · intro x y
    rw [Quotient.eq]
    change (Perm.sumCongr _ _).SameCycle (g x) (g y) ↔ _
    by_cases hx : p x <;> by_cases hy : p y
    · simp only [g, dif_pos hx, dif_pos hy, sameCycle_sumCongr_inl, Perm.sameCycle_subtypePerm]
    · simp only [g, dif_pos hx, dif_neg hy]
      exact ⟨fun h => absurd h not_sameCycle_sumCongr_inl_inr,
        fun h => absurd ((hinv h).1 hx) hy⟩
    · simp only [g, dif_neg hx, dif_pos hy]
      exact ⟨fun h => absurd h not_sameCycle_sumCongr_inr_inl,
        fun h => absurd ((hinv h).2 hy) hx⟩
    · simp only [g, dif_neg hx, dif_neg hy, sameCycle_sumCongr_inr, Perm.sameCycle_subtypePerm]

namespace CombMap

variable (M : CombMap)

/-- The submap on a set of darts invariant under the rotation and the edge involution. -/
def restrict (p : M.D → Prop) [DecidablePred p] (hσ : ∀ x, p (M.σ x) ↔ p x)
    (hα : ∀ x, p (M.α x) ↔ p x) : CombMap where
  D := {x // p x}
  σ := M.σ.subtypePerm hσ
  α := M.α.subtypePerm hα
  α_α := fun d => Subtype.ext (M.α_α d)
  α_ne := fun d h => M.α_ne d (congrArg Subtype.val h)

variable {M} (p : M.D → Prop) [DecidablePred p]

omit [DecidablePred p] in
theorem not_invariant_σ (hσ : ∀ x, p (M.σ x) ↔ p x) : ∀ x, ¬ p (M.σ x) ↔ ¬ p x := fun x => not_congr (hσ x)

omit [DecidablePred p] in
theorem not_invariant_α (hα : ∀ x, p (M.α x) ↔ p x) : ∀ x, ¬ p (M.α x) ↔ ¬ p x := fun x => not_congr (hα x)

omit [DecidablePred p] in
theorem invariant_φ (hσ : ∀ x, p (M.σ x) ↔ p x) (hα : ∀ x, p (M.α x) ↔ p x) : ∀ x, p (M.φ x) ↔ p x := fun x => (hσ _).trans (hα x)

theorem restrict_φ (hσ : ∀ x, p (M.σ x) ↔ p x) (hα : ∀ x, p (M.α x) ↔ p x) : (M.restrict p hσ hα).φ = M.φ.subtypePerm (invariant_φ p hσ hα) := by
  ext x; rfl

/-- **Additivity of `χ`** over an invariant set of darts and its complement. -/
theorem euler_restrict_add (hσ : ∀ x, p (M.σ x) ↔ p x) (hα : ∀ x, p (M.α x) ↔ p x) : M.euler = (M.restrict p hσ hα).euler +
    (M.restrict (fun x => ¬ p x) (not_invariant_σ p hσ) (not_invariant_α p hα)).euler := by
  have hV := numOrbits_subtypePerm_add M.σ p hσ
  have hE := numOrbits_subtypePerm_add M.α p hα
  have hF := numOrbits_subtypePerm_add M.φ p (invariant_φ p hσ hα)
  have hF1 := restrict_φ p hσ hα
  have hF2 := restrict_φ (fun x => ¬ p x) (not_invariant_σ p hσ) (not_invariant_α p hα)
  unfold euler numVertices numEdges numFaces
  rw [hF1, hF2]
  simp only [restrict] at *
  push_cast [hV, hE, hF]
  ring

omit [DecidablePred p] in
/-- Invariant sets are unions of components. -/
theorem invariant_of_eqvGen (hσ : ∀ x, p (M.σ x) ↔ p x) (hα : ∀ x, p (M.α x) ↔ p x) {u v : M.D} (h : Relation.EqvGen M.Step u v) : p u ↔ p v := by
  induction h with
  | rel u v h => rcases h with rfl | rfl
                 · exact (hσ u).symm
                 · exact (hα u).symm
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A restriction whose darts are all connected (in `M`) to one of its darts is connected. -/
theorem restrict_connected (hσ : ∀ x, p (M.σ x) ↔ p x) (hα : ∀ x, p (M.α x) ↔ p x) (c : M.D) (hc : p c)
    (hreach : ∀ x, p x → Relation.EqvGen M.Step c x) : (M.restrict p hσ hα).Connected := by
  have key : ∀ u v, Relation.EqvGen M.Step u v → ∀ (hu : p u) (hv : p v),
      Relation.EqvGen (M.restrict p hσ hα).Step ⟨u, hu⟩ ⟨v, hv⟩ := by
    intro u v h
    induction h with
    | rel u v h =>
      intro hu hv
      refine Relation.EqvGen.rel _ _ ?_
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    | refl => intro _ _; exact Relation.EqvGen.refl _
    | symm u v _ ih => intro hu hv; exact (ih hv hu).symm
    | trans u w v huw _ ih₁ ih₂ =>
      intro hu hv
      have hw : p w := (invariant_of_eqvGen p hσ hα huw).1 hu
      exact (ih₁ hu hw).trans _ _ _ (ih₂ hw hv)
  refine connected_of_base _ ⟨c, hc⟩ ?_
  rintro ⟨x, hx⟩
  exact key c x (hreach x hx) hc hx

/-! ### The component of a dart -/

variable (M) (c : M.D)

theorem component_invariant_σ : ∀ x, Relation.EqvGen M.Step c (M.σ x) ↔
    Relation.EqvGen M.Step c x := fun x =>
  ⟨fun h => h.trans _ _ _ ((Relation.EqvGen.rel x (M.σ x) (Or.inl rfl)).symm _ _),
    fun h => h.trans _ _ _ (Relation.EqvGen.rel x (M.σ x) (Or.inl rfl))⟩

theorem component_invariant_α : ∀ x, Relation.EqvGen M.Step c (M.α x) ↔
    Relation.EqvGen M.Step c x := fun x =>
  ⟨fun h => h.trans _ _ _ ((Relation.EqvGen.rel x (M.α x) (Or.inr rfl)).symm _ _),
    fun h => h.trans _ _ _ (Relation.EqvGen.rel x (M.α x) (Or.inr rfl))⟩

open Classical in
/-- The connected component of the dart `c`. -/
noncomputable def component : CombMap :=
  M.restrict (fun x => Relation.EqvGen M.Step c x) (M.component_invariant_σ c)
    (M.component_invariant_α c)

open Classical in
/-- The darts not connected to `c`. -/
noncomputable def componentCompl : CombMap :=
  M.restrict (fun x => ¬ Relation.EqvGen M.Step c x)
    (not_invariant_σ _ (M.component_invariant_σ c)) (not_invariant_α _ (M.component_invariant_α c))

/-- `χ` is the sum over the component of `c` and the rest. -/
theorem euler_component_add : M.euler = (M.component c).euler + (M.componentCompl c).euler := by
  classical
  exact euler_restrict_add _ (M.component_invariant_σ c) (M.component_invariant_α c)

/-- The component of a dart is connected. -/
theorem component_connected : (M.component c).Connected := by
  classical
  exact restrict_connected _ _ _ c (Relation.EqvGen.refl _) fun _ h => h

/-- If every dart outside the component of `c` is connected to `d`, the rest is connected. -/
theorem componentCompl_connected (d : M.D) (hd : ¬ Relation.EqvGen M.Step c d)
    (h : ∀ x, ¬ Relation.EqvGen M.Step c x → Relation.EqvGen M.Step d x) :
    (M.componentCompl c).Connected := by
  classical
  exact restrict_connected _ _ _ d hd h

/-! ### Splitting a spherical map inside one face -/

variable {M} {a b : M.D}

/-- **Splitting a spherical map at a vertex inside one face.**  If `M` is connected with
`χ(M) = 2`, and `a ≠ b` lie in the same vertex and in the same face, then the split map is
disconnected (`a` and `b` are no longer connected), its total Euler characteristic is `4`, and it
consists of exactly two parts, the component of `a` and the component of `b` (the complement of
the component of `a`), each connected with `χ = 2`. -/
theorem split_sameFace_spherical (hM : M.Connected) (hχ : M.euler = 2) (hab : a ≠ b)
    (hσ : M.σ.SameCycle a b) (hφ : M.φ.SameCycle a b) :
    ¬ Relation.EqvGen (M.split a b).Step a b ∧
    (M.split a b).euler = 4 ∧
    (∀ x, Relation.EqvGen (M.split a b).Step a x ∨ Relation.EqvGen (M.split a b).Step b x) ∧
    ((M.split a b).component a).Connected ∧ ((M.split a b).component a).euler = 2 ∧
    ((M.split a b).componentCompl a).Connected ∧ ((M.split a b).componentCompl a).euler = 2 := by
  have h4 : (M.split a b).euler = 4 := by rw [split_euler_of_sameCycle_face hab hσ hφ, hχ]; rfl
  have hdis : ¬ Relation.EqvGen (M.split a b).Step a b := by
    intro h
    have := (M.split a b).euler_le_two (split_connected_of_eqvGen hM h)
    omega
  have hreach := split_reach (a := a) (b := b) hM
  have hc1 := (M.split a b).component_connected a
  have hc2 := (M.split a b).componentCompl_connected a b hdis
    fun x hx => (hreach x).resolve_left hx
  have hadd := (M.split a b).euler_component_add a
  have hle1 := ((M.split a b).component a).euler_le_two hc1
  have hle2 := ((M.split a b).componentCompl a).euler_le_two hc2
  refine ⟨hdis, h4, hreach, hc1, ?_, hc2, ?_⟩ <;> omega

end CombMap

end TheoremA.Picture
