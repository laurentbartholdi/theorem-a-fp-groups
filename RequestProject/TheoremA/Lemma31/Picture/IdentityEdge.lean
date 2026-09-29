module

public import RequestProject.TheoremA.Lemma31.Picture.Consolidate

/-!
# Removing an identity-labelled marked edge

Let `R` be a raw picture for `x ≠ 1`, and `d` a dart at the marked vertex whose letter is the
identity (`(R.lab d).2 = 1`); its partner `u = α d` is ordinary (this is part of the raw-picture
conditions) and also carries the identity.  Since `x ≠ 1`, the marked vertex has at least two
darts (`σ d ≠ d`).  Delete the edge `{d, u}`: rotation `erase_{d,u}(σ)`, all other labels kept;
the new base is `σ d` if `d` was the base, and the old base otherwise (`deleteIdBase`).

* **Leaf endpoint** (`σ u = u`, `deleteId_leaf`): connected, `V' = V - 1`, `E' = E - 1`, `F' = F`.
* **Both endpoints of degree `≥ 2`, `d, u` in different faces** (`deleteId_diffFace`): connected,
  `V' = V`, `E' = E - 1`, `F' = F - 1`.
* **Both endpoints of degree `≥ 2`, `d, u` in the same face** (`deleteId_sameFace`): `V' = V`,
  `E' = E - 1`, `F' = F + 1`, total `χ = 4`, the map is disconnected, and it has exactly two
  components — the component of the marked vertex and its complement — each connected with
  `χ = 2`.  The component of the marked vertex is kept.

In every case the result is a raw picture for the **same** element `x` with strictly fewer edges
(`exists_fewer_edges_of_identity`).
-/

@[expose] public section

namespace TheoremA

universe u w

namespace ConeComplex

open Picture Equiv Function

variable {V T : Type w} {C : ConeComplex.{u, w} V T} {x : Monoid.CoprodI C.loc}

namespace RawPicture

variable (R : C.RawPicture x) {d : R.M.D}

section IdentityEdge

variable (hx : x ≠ 1) (hd : R.M.σ.SameCycle R.base d) (h1 : (R.lab d).2 = 1)

/-- The new base dart: `σ d` if `d` was the base, the old base otherwise. -/
def deleteIdBase (d : R.M.D) : R.M.D := if R.base = d then R.M.σ d else R.base

include hd

theorem not_marked_αd : ¬ R.M.σ.SameCycle R.base (R.M.α d) := (R.edge_boundary d hd).1

theorem d_ne_αd : d ≠ R.M.α d := fun h => R.not_marked_αd hd (h ▸ hd)

theorem marked_σd : R.M.σ.SameCycle R.base (R.M.σ d) := hd.trans ⟨1, by simp⟩

theorem σd_ne_αd : R.M.σ d ≠ R.M.α d := fun h => R.not_marked_αd hd (h ▸ R.marked_σd hd)

theorem σαd_ne_d : R.M.σ (R.M.α d) ≠ d := by
  intro h
  have : R.M.σ.SameCycle (R.M.α d) d := ⟨1, by simpa using h⟩
  exact R.not_marked_αd hd (hd.trans this.symm)

theorem marked_deleteIdBase : R.M.σ.SameCycle R.base (R.deleteIdBase d) := by
  unfold deleteIdBase
  split_ifs
  · exact R.marked_σd hd
  · exact Perm.SameCycle.refl _ _

theorem deleteIdBase_ne_αd : R.deleteIdBase d ≠ R.M.α d := fun h =>
  R.not_marked_αd hd (h ▸ R.marked_deleteIdBase hd)

theorem marked_iff_deleteIdBase {z : R.M.D} :
    R.M.σ.SameCycle (R.deleteIdBase d) z ↔ R.M.σ.SameCycle R.base z :=
  ⟨fun h => (R.marked_deleteIdBase hd).trans h, fun h => (R.marked_deleteIdBase hd).symm.trans h⟩

include h1

omit hd in
theorem word_d : C.letterWord (R.lab d) = 1 := by
  change Monoid.CoprodI.of (R.lab d).2 = 1
  rw [h1, map_one]

theorem word_αd : C.letterWord (R.lab (R.M.α d)) = 1 := by
  rw [(R.edge_boundary d hd).2, letterWord_inv, R.word_d h1, inv_one]

include hx

theorem σd_ne_d : R.M.σ d ≠ d := by
  intro h
  have hb : d = R.base := hd.symm.eq_of_left h
  apply hx
  rw [← R.boundary_word, ← hb, cycleWord_of_fixed _ h]
  exact R.word_d h1

theorem deleteIdBase_ne_d : R.deleteIdBase d ≠ d := by
  unfold deleteIdBase
  split_ifs with h
  · exact R.σd_ne_d hx hd h1
  · exact h

/-- The labelled map after deleting the identity edge `{d, α d}` (before choosing a
component). -/
def deleteIdPre : C.PrePicture x :=
  PrePicture.ofEraseEdge R.M R.M.σ d R.lab (R.deleteIdBase d)
    ⟨R.deleteIdBase_ne_d hx hd h1, R.deleteIdBase_ne_αd hd⟩
    (by
      intro z hz1 hz2 hz
      rw [R.marked_iff_deleteIdBase hd] at hz
      have hw1 := erase2_apply_ne_left (π := R.M.σ) (R.d_ne_αd hd) hz1
      have hw2 := erase2_apply_ne_right (π := R.M.σ) (a := d) hz2
      have hw : R.M.σ.SameCycle z (erase2 R.M.σ d (R.M.α d) z) :=
        (sameCycle_erase2_iff hz1 hz2 hw1 hw2).1 ⟨1, by simp⟩
      exact R.type_eq_of_sameCycle hz hw)
    (by
      intro z hz1 hz2 hz
      rw [R.marked_iff_deleteIdBase hd] at hz
      rw [cycleWord_erase2 _ hz1 hz2 (R.word_d h1) (R.word_αd hd h1)]
      exact R.local_eq z hz)
    (by
      intro z _ _ hz hz'
      rw [R.marked_iff_deleteIdBase hd] at hz hz'
      exact R.edge_interior z hz hz')
    (by
      intro z _ _ hz
      rw [R.marked_iff_deleteIdBase hd] at hz ⊢
      exact R.edge_boundary z hz)
    (by
      have hb1 := R.deleteIdBase_ne_d hx hd h1
      have hb2 := R.deleteIdBase_ne_αd hd
      rw [cycleWord_erase2 _ hb1 hb2 (R.word_d h1) (R.word_αd hd h1)]
      unfold deleteIdBase
      split_ifs with hb
      · rw [cycleWord_apply]
        simp only [Function.comp_apply, R.word_d h1, inv_one, one_mul, mul_one]
        rw [← hb]
        exact R.boundary_word
      · exact R.boundary_word)

theorem deleteIdPre_M : (R.deleteIdPre hx hd h1).M = R.M.eraseEdge R.M.σ d := rfl

/-! ### Counts -/

theorem deleteId_numVertices :
    (R.M.eraseEdge R.M.σ d).numVertices + 1 =
      R.M.numVertices + (if R.M.σ (R.M.α d) = R.M.α d then 0 else 1) := by
  have hA := CombMap.eraseEdge_numVertices R.M.σ d
  have hB := numOrbits_erase2 R.M.σ d (R.M.α d)
  have h5 : erasePt R.M.σ d (R.M.α d) = R.M.σ (R.M.α d) :=
    erasePt_apply_of_ne (R.d_ne_αd hd).symm (R.σαd_ne_d hd)
  rw [if_neg (R.σd_ne_d hx hd h1), h5] at hB
  unfold CombMap.numVertices at hA ⊢
  split_ifs at hB ⊢ <;> omega

theorem deleteId_numFaces :
    (R.M.eraseEdge R.M.σ d).numFaces + 1 =
      numOrbits (swap d (R.M.α d) * R.M.φ) +
        (if R.M.σ (R.M.α d) = R.M.α d then 0 else 1) := by
  have hA := CombMap.eraseEdge_numFaces R.M.σ d
  have hB := numOrbits_erase2 (Equiv.swap d (R.M.α d) * R.M.σ * R.M.α) d (R.M.α d)
  have hχ : Equiv.swap d (R.M.α d) * R.M.σ * R.M.α = swap d (R.M.α d) * R.M.φ := by
    rw [mul_assoc]; rfl
  have hχu : (Equiv.swap d (R.M.α d) * R.M.σ * R.M.α) (R.M.α d) = R.M.σ d := by
    change swap d (R.M.α d) (R.M.σ (R.M.α (R.M.α d))) = _
    rw [R.M.α_α]
    exact swap_apply_of_ne_of_ne (R.σd_ne_d hx hd h1) (R.σd_ne_αd hd)
  have h5 : erasePt (Equiv.swap d (R.M.α d) * R.M.σ * R.M.α) d (R.M.α d) ≠ R.M.α d := by
    rw [erasePt_apply_of_ne (R.d_ne_αd hd).symm (by rw [hχu]; exact R.σd_ne_d hx hd h1), hχu]
    exact R.σd_ne_αd hd
  have hχd : (Equiv.swap d (R.M.α d) * R.M.σ * R.M.α) d = swap d (R.M.α d) (R.M.σ (R.M.α d)) :=
    rfl
  rw [if_neg h5, hχd, hχ] at hB
  by_cases hleaf : R.M.σ (R.M.α d) = R.M.α d
  · rw [hleaf, swap_apply_right, if_pos rfl] at hB
    rw [if_pos hleaf]
    rw [hχ] at hA
    omega
  · have hne : R.M.σ (R.M.α d) ≠ d := R.σαd_ne_d hd
    rw [swap_apply_of_ne_of_ne hne hleaf, if_neg hne] at hB
    rw [if_neg hleaf]
    rw [hχ] at hA
    omega

omit hx h1 in
theorem numOrbits_swap_φ_of_sameFace (hφ : R.M.φ.SameCycle d (R.M.α d)) :
    numOrbits (swap d (R.M.α d) * R.M.φ) = R.M.numFaces + 1 :=
  numOrbits_swap_mul_split (R.d_ne_αd hd) hφ

omit hd hx h1 in
theorem numOrbits_swap_φ_of_diffFace (hφ : ¬ R.M.φ.SameCycle d (R.M.α d)) :
    numOrbits (swap d (R.M.α d) * R.M.φ) + 1 = R.M.numFaces :=
  (numOrbits_swap_mul hφ).symm

/-! ### Connectivity -/

/-- The image of `u = α d` under the retraction: `σ d` if `u` is a leaf, `σ u` otherwise. -/
def deleteIdUImg (d : R.M.D) : R.M.D :=
  if R.M.σ (R.M.α d) = R.M.α d then R.M.σ d else R.M.σ (R.M.α d)

/-- The retraction of darts used to transport old paths. -/
def deleteIdRetract (d : R.M.D) (z : R.M.D) : R.M.D :=
  if z = d then R.M.σ d else if z = R.M.α d then R.deleteIdUImg d else z

omit hd hx h1 in
theorem deleteIdRetract_d : R.deleteIdRetract d d = R.M.σ d := by
  simp [deleteIdRetract]

omit hx h1 in
theorem deleteIdRetract_u : R.deleteIdRetract d (R.M.α d) = R.deleteIdUImg d := by
  unfold deleteIdRetract
  rw [if_neg (R.d_ne_αd hd).symm, if_pos rfl]

omit hd hx h1 in
theorem deleteIdRetract_of_ne {z : R.M.D} (h1 : z ≠ d) (h2 : z ≠ R.M.α d) :
    R.deleteIdRetract d z = z := by
  unfold deleteIdRetract
  rw [if_neg h1, if_neg h2]

omit hd hx h1 in
theorem deleteIdUImg_of_leaf (h : R.M.σ (R.M.α d) = R.M.α d) :
    R.deleteIdUImg d = R.M.σ d := if_pos h

omit hd hx h1 in
theorem deleteIdUImg_of_not_leaf (h : R.M.σ (R.M.α d) ≠ R.M.α d) :
    R.deleteIdUImg d = R.M.σ (R.M.α d) := if_neg h

theorem deleteId_stepσ (y : R.M.D) :
    Relation.EqvGen (R.M.withσ (erase2 R.M.σ d (R.M.α d))).Step
      (R.deleteIdRetract d y) (R.deleteIdRetract d (R.M.σ y)) := by
  have hσd := R.σd_ne_d hx hd h1
  have hσdu := R.σd_ne_αd hd
  have hne := R.σαd_ne_d hd
  have hSC : ∀ y z, (y ≠ d ∧ y ≠ R.M.α d) → (z ≠ d ∧ z ≠ R.M.α d) → R.M.σ.SameCycle y z →
      Relation.EqvGen (R.M.withσ (erase2 R.M.σ d (R.M.α d))).Step y z := fun y z hy hz h =>
    CombMap.withσ_eqvGen_of_sameCycle ((sameCycle_erase2_iff hy.1 hy.2 hz.1 hz.2).2 h)
  have hσ1 : ∀ y, R.M.σ.SameCycle y (R.M.σ y) := fun y => ⟨1, by simp⟩
  by_cases hyd : y = d
  · subst hyd
    rw [R.deleteIdRetract_d, R.deleteIdRetract_of_ne hσd hσdu]
    exact Relation.EqvGen.refl _
  by_cases hyu : y = R.M.α d
  · subst hyu
    rw [R.deleteIdRetract_u hd]
    by_cases hleaf : R.M.σ (R.M.α d) = R.M.α d
    · rw [hleaf, R.deleteIdRetract_u hd]
      exact Relation.EqvGen.refl _
    · rw [R.deleteIdRetract_of_ne hne hleaf, R.deleteIdUImg_of_not_leaf hleaf]
      exact Relation.EqvGen.refl _
  rw [R.deleteIdRetract_of_ne hyd hyu]
  by_cases h2 : R.M.σ y = d
  · rw [h2, R.deleteIdRetract_d (d := d)]
    exact hSC _ _ ⟨hyd, hyu⟩ ⟨hσd, hσdu⟩ (by rw [← h2]; exact (hσ1 y).trans (hσ1 _))
  by_cases h3 : R.M.σ y = R.M.α d
  · have hleaf : R.M.σ (R.M.α d) ≠ R.M.α d := fun h => hyu (R.M.σ.injective (h3.trans h.symm))
    rw [h3, R.deleteIdRetract_u hd, R.deleteIdUImg_of_not_leaf hleaf]
    exact hSC _ _ ⟨hyd, hyu⟩ ⟨hne, hleaf⟩ (by rw [← h3]; exact (hσ1 y).trans (hσ1 _))
  rw [R.deleteIdRetract_of_ne h2 h3]
  exact hSC _ _ ⟨hyd, hyu⟩ ⟨h2, h3⟩ (hσ1 y)

omit hd hx h1 in
theorem deleteId_stepα {y : R.M.D} (hyd : y ≠ d) (hyu : y ≠ R.M.α d) :
    Relation.EqvGen (R.M.withσ (erase2 R.M.σ d (R.M.α d))).Step
      (R.deleteIdRetract d y) (R.deleteIdRetract d (R.M.α y)) := by
  have h1' : R.M.α y ≠ d := fun h => hyu (by rw [← h, R.M.α_α])
  have h2' : R.M.α y ≠ R.M.α d := fun h => hyd (R.M.α.injective h)
  rw [R.deleteIdRetract_of_ne hyd hyu, R.deleteIdRetract_of_ne h1' h2']
  exact CombMap.withσ_eqvGen_α y

/-- Connectivity, given a connection between the two ends of the deleted edge. -/
theorem deleteId_connected_of
    (hkey : Relation.EqvGen (R.M.withσ (erase2 R.M.σ d (R.M.α d))).Step
      (R.deleteIdRetract d d) (R.deleteIdRetract d (R.M.α d))) :
    (R.M.eraseEdge R.M.σ d).Connected := by
  refine CombMap.eraseEdge_connected_of R.M.σ d R.connected (R.deleteIdRetract d)
    (fun y hy1 hy2 => R.deleteIdRetract_of_ne hy1 hy2)
    (R.deleteId_stepσ hx hd h1) fun y => ?_
  by_cases hyd : y = d
  · subst hyd; exact hkey
  by_cases hyu : y = R.M.α d
  · subst hyu; rw [R.M.α_α]; exact hkey.symm _ _
  exact R.deleteId_stepα hyd hyu

/-- **Leaf endpoint.** -/
theorem deleteId_leaf (hleaf : R.M.σ (R.M.α d) = R.M.α d) :
    (R.M.eraseEdge R.M.σ d).Connected ∧ (R.M.eraseEdge R.M.σ d).euler = 2 ∧
    (R.M.eraseEdge R.M.σ d).numVertices + 1 = R.M.numVertices ∧
    (R.M.eraseEdge R.M.σ d).numEdges + 1 = R.M.numEdges ∧
    (R.M.eraseEdge R.M.σ d).numFaces = R.M.numFaces := by
  have hV := R.deleteId_numVertices hx hd h1
  have hF := R.deleteId_numFaces hx hd h1
  have hE := CombMap.eraseEdge_numEdges (M := R.M) R.M.σ d
  have hφ : R.M.φ.SameCycle d (R.M.α d) := ⟨1, by
    change R.M.σ (R.M.α d) = R.M.α d
    exact hleaf⟩
  have hs := R.numOrbits_swap_φ_of_sameFace hd hφ
  rw [if_pos hleaf] at hV hF
  have hconn : (R.M.eraseEdge R.M.σ d).Connected := by
    refine R.deleteId_connected_of hx hd h1 ?_
    rw [R.deleteIdRetract_d (d := d), R.deleteIdRetract_u hd, R.deleteIdUImg_of_leaf hleaf]
    exact Relation.EqvGen.refl _
  refine ⟨hconn, ?_, by omega, hE, by omega⟩
  have h := R.spherical
  unfold CombMap.euler at h ⊢
  omega

/-- The face walk: if `d`, `u` lie in different faces (and `u` is not a leaf), the two darts
following them at their vertices are still connected after deleting the edge. -/
theorem deleteId_key_of_diffFace (hleaf : R.M.σ (R.M.α d) ≠ R.M.α d)
    (hφ : ¬ R.M.φ.SameCycle d (R.M.α d)) :
    Relation.EqvGen (R.M.withσ (erase2 R.M.σ d (R.M.α d))).Step
      (R.M.σ (R.M.α d)) (R.M.σ d) := by
  classical
  set u := R.M.α d with hu
  set N := R.M.withσ (erase2 R.M.σ d u) with hN
  have hσd := R.σd_ne_d hx hd h1
  have hdu := R.d_ne_αd hd
  have hne : R.M.σ u ≠ d := R.σαd_ne_d hd
  -- one face step between retained darts is a connection
  have hfstep : ∀ y, y ≠ d → y ≠ u → R.M.φ y ≠ d → R.M.φ y ≠ u →
      Relation.EqvGen N.Step y (R.M.φ y) := by
    intro y hy1 hy2 hy3 hy4
    have ha1 : R.M.α y ≠ d := fun h => hy2 (by rw [hu, ← h, R.M.α_α])
    have ha2 : R.M.α y ≠ u := fun h => hy1 (R.M.α.injective h)
    have e : erase2 R.M.σ d u (R.M.α y) = R.M.φ y := erase2_apply_of_notMem ha1 ha2 hy3 hy4
    exact (CombMap.withσ_eqvGen_α (σ' := erase2 R.M.σ d u) y).trans _ _ _
      (Relation.EqvGen.rel _ _ (Or.inl e.symm))
  have hex : ∃ n : ℕ, (R.M.φ ^ n) (R.M.σ u) = d ∨ (R.M.φ ^ n) (R.M.σ u) = u := by
    have hc : R.M.φ.SameCycle (R.M.σ u) d :=
      (show R.M.φ.SameCycle d (R.M.σ u) from ⟨1, by simp [CombMap.φ, hu]⟩).symm
    obtain ⟨n, hn⟩ := hc.exists_nat_pow_eq
    exact ⟨n, Or.inl hn⟩
  obtain ⟨n, hn, hmin⟩ : ∃ n, ((R.M.φ ^ n) (R.M.σ u) = d ∨ (R.M.φ ^ n) (R.M.σ u) = u) ∧
      ∀ i < n, (R.M.φ ^ i) (R.M.σ u) ≠ d ∧ (R.M.φ ^ i) (R.M.σ u) ≠ u :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => by
      have := Nat.find_min hex hi
      push_neg at this
      exact this⟩
  obtain _ | m := n
  · simp only [pow_zero, Perm.one_apply] at hn
    rcases hn with h | h
    · exact absurd h hne
    · exact absurd h hleaf
  have hwalk : ∀ i ≤ m, Relation.EqvGen N.Step (R.M.σ u) ((R.M.φ ^ i) (R.M.σ u)) := by
    intro i
    induction i with
    | zero => intro _; exact Relation.EqvGen.refl _
    | succ i ih =>
      intro hi
      have hc := hmin i (by omega)
      have hc' := hmin (i + 1) (by omega)
      rw [pow_succ', Perm.mul_apply] at hc' ⊢
      exact (ih (by omega)).trans _ _ _ (hfstep _ hc.1 hc.2 hc'.1 hc'.2)
  have hy := hwalk m le_rfl
  set y := (R.M.φ ^ m) (R.M.σ u) with hy_def
  have hφy : R.M.φ y = d ∨ R.M.φ y = u := by
    have : (R.M.φ ^ (m + 1)) (R.M.σ u) = R.M.φ y := by rw [pow_succ', Perm.mul_apply]
    rw [← this]; exact hn
  rcases hφy with hφy | hφy
  · -- `σ (α y) = d`, so `α y = σ⁻¹ d`, and `σ'(α y) = σ d`
    have hyr := hmin m (by omega)
    have ha1 : R.M.α y ≠ d := fun h => hyr.2 (by rw [← hy_def, hu, ← h, R.M.α_α])
    have ha2 : R.M.α y ≠ u := fun h => hyr.1 (by rw [← hy_def]; exact R.M.α.injective h)
    have e : erase2 R.M.σ d u (R.M.α y) = R.M.σ d :=
      erase2_apply_of_eq_left ha2 hφy (R.σd_ne_αd hd)
    exact hy.trans _ _ _ ((CombMap.withσ_eqvGen_α (σ' := erase2 R.M.σ d u) y).trans _ _ _
      (Relation.EqvGen.rel _ _ (Or.inl e.symm)))
  · exfalso
    apply hφ
    have h2 : R.M.φ.SameCycle (R.M.σ u) u := ⟨(m + 1 : ℕ), by
      rw [zpow_natCast, pow_succ', Perm.mul_apply]; exact hφy⟩
    exact (show R.M.φ.SameCycle d (R.M.σ u) from ⟨1, by simp [CombMap.φ, hu]⟩).trans h2

/-- **Both endpoints of degree `≥ 2`, different faces.** -/
theorem deleteId_diffFace (hleaf : R.M.σ (R.M.α d) ≠ R.M.α d)
    (hφ : ¬ R.M.φ.SameCycle d (R.M.α d)) :
    (R.M.eraseEdge R.M.σ d).Connected ∧ (R.M.eraseEdge R.M.σ d).euler = 2 ∧
    (R.M.eraseEdge R.M.σ d).numVertices = R.M.numVertices ∧
    (R.M.eraseEdge R.M.σ d).numEdges + 1 = R.M.numEdges ∧
    (R.M.eraseEdge R.M.σ d).numFaces + 1 = R.M.numFaces := by
  have hV := R.deleteId_numVertices hx hd h1
  have hF := R.deleteId_numFaces hx hd h1
  have hE := CombMap.eraseEdge_numEdges (M := R.M) R.M.σ d
  have hs := R.numOrbits_swap_φ_of_diffFace hφ
  rw [if_neg hleaf] at hV hF
  have hconn : (R.M.eraseEdge R.M.σ d).Connected := by
    refine R.deleteId_connected_of hx hd h1 ?_
    rw [R.deleteIdRetract_d (d := d), R.deleteIdRetract_u hd, R.deleteIdUImg_of_not_leaf hleaf]
    exact (R.deleteId_key_of_diffFace hx hd h1 hleaf hφ).symm _ _
  refine ⟨hconn, ?_, by omega, hE, by omega⟩
  have h := R.spherical
  unfold CombMap.euler at h ⊢
  omega

/-- Every retained dart is connected to `σ d` or to `σ u` after the deletion. -/
theorem deleteId_reach (hleaf : R.M.σ (R.M.α d) ≠ R.M.α d) (z : R.M.D) :
    Relation.EqvGen (R.M.withσ (erase2 R.M.σ d (R.M.α d))).Step (R.M.σ d)
        (R.deleteIdRetract d z) ∨
      Relation.EqvGen (R.M.withσ (erase2 R.M.σ d (R.M.α d))).Step (R.M.σ (R.M.α d))
        (R.deleteIdRetract d z) := by
  have mono : ∀ {a b : R.M.D}, Relation.EqvGen (R.M.withσ (erase2 R.M.σ d (R.M.α d))).Step a b →
      Relation.EqvGen (joinRel (R.M.withσ (erase2 R.M.σ d (R.M.α d))).Step (R.M.σ d)
        (R.M.σ (R.M.α d))) a b := by
    intro a b h
    induction h with
    | rel a b h => exact Relation.EqvGen.rel _ _ (Or.inl h)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂
  have hjoin : Relation.EqvGen (joinRel (R.M.withσ (erase2 R.M.σ d (R.M.α d))).Step (R.M.σ d)
      (R.M.σ (R.M.α d))) (R.deleteIdRetract d d) (R.deleteIdRetract d (R.M.α d)) := by
    rw [R.deleteIdRetract_d (d := d), R.deleteIdRetract_u hd, R.deleteIdUImg_of_not_leaf hleaf]
    exact Relation.EqvGen.rel _ _ (Or.inr ⟨rfl, rfl⟩)
  have key := CombMap.eqvGen_map (M := R.M)
    (r := joinRel (R.M.withσ (erase2 R.M.σ d (R.M.α d))).Step (R.M.σ d) (R.M.σ (R.M.α d)))
    (R.deleteIdRetract d) (fun y => mono (R.deleteId_stepσ hx hd h1 y)) (fun y => by
      by_cases hyd : y = d
      · subst hyd; exact hjoin
      by_cases hyu : y = R.M.α d
      · subst hyu; rw [R.M.α_α]; exact hjoin.symm _ _
      exact mono (R.deleteId_stepα hyd hyu)) (R.connected d z)
  rw [R.deleteIdRetract_d (d := d), eqvGen_joinRel_iff] at key
  rcases key with h | ⟨-, h | h⟩
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inr h

/-- **Both endpoints of degree `≥ 2`, same face.**  The map after deletion has `χ = 4`, is
disconnected, and consists of the component of the new base (connected, `χ = 2`) and its
complement (connected, `χ = 2`). -/
theorem deleteId_sameFace (hleaf : R.M.σ (R.M.α d) ≠ R.M.α d)
    (hφ : R.M.φ.SameCycle d (R.M.α d)) :
    (R.M.eraseEdge R.M.σ d).euler = 4 ∧ ¬ (R.M.eraseEdge R.M.σ d).Connected ∧
    (R.M.eraseEdge R.M.σ d).numVertices = R.M.numVertices ∧
    (R.M.eraseEdge R.M.σ d).numEdges + 1 = R.M.numEdges ∧
    (R.M.eraseEdge R.M.σ d).numFaces = R.M.numFaces + 1 ∧
    ((R.deleteIdPre hx hd h1).component.M).Connected ∧
    ((R.deleteIdPre hx hd h1).component.M).euler = 2 ∧
    ((R.M.eraseEdge R.M.σ d).componentCompl (R.deleteIdPre hx hd h1).base).Connected ∧
    ((R.M.eraseEdge R.M.σ d).componentCompl (R.deleteIdPre hx hd h1).base).euler = 2 := by
  have hV := R.deleteId_numVertices hx hd h1
  have hF := R.deleteId_numFaces hx hd h1
  have hE := CombMap.eraseEdge_numEdges (M := R.M) R.M.σ d
  have hs := R.numOrbits_swap_φ_of_sameFace hd hφ
  rw [if_neg hleaf] at hV hF
  have h4 : (R.M.eraseEdge R.M.σ d).euler = 4 := by
    have h := R.spherical
    unfold CombMap.euler at h ⊢
    omega
  have hσd := R.σd_ne_d hx hd h1
  let sd : (R.M.eraseEdge R.M.σ d).D := ⟨R.M.σ d, hσd, R.σd_ne_αd hd⟩
  let su : (R.M.eraseEdge R.M.σ d).D := ⟨R.M.σ (R.M.α d), R.σαd_ne_d hd, hleaf⟩
  have hreach : ∀ z : (R.M.eraseEdge R.M.σ d).D, Relation.EqvGen (R.M.eraseEdge R.M.σ d).Step sd z ∨ Relation.EqvGen (R.M.eraseEdge R.M.σ d).Step su z := by
    intro z
    rcases R.deleteId_reach hx hd h1 hleaf z.val with h | h <;>
      rw [R.deleteIdRetract_of_ne z.2.1 z.2.2] at h
    · exact Or.inl (CombMap.eraseEdge_eqvGen R.M.σ d h sd.2 z.2)
    · exact Or.inr (CombMap.eraseEdge_eqvGen R.M.σ d h su.2 z.2)
  have hnc : ¬ (R.M.eraseEdge R.M.σ d).Connected := fun h => by
    have := (R.M.eraseEdge R.M.σ d).euler_le_two h
    omega
  have hdis : ¬ Relation.EqvGen (R.M.eraseEdge R.M.σ d).Step sd su := fun h => hnc ((R.M.eraseEdge R.M.σ d).connected_of_base sd
    fun z => (hreach z).elim id fun h' => h.trans _ _ _ h')
  have hbsd : Relation.EqvGen (R.M.eraseEdge R.M.σ d).Step (R.deleteIdPre hx hd h1).base sd := by
    refine (R.M.eraseEdge R.M.σ d).eqvGen_of_sameCycle ((CombMap.eraseEdge_sameCycle_iff R.M.σ d).2 ?_)
    exact (R.marked_deleteIdBase hd).symm.trans (R.marked_σd hd)
  have hc1 := (R.M.eraseEdge R.M.σ d).component_connected (R.deleteIdPre hx hd h1).base
  have hc2 : ((R.M.eraseEdge R.M.σ d).componentCompl (R.deleteIdPre hx hd h1).base).Connected := by
    refine (R.M.eraseEdge R.M.σ d).componentCompl_connected (R.deleteIdPre hx hd h1).base su (fun h => hdis (((hbsd.symm _ _).trans _ _ _ h)))
      fun z hz => (hreach z).resolve_left fun h => hz (hbsd.trans _ _ _ h)
  have hadd := (R.M.eraseEdge R.M.σ d).euler_component_add (R.deleteIdPre hx hd h1).base
  have hle1 := ((R.M.eraseEdge R.M.σ d).component (R.deleteIdPre hx hd h1).base).euler_le_two hc1
  have hle2 := ((R.M.eraseEdge R.M.σ d).componentCompl (R.deleteIdPre hx hd h1).base).euler_le_two hc2
  refine ⟨h4, hnc, by omega, hE, by omega, hc1, ?_, hc2, ?_⟩
  · change ((R.M.eraseEdge R.M.σ d).component (R.deleteIdPre hx hd h1).base).euler = 2
    omega
  · omega

/-- The raw picture obtained from an identity-labelled marked edge, in each case (connected
result in the leaf and different-face cases, the component of the new base in the same-face
case). -/
noncomputable def deleteIdentity : C.RawPicture x :=
  if hleaf : R.M.σ (R.M.α d) = R.M.α d then
    (R.deleteIdPre hx hd h1).toRaw (R.deleteId_leaf hx hd h1 hleaf).1
      (R.deleteId_leaf hx hd h1 hleaf).2.1
  else if hφ : R.M.φ.SameCycle d (R.M.α d) then
    (R.deleteIdPre hx hd h1).component.toRaw (R.deleteId_sameFace hx hd h1 hleaf hφ).2.2.2.2.2.1
      (R.deleteId_sameFace hx hd h1 hleaf hφ).2.2.2.2.2.2.1
  else
    (R.deleteIdPre hx hd h1).toRaw (R.deleteId_diffFace hx hd h1 hleaf hφ).1
      (R.deleteId_diffFace hx hd h1 hleaf hφ).2.1

/-- **Removing an identity-labelled marked edge gives strictly fewer edges.** -/
theorem deleteIdentity_numEdges_lt : (R.deleteIdentity hx hd h1).M.numEdges < R.M.numEdges := by
  have hE := CombMap.eraseEdge_numEdges (M := R.M) R.M.σ d
  unfold deleteIdentity
  split_ifs with hleaf hφ
  · change (R.M.eraseEdge R.M.σ d).numEdges < _; omega
  · change ((R.M.eraseEdge R.M.σ d).component (R.deleteIdPre hx hd h1).base).numEdges < _
    have := (R.M.eraseEdge R.M.σ d).numEdges_component_add (R.deleteIdPre hx hd h1).base
    omega
  · change (R.M.eraseEdge R.M.σ d).numEdges < _; omega

/-- The base of the result is `deleteIdBase` (`σ d` if `d` was the base), and every label is
the old label. -/
theorem deleteIdentity_base_lab :
    ∃ e : (R.deleteIdentity hx hd h1).M.D → R.M.D,
      e (R.deleteIdentity hx hd h1).base = R.deleteIdBase d ∧
      ∀ z, (R.deleteIdentity hx hd h1).lab z = R.lab (e z) := by
  have key : ∀ R' : C.RawPicture x, ((∃ h h', R' = (R.deleteIdPre hx hd h1).toRaw h h') ∨
      ∃ h h', R' = (R.deleteIdPre hx hd h1).component.toRaw h h') →
      ∃ e : R'.M.D → R.M.D, e R'.base = R.deleteIdBase d ∧ ∀ z, R'.lab z = R.lab (e z) := by
    rintro R' (⟨h, h', rfl⟩ | ⟨h, h', rfl⟩)
    · exact ⟨Subtype.val, rfl, fun _ => rfl⟩
    · exact ⟨fun z => z.val.val, rfl, fun _ => rfl⟩
  apply key
  unfold deleteIdentity
  split_ifs with hleaf hφ
  · exact Or.inl ⟨(R.deleteId_leaf hx hd h1 hleaf).1, (R.deleteId_leaf hx hd h1 hleaf).2.1, rfl⟩
  · exact Or.inr ⟨(R.deleteId_sameFace hx hd h1 hleaf hφ).2.2.2.2.2.1,
      (R.deleteId_sameFace hx hd h1 hleaf hφ).2.2.2.2.2.2.1, rfl⟩
  · exact Or.inl ⟨(R.deleteId_diffFace hx hd h1 hleaf hφ).1,
      (R.deleteId_diffFace hx hd h1 hleaf hφ).2.1, rfl⟩

end IdentityEdge

/-- **Identity marked letters can be removed.**  If `x ≠ 1` and some dart at the marked vertex
carries the identity letter, then `x` has a raw picture with strictly fewer edges. -/
theorem exists_fewer_edges_of_identity (hx : x ≠ 1) {d : R.M.D}
    (hd : R.M.σ.SameCycle R.base d) (h1 : (R.lab d).2 = 1) :
    ∃ R' : C.RawPicture x, R'.M.numEdges < R.M.numEdges :=
  ⟨R.deleteIdentity hx hd h1, R.deleteIdentity_numEdges_lt hx hd h1⟩

end RawPicture

end ConeComplex

end TheoremA
