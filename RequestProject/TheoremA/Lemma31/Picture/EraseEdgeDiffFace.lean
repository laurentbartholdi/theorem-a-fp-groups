module

public import RequestProject.TheoremA.Lemma31.Picture.EraseEdge

/-!
# Deleting an edge between two different faces (map level)

Let `M` be a connected spherical map and `{d, u = α d}` an edge whose endpoints are different
vertices, both of degree at least two, and whose two sides lie in different faces.  Deleting the
edge (`CombMap.eraseEdge M.σ d`) gives a connected spherical map with the same vertices, one edge
fewer and one face fewer (`CombMap.eraseEdge_diffFace`).

This is the map-level content of the "different faces" case of `IdentityEdge.lean`, stated for an
arbitrary map (no labels, no marked vertex).
-/

@[expose] public section

namespace TheoremA.Picture.CombMap

open Equiv Function

variable {M : CombMap} {d : M.D} (hloop : ¬ M.σ.SameCycle d (M.α d)) (hσd : M.σ d ≠ d)
  (hleaf : M.σ (M.α d) ≠ M.α d)

include hloop in
theorem ne_α_of_loop : d ≠ M.α d := fun h => hloop (h ▸ Perm.SameCycle.refl _ _)

include hloop in
theorem σ_ne_α_of_loop : M.σ d ≠ M.α d := fun h => hloop ⟨1, by simpa using h⟩

include hloop in
theorem σα_ne_of_loop : M.σ (M.α d) ≠ d := fun h =>
  hloop (Perm.SameCycle.symm ⟨1, by simpa using h⟩)

/-- The retraction used to transport paths. -/
def delRetract (M : CombMap) (d : M.D) (z : M.D) : M.D :=
  if z = d then M.σ d else if z = M.α d then M.σ (M.α d) else z

theorem delRetract_d : M.delRetract d d = M.σ d := by simp [delRetract]

include hloop in
theorem delRetract_u : M.delRetract d (M.α d) = M.σ (M.α d) := by
  unfold delRetract
  rw [if_neg (ne_α_of_loop hloop).symm, if_pos rfl]

theorem delRetract_of_ne {z : M.D} (h1 : z ≠ d) (h2 : z ≠ M.α d) : M.delRetract d z = z := by
  unfold delRetract
  rw [if_neg h1, if_neg h2]

include hloop hσd hleaf in
theorem del_stepσ (y : M.D) :
    Relation.EqvGen (M.withσ (erase2 M.σ d (M.α d))).Step
      (M.delRetract d y) (M.delRetract d (M.σ y)) := by
  have hσdu := σ_ne_α_of_loop hloop
  have hne := σα_ne_of_loop hloop
  have hSC : ∀ y z, (y ≠ d ∧ y ≠ M.α d) → (z ≠ d ∧ z ≠ M.α d) → M.σ.SameCycle y z →
      Relation.EqvGen (M.withσ (erase2 M.σ d (M.α d))).Step y z := fun y z hy hz h =>
    withσ_eqvGen_of_sameCycle ((sameCycle_erase2_iff hy.1 hy.2 hz.1 hz.2).2 h)
  have hσ1 : ∀ y, M.σ.SameCycle y (M.σ y) := fun y => ⟨1, by simp⟩
  by_cases hyd : y = d
  · subst hyd
    rw [delRetract_d, delRetract_of_ne hσd hσdu]
    exact Relation.EqvGen.refl _
  by_cases hyu : y = M.α d
  · subst hyu
    rw [delRetract_u hloop, delRetract_of_ne hne hleaf]
    exact Relation.EqvGen.refl _
  rw [delRetract_of_ne hyd hyu]
  by_cases h2 : M.σ y = d
  · rw [h2, delRetract_d]
    exact hSC _ _ ⟨hyd, hyu⟩ ⟨hσd, hσdu⟩ (by rw [← h2]; exact (hσ1 y).trans (hσ1 _))
  by_cases h3 : M.σ y = M.α d
  · rw [h3, delRetract_u hloop]
    exact hSC _ _ ⟨hyd, hyu⟩ ⟨hne, hleaf⟩ (by rw [← h3]; exact (hσ1 y).trans (hσ1 _))
  rw [delRetract_of_ne h2 h3]
  exact hSC _ _ ⟨hyd, hyu⟩ ⟨h2, h3⟩ (hσ1 y)

theorem del_stepα {y : M.D} (hyd : y ≠ d) (hyu : y ≠ M.α d) :
    Relation.EqvGen (M.withσ (erase2 M.σ d (M.α d))).Step
      (M.delRetract d y) (M.delRetract d (M.α y)) := by
  have h1' : M.α y ≠ d := fun h => hyu (by rw [← h, M.α_α])
  have h2' : M.α y ≠ M.α d := fun h => hyd (M.α.injective h)
  rw [delRetract_of_ne hyd hyu, delRetract_of_ne h1' h2']
  exact withσ_eqvGen_α y

include hloop hleaf in
/-- The face walk: if `d`, `u` lie in different faces, `σ u` and `σ d` are still connected after
deleting the edge. -/
theorem del_key (hφ : ¬ M.φ.SameCycle d (M.α d)) :
    Relation.EqvGen (M.withσ (erase2 M.σ d (M.α d))).Step (M.σ (M.α d)) (M.σ d) := by
  classical
  set u := M.α d with hu
  set N := M.withσ (erase2 M.σ d u) with hN
  have hne : M.σ u ≠ d := σα_ne_of_loop hloop
  have hfstep : ∀ y, y ≠ d → y ≠ u → M.φ y ≠ d → M.φ y ≠ u →
      Relation.EqvGen N.Step y (M.φ y) := by
    intro y hy1 hy2 hy3 hy4
    have ha1 : M.α y ≠ d := fun h => hy2 (by rw [hu, ← h, M.α_α])
    have ha2 : M.α y ≠ u := fun h => hy1 (M.α.injective h)
    have e : erase2 M.σ d u (M.α y) = M.φ y := erase2_apply_of_notMem ha1 ha2 hy3 hy4
    exact (withσ_eqvGen_α (σ' := erase2 M.σ d u) y).trans _ _ _
      (Relation.EqvGen.rel _ _ (Or.inl e.symm))
  have hex : ∃ n : ℕ, (M.φ ^ n) (M.σ u) = d ∨ (M.φ ^ n) (M.σ u) = u := by
    have hc : M.φ.SameCycle (M.σ u) d :=
      (show M.φ.SameCycle d (M.σ u) from ⟨1, by simp [φ, hu]⟩).symm
    obtain ⟨n, hn⟩ := hc.exists_nat_pow_eq
    exact ⟨n, Or.inl hn⟩
  obtain ⟨n, hn, hmin⟩ : ∃ n, ((M.φ ^ n) (M.σ u) = d ∨ (M.φ ^ n) (M.σ u) = u) ∧
      ∀ i < n, (M.φ ^ i) (M.σ u) ≠ d ∧ (M.φ ^ i) (M.σ u) ≠ u :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => by
      have := Nat.find_min hex hi
      push_neg at this
      exact this⟩
  obtain _ | m := n
  · simp only [pow_zero, Perm.one_apply] at hn
    rcases hn with h | h
    · exact absurd h hne
    · exact absurd h hleaf
  have hwalk : ∀ i ≤ m, Relation.EqvGen N.Step (M.σ u) ((M.φ ^ i) (M.σ u)) := by
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
  set y := (M.φ ^ m) (M.σ u) with hy_def
  have hφy : M.φ y = d ∨ M.φ y = u := by
    have : (M.φ ^ (m + 1)) (M.σ u) = M.φ y := by rw [pow_succ', Perm.mul_apply]
    rw [← this]; exact hn
  rcases hφy with hφy | hφy
  · have hyr := hmin m (by omega)
    have ha1 : M.α y ≠ d := fun h => hyr.2 (by rw [← hy_def, hu, ← h, M.α_α])
    have ha2 : M.α y ≠ u := fun h => hyr.1 (by rw [← hy_def]; exact M.α.injective h)
    have e : erase2 M.σ d u (M.α y) = M.σ d :=
      erase2_apply_of_eq_left ha2 hφy (σ_ne_α_of_loop hloop)
    exact hy.trans _ _ _ ((withσ_eqvGen_α (σ' := erase2 M.σ d u) y).trans _ _ _
      (Relation.EqvGen.rel _ _ (Or.inl e.symm)))
  · exfalso
    apply hφ
    have h2 : M.φ.SameCycle (M.σ u) u := ⟨(m + 1 : ℕ), by
      rw [zpow_natCast, pow_succ', Perm.mul_apply]; exact hφy⟩
    exact (show M.φ.SameCycle d (M.σ u) from ⟨1, by simp [φ, hu]⟩).trans h2

include hloop hσd hleaf in
/-- **Deleting an edge between different faces.**  Both endpoints of degree `≥ 2`, endpoints at
different vertices, sides in different faces: the result is connected, has the same number of
vertices, one edge fewer and one face fewer; in particular `χ` is unchanged. -/
theorem eraseEdge_diffFace (hc : M.Connected) (hφ : ¬ M.φ.SameCycle d (M.α d)) :
    (M.eraseEdge M.σ d).Connected ∧ (M.eraseEdge M.σ d).euler = M.euler ∧
    (M.eraseEdge M.σ d).numEdges + 1 = M.numEdges := by
  have hdu := ne_α_of_loop hloop
  have hσdu := σ_ne_α_of_loop hloop
  have hne := σα_ne_of_loop hloop
  -- vertices
  have hA := eraseEdge_numVertices M.σ d
  have hB := numOrbits_erase2 M.σ d (M.α d)
  have h5 : erasePt M.σ d (M.α d) = M.σ (M.α d) := erasePt_apply_of_ne hdu.symm hne
  rw [if_neg hσd, h5, if_neg hleaf] at hB
  -- faces
  have hA' := eraseEdge_numFaces M.σ d
  have hB' := numOrbits_erase2 (Equiv.swap d (M.α d) * M.σ * M.α) d (M.α d)
  have hχ : Equiv.swap d (M.α d) * M.σ * M.α = swap d (M.α d) * M.φ := by
    rw [mul_assoc]; rfl
  have hχu : (Equiv.swap d (M.α d) * M.σ * M.α) (M.α d) = M.σ d := by
    change swap d (M.α d) (M.σ (M.α (M.α d))) = _
    rw [M.α_α]
    exact swap_apply_of_ne_of_ne hσd hσdu
  have h5' : erasePt (Equiv.swap d (M.α d) * M.σ * M.α) d (M.α d) ≠ M.α d := by
    rw [erasePt_apply_of_ne hdu.symm (by rw [hχu]; exact hσd), hχu]
    exact hσdu
  have hχd : (Equiv.swap d (M.α d) * M.σ * M.α) d = swap d (M.α d) (M.σ (M.α d)) := rfl
  rw [if_neg h5', hχd, swap_apply_of_ne_of_ne hne hleaf, if_neg hne, hχ] at hB'
  rw [hχ] at hA'
  have hs : numOrbits (swap d (M.α d) * M.φ) + 1 = M.numFaces := (numOrbits_swap_mul hφ).symm
  have hE := eraseEdge_numEdges (M := M) M.σ d
  have hconn : (M.eraseEdge M.σ d).Connected := by
    refine eraseEdge_connected_of M.σ d hc (M.delRetract d)
      (fun y hy1 hy2 => delRetract_of_ne hy1 hy2) (del_stepσ hloop hσd hleaf) fun y => ?_
    have hkey : Relation.EqvGen (M.withσ (erase2 M.σ d (M.α d))).Step
        (M.delRetract d d) (M.delRetract d (M.α d)) := by
      rw [delRetract_d, delRetract_u hloop]
      exact (del_key hloop hleaf hφ).symm _ _
    by_cases hyd : y = d
    · subst hyd; exact hkey
    by_cases hyu : y = M.α d
    · subst hyu; rw [M.α_α]; exact hkey.symm _ _
    exact del_stepα hyd hyu
  refine ⟨hconn, ?_, hE⟩
  unfold euler numVertices numFaces at *
  omega

end TheoremA.Picture.CombMap
