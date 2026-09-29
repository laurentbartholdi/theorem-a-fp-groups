module

public import RequestProject.TheoremA.Lemma31.Picture.DefectSplit

/-!
# Degrees, faces and labels of a least defect (Sections 2–4)

Let `M, lab` be a least defect of a non-positively curved cone complex of groups.

* **Section 2** (`IsLeastDefect.σ_ne`): every vertex has degree at least two.  A leaf `d` would
  give `φ (α d) = d`, `φ d = σ (α d)`, so `u = α d` and `σ u` share a vertex and a face; by
  Section 1 `σ u = u`, and connectedness forces the whole map to be the single edge `{d, u}`.
  One endpoint is ordinary, so its (single) label is `1`; by injectivity of the structure maps the
  other label is `1` too, contradicting the nonidentity exceptional product.
* **Section 3** (`IsLeastDefect.not_sameFace_α`): the two sides of every edge lie in different
  faces (otherwise `d` and `σ d = φ (α d)` share a vertex and a face).
* **Section 4** (`IsLeastDefect.letterWord_ne_one`): no dart carries an identity label.  An
  identity label forces the identity label at the other end of the edge (injectivity); deleting the
  edge (both endpoints of degree `≥ 2`, different faces: `CombMap.eraseEdge_diffFace`) leaves a
  connected spherical map with the same vertex products, hence defect data with one edge fewer.

`DefectData.of_eraseEdge` is the general criterion for defect data after erasing an edge with
modified labels; it is reused for the consolidation moves.
-/

@[expose] public section

namespace TheoremA

universe u w

open Picture Equiv Function

namespace ConeComplex

variable {V T : Type w} {C : ConeComplex.{u, w} V T}

/-- The label of a dart is trivial iff its image in the free product is trivial. -/
theorem letterWord_eq_one_iff (p : C.Letter) : C.letterWord p = 1 ↔ p.2 = 1 := by
  constructor
  · intro h
    exact Monoid.CoprodI.of_injective p.1 (h.trans (map_one _).symm)
  · intro h
    change Monoid.CoprodI.of p.2 = 1
    rw [h, map_one]

/-- Along a relator edge, one label is trivial iff the other one is (injectivity of the structure
maps). -/
theorem NPC.letterWord_eq_one_iff_of_relEdge (hC : C.NPC) {p q : C.Letter} (h : C.RelEdge p q) :
    C.letterWord p = 1 ↔ C.letterWord q = 1 := by
  obtain ⟨v, t, hvt, a, rfl, rfl⟩ := h
  rw [letterWord_eq_one_iff, letterWord_eq_one_iff]
  change a = 1 ↔ (C.φ v t hvt a)⁻¹ = 1
  rw [inv_eq_one]
  exact ⟨fun h => by rw [h, map_one], fun h => hC.φ_injective v t hvt (h.trans (map_one _).symm)⟩

theorem DefectData.letterWord_α_eq_one_iff (hC : C.NPC) {M : CombMap} {lab : M.D → C.Letter}
    (h : C.DefectData M lab) (x : M.D) :
    C.letterWord (lab (M.α x)) = 1 ↔ C.letterWord (lab x) = 1 := by
  rcases h.edge x with he | he
  · exact (hC.letterWord_eq_one_iff_of_relEdge he).symm
  · exact hC.letterWord_eq_one_iff_of_relEdge he

theorem eraseEdge_cycleWord_comp {G : Type*} [Monoid G] {M : CombMap} (π : Perm M.D) (a : M.D)
    (g : C.Letter → G) (lab : M.D → C.Letter) (x : (M.eraseEdge π a).D) :
    cycleWord (M.eraseEdge π a).σ (g ∘ lab ∘ Subtype.val) x =
      cycleWord (erase2 π a (M.α a)) (g ∘ lab) x.val :=
  CombMap.eraseEdge_cycleWord π a (g ∘ lab) x

/-- **Defect data after erasing an edge**, with new labels `lab'` on the retained darts. -/
theorem DefectData.of_eraseEdge {M : CombMap} (π : Perm M.D) (a : M.D) (lab' : M.D → C.Letter)
    (hc : (M.eraseEdge π a).Connected) (hs : (M.eraseEdge π a).euler = 2)
    (htype : ∀ z w, z ≠ a → z ≠ M.α a → w ≠ a → w ≠ M.α a → π.SameCycle z w →
      (lab' w).1 = (lab' z).1)
    (hedge : ∀ z, z ≠ a → z ≠ M.α a →
      C.RelEdge (lab' z) (lab' (M.α z)) ∨ C.RelEdge (lab' (M.α z)) (lab' z))
    (x : M.D) (hxa : x ≠ a) (hxb : x ≠ M.α a)
    (hwx : cycleWord (erase2 π a (M.α a)) (C.letterWord ∘ lab') x ≠ 1)
    (hrest : ∀ y, y ≠ a → y ≠ M.α a →
      cycleWord (erase2 π a (M.α a)) (C.letterWord ∘ lab') y ≠ 1 → π.SameCycle x y) :
    C.DefectData (M.eraseEdge π a) (lab' ∘ Subtype.val) := by
  refine ⟨hc, hs, fun z => ?_, fun z => hedge z.val z.2.1 z.2.2, ⟨⟨x, hxa, hxb⟩, ?_, ?_⟩⟩
  · have hz' := ((M.eraseEdge π a).σ z).2
    refine htype z.val _ z.2.1 z.2.2 hz'.1 hz'.2 ?_
    exact (sameCycle_erase2_iff z.2.1 z.2.2 hz'.1 hz'.2).1 ⟨1, by
      rw [zpow_one]; exact (CombMap.eraseEdge_σ_val π a z).symm⟩
  · rw [eraseEdge_cycleWord_comp]
    exact hwx
  · intro y hy
    rw [eraseEdge_cycleWord_comp] at hy
    rw [CombMap.eraseEdge_sameCycle_iff]
    exact hrest y.val y.2.1 y.2.2 hy

namespace IsLeastDefect

variable {M : CombMap} {lab : M.D → C.Letter} (h : C.IsLeastDefect M lab) (hC : C.NPC)

include h hC

/-- **Section 2: every vertex has degree at least two.** -/
theorem σ_ne (d : M.D) : M.σ d ≠ d := by
  classical
  intro hfix
  set u := M.α d with hu
  have hφu : M.φ u = d := by
    change M.σ (M.α u) = d
    rw [hu, M.α_α, hfix]
  have hφd : M.φ d = M.σ u := rfl
  have hface : M.φ.SameCycle u (M.σ u) := ⟨2, by
    rw [zpow_ofNat, pow_two, Perm.mul_apply, hφu, hφd]⟩
  have hσu : M.σ u = u := (h.sameVertex_sameFace_eq ⟨1, by simp⟩ hface).symm
  -- the whole map is the edge `{d, u}`
  have hdu : d ≠ u := CombMap.ne_α_of_loop (h.1.not_sameCycle_α d)
  have hinv : ∀ x, Relation.EqvGen M.Step d x → x = d ∨ x = u := by
    intro x hx
    have key := CombMap.invariant_of_eqvGen (M := M) (fun y => y = d ∨ y = u)
      (fun y => by
        constructor
        · rintro (hy | hy)
          · exact Or.inl (M.σ.injective (hy.trans hfix.symm))
          · exact Or.inr (M.σ.injective (hy.trans hσu.symm))
        · rintro (rfl | rfl)
          · exact Or.inl hfix
          · exact Or.inr hσu)
      (fun y => by
        constructor
        · rintro (hy | hy)
          · right; rw [hu, ← hy, M.α_α]
          · left; exact M.α.injective (hy.trans hu)
        · rintro (rfl | rfl)
          · exact Or.inr rfl
          · exact Or.inl (M.α_α _))
      hx
    exact key.1 (Or.inl rfl)
  obtain ⟨b0, hb0, hexc⟩ := h.1.exc
  have hwd : cycleWord M.σ (C.letterWord ∘ lab) d = C.letterWord (lab d) :=
    cycleWord_of_fixed _ hfix
  have hwu : cycleWord M.σ (C.letterWord ∘ lab) u = C.letterWord (lab u) :=
    cycleWord_of_fixed _ hσu
  have hαd := h.1.letterWord_α_eq_one_iff hC d
  have hnd := h.1.not_sameCycle_α d
  rcases hinv b0 (h.1.connected d b0) with rfl | rfl
  · apply hb0
    rw [hwd, ← hαd, ← hwu]
    by_contra hne
    exact hnd (hexc u hne)
  · apply hb0
    rw [hwu, hαd, ← hwd]
    by_contra hne
    exact hnd ((hexc d hne).symm)

/-- **Section 3: the two sides of every edge lie in different faces.** -/
theorem not_sameFace_α (d : M.D) : ¬ M.φ.SameCycle d (M.α d) := by
  intro hφ
  have h1 : M.φ (M.α d) = M.σ d := by
    change M.σ (M.α (M.α d)) = M.σ d
    rw [M.α_α]
  have hface : M.φ.SameCycle d (M.σ d) := hφ.trans ⟨1, by rw [zpow_one, h1]⟩
  exact h.σ_ne hC d (h.sameVertex_sameFace_eq ⟨1, by simp⟩ hface).symm

/-- **Section 4: no dart carries an identity label.** -/
theorem letterWord_ne_one (d : M.D) : C.letterWord (lab d) ≠ 1 := by
  classical
  intro h1
  have h1' : C.letterWord (lab (M.α d)) = 1 := (h.1.letterWord_α_eq_one_iff hC d).2 h1
  have hloop := h.1.not_sameCycle_α d
  obtain ⟨hconn, hχ, hE⟩ := CombMap.eraseEdge_diffFace hloop (h.σ_ne hC d) (h.σ_ne hC (M.α d))
    h.1.connected (h.not_sameFace_α hC d)
  obtain ⟨b0, hb0, hexc⟩ := h.1.exc
  -- a retained dart at the exceptional vertex
  obtain ⟨b1, hb1d, hb1u, hb01⟩ : ∃ b1, b1 ≠ d ∧ b1 ≠ M.α d ∧ M.σ.SameCycle b0 b1 := by
    by_cases hbd : b0 = d
    · rw [hbd]
      exact ⟨M.σ d, h.σ_ne hC d, CombMap.σ_ne_α_of_loop hloop, ⟨1, by simp⟩⟩
    by_cases hbu : b0 = M.α d
    · refine ⟨M.σ b0, ?_, ?_, ⟨1, by simp⟩⟩
      · rw [hbu]; exact CombMap.σα_ne_of_loop hloop
      · rw [hbu]; exact h.σ_ne hC _
    · exact ⟨b0, hbd, hbu, Perm.SameCycle.refl _ _⟩
  have hword : ∀ y, y ≠ d → y ≠ M.α d →
      cycleWord (erase2 M.σ d (M.α d)) (C.letterWord ∘ lab) y =
        cycleWord M.σ (C.letterWord ∘ lab) y :=
    fun y hy1 hy2 => cycleWord_erase2 _ hy1 hy2 h1 h1'
  have hdata : C.DefectData (M.eraseEdge M.σ d) (lab ∘ Subtype.val) := by
    refine DefectData.of_eraseEdge M.σ d lab hconn (by rw [hχ, h.1.spherical])
      (fun z w _ _ _ _ hzw => h.1.type_eq_of_sameCycle hzw) (fun z _ _ => h.1.edge z)
      b1 hb1d hb1u ?_ ?_
    · rw [hword b1 hb1d hb1u]
      intro hw
      exact hb0 (cycleWord_eq_one_of_sameCycle _ hb01.symm hw)
    · intro y hy1 hy2 hy
      rw [hword y hy1 hy2] at hy
      exact hb01.symm.trans (hexc y hy)
  exact h.not_lt hdata (by omega)

end IsLeastDefect

end ConeComplex

end TheoremA
