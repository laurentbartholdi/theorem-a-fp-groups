module

public import RequestProject.TheoremA.Lemma31.Picture.CombMap
public import RequestProject.TheoremA.Lemma31.ConeComplex

/-!
# Raw pictures from null words

This file is the first step of the picture route to the injectivity statement behind Lemma 3.1.
It uses **neither `NPC` nor the girth of the incidence graph**.

## Raw pictures

A *letter* is an element of one of the local groups, `⟨k, g⟩` with `k : V ⊕ T` and
`g : C.loc k`.  A **raw picture** `C.RawPicture x` for an element `x` of the free product
`∗ₖ C.loc k` consists of

* a connected combinatorial map `M` (dart representation, `CombMap`) with `χ(M) = 2`;
* a letter `lab d` on every dart `d`;
* a base dart `base`; the vertex of `base` is the **marked vertex**, all other vertices are
  *interior*;

subject to the following conditions (`[g]` denotes the image of a letter in the free product):

* (type) all darts of an interior vertex carry letters of the same local group;
* (local) at every interior vertex, the product of the letters read once around the vertex (from
  any of its darts) is `1`;
* (interior edges) an edge between interior vertices is a *relator edge*: one end carries
  `⟨v, a⟩` with `a : A v`, the other end carries `⟨t, (φ v t h a)⁻¹⟩` for an incidence `h`;
* (boundary edges) an edge at the marked vertex has its other end at an interior vertex, and the
  two ends carry mutually inverse letters `⟨k, g⟩`, `⟨k, g⁻¹⟩`;
* (marked word) the product of the letters read once around the marked vertex, starting at
  `base`, is `x`.

The marked vertex is the boundary of a van Kampen-type disc collapsed to a point: it is the
marked spherical picture directly (`χ = 2`, not the disc value `χ = 1`); see
`RawPicture.euler_disc` for the explicit bookkeeping.  There are **no** degree bounds, no face
bounds, and no reducedness conditions.

## Main results

* `ConeComplex.relatorPicture` : a raw picture for each defining relator `a · (φ a)⁻¹`;
* `ConeComplex.letterPairPicture` : a raw picture for `g⁻¹ g` (one interior vertex);
* `ConeComplex.RawPicture.glue` : raw pictures for `x` and `y` give one for `x * y` (merging the
  marked vertices; `χ = 2 + 2 - 2`);
* `ConeComplex.RawPicture.rotate` : moving the base dart conjugates the marked word;
* `ConeComplex.realizable_of_mem_normalClosure` : **every element of the normal closure of the
  relators has a raw picture**;
* `ConeComplex.exists_rawPicture_of_ι_eq_one` : if `ι_v a = 1` in the colimit, there is a raw
  picture whose marked word is `a` (as an element of the free product); it is nonidentity iff
  `a ≠ 1` (`ConeComplex.letter_ne_one`).
-/

@[expose] public section

namespace TheoremA

universe u w

namespace ConeComplex

open Picture Equiv Function

variable {V T : Type w} (C : ConeComplex.{u, w} V T)

/-- A letter: an element of one of the local groups. -/
abbrev Letter : Type _ := Σ k : V ⊕ T, C.loc k

variable {C} in
/-- The inverse letter. -/
def Letter.inv (p : C.Letter) : C.Letter := ⟨p.1, p.2⁻¹⟩

variable {C} in
@[simp] theorem Letter.inv_inv (p : C.Letter) : p.inv.inv = p := by
  simp [Letter.inv]

/-- The image of a letter in the free product of the local groups. -/
def letterWord (p : C.Letter) : Monoid.CoprodI C.loc := Monoid.CoprodI.of p.2

theorem letterWord_inv (p : C.Letter) : C.letterWord p.inv = (C.letterWord p)⁻¹ :=
  map_inv _ _

/-- The labels at the two ends of a relator edge: `⟨v, a⟩` at the index end and
`⟨t, (φ v t h a)⁻¹⟩` at the triple end. -/
def RelEdge (p q : C.Letter) : Prop :=
  ∃ (v : V) (t : T) (h : C.inc v t) (a : C.A v),
    p = ⟨Sum.inl v, a⟩ ∧ q = ⟨Sum.inr t, (C.φ v t h a)⁻¹⟩

/-- A **raw picture** for an element `x` of the free product of the local groups: a connected
spherical labelled combinatorial map with a marked vertex whose word is `x`, satisfying the local
group-product equations at all other vertices (see the module docstring). -/
structure RawPicture (x : Monoid.CoprodI C.loc) where
  /-- The underlying combinatorial map. -/
  M : CombMap
  /-- The letters on the darts. -/
  lab : M.D → C.Letter
  /-- The base dart; its vertex is the marked vertex. -/
  base : M.D
  connected : M.Connected
  spherical : M.euler = 2
  /-- (type) Interior vertices are labelled by a single local group. -/
  type_σ : ∀ d, ¬ M.σ.SameCycle base d → (lab (M.σ d)).1 = (lab d).1
  /-- (local) The local group-product equation at interior vertices. -/
  local_eq : ∀ d, ¬ M.σ.SameCycle base d → cycleWord M.σ (C.letterWord ∘ lab) d = 1
  /-- (interior edges) Edges between interior vertices are relator edges. -/
  edge_interior : ∀ d, ¬ M.σ.SameCycle base d → ¬ M.σ.SameCycle base (M.α d) →
    C.RelEdge (lab d) (lab (M.α d)) ∨ C.RelEdge (lab (M.α d)) (lab d)
  /-- (boundary edges) Edges at the marked vertex go to interior vertices, with inverse
  letters. -/
  edge_boundary : ∀ d, M.σ.SameCycle base d →
    ¬ M.σ.SameCycle base (M.α d) ∧ lab (M.α d) = (lab d).inv
  /-- (marked word) The word around the marked vertex, read from `base`. -/
  boundary_word : cycleWord M.σ (C.letterWord ∘ lab) base = x

/-- `x` has a raw picture. -/
def Realizable (x : Monoid.CoprodI C.loc) : Prop := Nonempty (C.RawPicture x)

variable {C}

theorem Realizable.of_eq {x y : Monoid.CoprodI C.loc} (hx : C.Realizable x) (h : x = y) :
    C.Realizable y := h ▸ hx

/-- **Disc versus sphere (bookkeeping).**  A raw picture is a disc picture whose boundary circle
has been collapsed to the marked vertex.  Collapsing a boundary circle with `n` vertices and `n`
edges to one point changes `V - E + F` by exactly `+1`, so the disc count (the sphere count with
the marked vertex removed) is `1` exactly when the spherical count is `2`.  This lemma records that
the raw pictures constructed here satisfy the disc value `1` in this sense. -/
theorem RawPicture.euler_disc {x : Monoid.CoprodI C.loc} (P : C.RawPicture x) :
    ((P.M.numVertices : ℤ) - 1) - P.M.numEdges + P.M.numFaces = 1 := by
  have := P.spherical
  unfold CombMap.euler at this
  omega

/-! ### Gluing two raw pictures at their marked vertices -/

section Glue

variable {x y : Monoid.CoprodI C.loc} (P : C.RawPicture x) (Q : C.RawPicture y)

theorem glue_marked_inl {d : P.M.D} :
    (CombMap.glue P.M Q.M P.base Q.base).σ.SameCycle (Sum.inl P.base) (Sum.inl d) ↔
      P.M.σ.SameCycle P.base d := by
  rw [CombMap.glue_sameCycle_iff]
  simp [sameCycle_sumCongr_inl, not_sameCycle_sumCongr_inr_inl, Perm.SameCycle.refl]

theorem glue_marked_inr {d : Q.M.D} :
    (CombMap.glue P.M Q.M P.base Q.base).σ.SameCycle (Sum.inl P.base) (Sum.inr d) ↔
      Q.M.σ.SameCycle Q.base d := by
  rw [CombMap.glue_sameCycle_iff]
  simp [sameCycle_sumCongr_inr, not_sameCycle_sumCongr_inl_inr, Perm.SameCycle.refl]

theorem glue_pow_inl {d : P.M.D} (hd : ¬ P.M.σ.SameCycle P.base d) (n : ℕ) :
    ((CombMap.glue P.M Q.M P.base Q.base).σ ^ n) (Sum.inl d) = Sum.inl ((P.M.σ ^ n) d) := by
  have := swap_mul_pow_apply_of_not_sameCycle (π := Perm.sumCongr P.M.σ Q.M.σ)
    (a := Sum.inl P.base) (b := Sum.inr Q.base) (x := Sum.inl d)
    (by rwa [sameCycle_sumCongr_inl]) not_sameCycle_sumCongr_inr_inl n
  rw [sumCongr_pow', Perm.sumCongr_apply, Sum.map_inl] at this
  exact this

theorem glue_pow_inr {d : Q.M.D} (hd : ¬ Q.M.σ.SameCycle Q.base d) (n : ℕ) :
    ((CombMap.glue P.M Q.M P.base Q.base).σ ^ n) (Sum.inr d) = Sum.inr ((Q.M.σ ^ n) d) := by
  have := swap_mul_pow_apply_of_not_sameCycle (π := Perm.sumCongr P.M.σ Q.M.σ)
    (a := Sum.inl P.base) (b := Sum.inr Q.base) (x := Sum.inr d)
    not_sameCycle_sumCongr_inl_inr (by rwa [sameCycle_sumCongr_inr]) n
  rw [sumCongr_pow', Perm.sumCongr_apply, Sum.map_inr] at this
  exact this

theorem glue_cycleWord_inl {d : P.M.D} (hd : ¬ P.M.σ.SameCycle P.base d) :
    cycleWord (CombMap.glue P.M Q.M P.base Q.base).σ
      (C.letterWord ∘ Sum.elim P.lab Q.lab) (Sum.inl d) =
      cycleWord P.M.σ (C.letterWord ∘ P.lab) d := by
  rw [cycleWord_congr (π := Perm.sumCongr P.M.σ Q.M.σ) _ (fun n =>
    (glue_pow_inl P Q hd n).trans (by rw [sumCongr_pow', Perm.sumCongr_apply, Sum.map_inl])),
    cycleWord_sumCongr_inl]
  rfl

theorem glue_cycleWord_inr {d : Q.M.D} (hd : ¬ Q.M.σ.SameCycle Q.base d) :
    cycleWord (CombMap.glue P.M Q.M P.base Q.base).σ
      (C.letterWord ∘ Sum.elim P.lab Q.lab) (Sum.inr d) =
      cycleWord Q.M.σ (C.letterWord ∘ Q.lab) d := by
  rw [cycleWord_congr (π := Perm.sumCongr P.M.σ Q.M.σ) _ (fun n =>
    (glue_pow_inr P Q hd n).trans (by rw [sumCongr_pow', Perm.sumCongr_apply, Sum.map_inr])),
    cycleWord_sumCongr_inr]
  rfl

/-- **Gluing raw pictures**: merging the marked vertices of raw pictures for `x` and `y` gives
a raw picture for `x * y`. -/
def RawPicture.glue : C.RawPicture (x * y) where
  M := CombMap.glue P.M Q.M P.base Q.base
  lab := Sum.elim P.lab Q.lab
  base := Sum.inl P.base
  connected := CombMap.glue_connected _ _ _ _ P.connected Q.connected
  spherical := by rw [CombMap.glue_euler, P.spherical, Q.spherical]; norm_num
  type_σ := by
    rintro (d | d) hd
    · rw [glue_marked_inl] at hd
      have := glue_pow_inl P Q hd 1
      simp only [pow_one] at this
      rw [this]
      exact P.type_σ d hd
    · rw [glue_marked_inr] at hd
      have := glue_pow_inr P Q hd 1
      simp only [pow_one] at this
      rw [this]
      exact Q.type_σ d hd
  local_eq := by
    rintro (d | d) hd
    · rw [glue_marked_inl] at hd
      rw [glue_cycleWord_inl P Q hd]
      exact P.local_eq d hd
    · rw [glue_marked_inr] at hd
      rw [glue_cycleWord_inr P Q hd]
      exact Q.local_eq d hd
  edge_interior := by
    rintro (d | d) hd hd'
    · rw [glue_marked_inl] at hd
      change ¬ Perm.SameCycle _ _ (Sum.inl (P.M.α d)) at hd'
      rw [glue_marked_inl] at hd'
      exact P.edge_interior d hd hd'
    · rw [glue_marked_inr] at hd
      change ¬ Perm.SameCycle _ _ (Sum.inr (Q.M.α d)) at hd'
      rw [glue_marked_inr] at hd'
      exact Q.edge_interior d hd hd'
  edge_boundary := by
    rintro (d | d) hd
    · rw [glue_marked_inl] at hd
      change ¬ Perm.SameCycle _ _ (Sum.inl (P.M.α d)) ∧ P.lab (P.M.α d) = (P.lab d).inv
      rw [glue_marked_inl]
      exact P.edge_boundary d hd
    · rw [glue_marked_inr] at hd
      change ¬ Perm.SameCycle _ _ (Sum.inr (Q.M.α d)) ∧ Q.lab (Q.M.α d) = (Q.lab d).inv
      rw [glue_marked_inr]
      exact Q.edge_boundary d hd
  boundary_word := by
    change cycleWord (swap (Sum.inl P.base) (Sum.inr Q.base) * Perm.sumCongr P.M.σ Q.M.σ)
      (C.letterWord ∘ Sum.elim P.lab Q.lab) (Sum.inl P.base) = x * y
    rw [cycleWord_swap_mul _ not_sameCycle_sumCongr_inl_inr, cycleWord_sumCongr_inl,
      cycleWord_sumCongr_inr]
    exact congrArg₂ (· * ·) P.boundary_word Q.boundary_word

end Glue

/-! ### Moving the base dart -/

theorem sameCycle_inv_apply_left' {D : Type*} {π : Perm D} {x y : D} :
    π.SameCycle (π⁻¹ x) y ↔ π.SameCycle x y := by
  have hb : π.SameCycle (π⁻¹ x) x := ⟨1, by simp⟩
  exact ⟨fun h => hb.symm.trans h, fun h => hb.trans h⟩

/-- **Moving the base dart** back by one position around the marked vertex conjugates the marked
word by the letter at the new base dart. -/
def RawPicture.rotate {x : Monoid.CoprodI C.loc} (P : C.RawPicture x) :
    C.RawPicture (C.letterWord (P.lab (P.M.σ⁻¹ P.base)) * x *
      (C.letterWord (P.lab (P.M.σ⁻¹ P.base)))⁻¹) where
  M := P.M
  lab := P.lab
  base := P.M.σ⁻¹ P.base
  connected := P.connected
  spherical := P.spherical
  type_σ d hd := P.type_σ d (by rwa [sameCycle_inv_apply_left'] at hd)
  local_eq d hd := P.local_eq d (by rwa [sameCycle_inv_apply_left'] at hd)
  edge_interior d hd hd' := P.edge_interior d (by rwa [sameCycle_inv_apply_left'] at hd)
    (by rwa [sameCycle_inv_apply_left'] at hd')
  edge_boundary d hd := by
    rw [sameCycle_inv_apply_left'] at hd ⊢
    exact P.edge_boundary d hd
  boundary_word := by
    have h := cycleWord_apply P.M.σ (C.letterWord ∘ P.lab) (P.M.σ⁻¹ P.base)
    rw [show P.M.σ (P.M.σ⁻¹ P.base) = P.base by simp] at h
    simp only [Function.comp_apply] at h
    calc _ = C.letterWord (P.lab (P.M.σ⁻¹ P.base)) *
          ((C.letterWord (P.lab (P.M.σ⁻¹ P.base)))⁻¹ *
            cycleWord P.M.σ (C.letterWord ∘ P.lab) (P.M.σ⁻¹ P.base) *
            C.letterWord (P.lab (P.M.σ⁻¹ P.base))) *
          (C.letterWord (P.lab (P.M.σ⁻¹ P.base)))⁻¹ := by group
      _ = _ := by rw [← h, P.boundary_word]

/-! ### The two basic pictures -/

/-- The labels of the relator picture on the triangle (`CombMap.triangle`): the marked vertex
`{0, 5}`, the index vertex `{1, 2}` and the triple vertex `{3, 4}`. -/
def relatorLab (v : V) (t : T) (h : C.inc v t) (a : C.A v) : Fin 6 → C.Letter :=
  ![⟨Sum.inl v, a⟩, ⟨Sum.inl v, a⁻¹⟩, ⟨Sum.inl v, a⟩, ⟨Sum.inr t, (C.φ v t h a)⁻¹⟩,
    ⟨Sum.inr t, C.φ v t h a⟩, ⟨Sum.inr t, (C.φ v t h a)⁻¹⟩]

theorem triangle_marked_iff (d : Fin 6) :
    CombMap.triangle.σ.SameCycle (0 : Fin 6) d ↔ d = 0 ∨ d = 5 := by
  rw [sameCycle_iff_of_invariant (N := 2) CombMap.triangle.σ (![0, 1, 1, 2, 2, 0] : Fin 6 → Fin 3)
    (by decide) (by decide)]
  fin_cases d <;> decide

/-- **The relator picture**: a raw picture for the defining relator `a · (φ v t h a)⁻¹`. -/
def relatorPicture (v : V) (t : T) (h : C.inc v t) (a : C.A v) :
    C.RawPicture (Monoid.CoprodI.of (i := Sum.inl v) a *
      (Monoid.CoprodI.of (i := Sum.inr t) (C.φ v t h a))⁻¹) where
  M := CombMap.triangle
  lab := relatorLab v t h a
  base := (0 : Fin 6)
  connected := CombMap.triangle_connected
  spherical := CombMap.triangle_euler
  type_σ := by
    intro d hd
    rw [triangle_marked_iff] at hd
    fin_cases d <;> first | exact (hd (by decide)).elim | rfl
  local_eq := by
    intro d hd
    rw [triangle_marked_iff] at hd
    rw [cycleWord_of_apply_apply _ _ _ (by revert d; decide) (by revert d; decide)]
    fin_cases d <;> first | exact (hd (by decide)).elim | simp [relatorLab, letterWord, CombMap.triangle, Equiv.swap_apply_def]
  edge_interior := by
    intro d hd hd'
    rw [triangle_marked_iff] at hd hd'
    fin_cases d <;> first | exact (hd (by decide)).elim | (exfalso; revert hd'; decide) |
      exact Or.inl ⟨v, t, h, a, rfl, rfl⟩ | exact Or.inr ⟨v, t, h, a, rfl, rfl⟩
  edge_boundary := by
    intro d hd
    rw [triangle_marked_iff] at hd ⊢
    rcases hd with rfl | rfl
    · exact ⟨by decide, rfl⟩
    · exact ⟨by decide, by simp [relatorLab, Letter.inv, CombMap.triangle, Equiv.swap_apply_def]⟩
  boundary_word := by
    rw [cycleWord_of_apply_apply _ _ _ (by decide) (by decide)]
    simp [relatorLab, letterWord, CombMap.triangle, Equiv.swap_apply_def]

/-- The labels of the letter-pair picture on the digon (`CombMap.digon`): the marked vertex
`{0, 3}` and one interior vertex `{1, 2}`. -/
def letterPairLab (m : C.Letter) : Fin 4 → C.Letter := ![m.inv, m, m.inv, m]

theorem digon_marked_iff (d : Fin 4) :
    CombMap.digon.σ.SameCycle (0 : Fin 4) d ↔ d = 0 ∨ d = 3 := by
  rw [sameCycle_iff_of_invariant (N := 2) CombMap.digon.σ (![0, 1, 1, 0] : Fin 4 → Fin 2)
    (by decide) (by decide)]
  fin_cases d <;> decide

variable (C) in
/-- **The letter-pair picture**: a raw picture for `g⁻¹ g`, for any letter `g`. -/
def letterPairPicture (m : C.Letter) :
    C.RawPicture ((C.letterWord m)⁻¹ * C.letterWord m) where
  M := CombMap.digon
  lab := letterPairLab m
  base := (0 : Fin 4)
  connected := CombMap.digon_connected
  spherical := CombMap.digon_euler
  type_σ := by
    intro d hd
    rw [digon_marked_iff] at hd
    fin_cases d <;> first | exact (hd (by decide)).elim | rfl
  local_eq := by
    intro d hd
    rw [digon_marked_iff] at hd
    rw [cycleWord_of_apply_apply _ _ _ (by revert d; decide) (by revert d; decide)]
    fin_cases d <;> first | exact (hd (by decide)).elim |
      simp [letterPairLab, letterWord_inv, CombMap.digon, Equiv.swap_apply_def]
  edge_interior := by
    intro d hd hd'
    rw [digon_marked_iff] at hd hd'
    fin_cases d <;> first | exact (hd (by decide)).elim | (exfalso; revert hd'; decide)
  edge_boundary := by
    intro d hd
    rw [digon_marked_iff] at hd ⊢
    rcases hd with rfl | rfl
    · exact ⟨by decide, by simp [letterPairLab, CombMap.digon, Equiv.swap_apply_def]⟩
    · exact ⟨by decide, rfl⟩
  boundary_word := by
    rw [cycleWord_of_apply_apply _ _ _ (by decide) (by decide)]
    simp [letterPairLab, letterWord_inv, CombMap.digon, Equiv.swap_apply_def]

/-! ### Closure properties and existence -/

theorem realizable_mul {x y : Monoid.CoprodI C.loc} (hx : C.Realizable x) (hy : C.Realizable y) :
    C.Realizable (x * y) :=
  ⟨hx.some.glue hy.some⟩

/-- Conjugation by a single letter. -/
theorem realizable_conj_letter (m : C.Letter) {x : Monoid.CoprodI C.loc} (hx : C.Realizable x) :
    C.Realizable (C.letterWord m * x * (C.letterWord m)⁻¹) := by
  obtain ⟨P⟩ := hx
  let R := (P.glue (C.letterPairPicture m)).rotate
  have hb : (P.glue (C.letterPairPicture m)).M.σ⁻¹ (P.glue (C.letterPairPicture m)).base =
      Sum.inr (3 : Fin 4) := by
    rw [Perm.inv_eq_iff_eq]
    change Sum.inl P.base = swap (Sum.inl P.base) (Sum.inr (0 : Fin 4))
      (Sum.inr (CombMap.digon.σ (3 : Fin 4)))
    rw [show CombMap.digon.σ (3 : Fin 4) = (0 : Fin 4) by decide, swap_apply_right]
  refine Realizable.of_eq ⟨R⟩ ?_
  change C.letterWord ((P.glue (C.letterPairPicture m)).lab
      ((P.glue (C.letterPairPicture m)).M.σ⁻¹ (P.glue (C.letterPairPicture m)).base)) *
    (x * ((C.letterWord m)⁻¹ * C.letterWord m)) * _ = _
  rw [hb]
  change C.letterWord m * (x * ((C.letterWord m)⁻¹ * C.letterWord m)) *
    (C.letterWord m)⁻¹ = _
  group

/-- Conjugation by an arbitrary element of the free product. -/
theorem realizable_conj (g : Monoid.CoprodI C.loc) {x : Monoid.CoprodI C.loc}
    (hx : C.Realizable x) : C.Realizable (g * x * g⁻¹) := by
  induction g using Monoid.CoprodI.induction_on generalizing x with
  | one => simpa using hx
  | of i m => exact realizable_conj_letter ⟨i, m⟩ hx
  | mul g₁ g₂ ih₁ ih₂ =>
    refine (ih₁ (ih₂ hx)).of_eq ?_
    group

theorem realizable_rel {r : Monoid.CoprodI C.loc} (hr : r ∈ C.rels) : C.Realizable r := by
  obtain ⟨v, t, h, a, rfl⟩ := hr
  exact ⟨relatorPicture v t h a⟩

/-- The inverse of a relator is a conjugate of a relator. -/
theorem rel_inv_eq (v : V) (t : T) (h : C.inc v t) (a : C.A v) :
    (Monoid.CoprodI.of (M := C.loc) (i := Sum.inl v) a *
      (Monoid.CoprodI.of (M := C.loc) (i := Sum.inr t) (C.φ v t h a))⁻¹)⁻¹ =
    Monoid.CoprodI.of (M := C.loc) (i := Sum.inr t) (C.φ v t h a) *
      (Monoid.CoprodI.of (M := C.loc) (i := Sum.inl v) a⁻¹ *
        (Monoid.CoprodI.of (M := C.loc) (i := Sum.inr t) (C.φ v t h a⁻¹))⁻¹) *
      (Monoid.CoprodI.of (M := C.loc) (i := Sum.inr t) (C.φ v t h a))⁻¹ := by
  rw [map_inv, map_inv, map_inv]
  group

/-- **Existence of raw pictures**: every element of the normal closure of the relators has a raw
picture (provided there is at least one local group). -/
theorem realizable_of_mem_normalClosure (k : V ⊕ T) {x : Monoid.CoprodI C.loc}
    (hx : x ∈ Subgroup.normalClosure C.rels) : C.Realizable x := by
  induction hx using Subgroup.closure_induction'' with
  | mem y hy =>
    obtain ⟨r, hr, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨c, rfl⟩ := isConj_iff.mp hc
    exact realizable_conj c (realizable_rel hr)
  | inv_mem y hy =>
    obtain ⟨r, hr, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨c, rfl⟩ := isConj_iff.mp hc
    obtain ⟨v, t, h, a, rfl⟩ := hr
    refine (realizable_conj (c * Monoid.CoprodI.of (i := Sum.inr t) (C.φ v t h a))
      (realizable_rel ⟨v, t, h, a⁻¹, rfl⟩)).of_eq ?_
    rw [conj_inv, rel_inv_eq]
    group
  | one =>
    exact Realizable.of_eq ⟨C.letterPairPicture ⟨k, 1⟩⟩ (inv_mul_cancel _)
  | mul y z _ _ hy hz => exact realizable_mul hy hz

/-- **Raw picture from a null word.**  If an element `a` of an index group maps to `1` in the
colimit, there is a raw picture whose marked word is `a` (viewed in the free product).  This uses
neither `NPC` nor the girth of the incidence graph. -/
theorem exists_rawPicture_of_ι_eq_one {v : V} {a : C.A v} (h : C.ι (Sum.inl v) a = 1) :
    Nonempty (C.RawPicture (Monoid.CoprodI.of (i := Sum.inl v) a)) :=
  realizable_of_mem_normalClosure (Sum.inl v) ((QuotientGroup.eq_one_iff _).mp h)

/-- The marked word `a` of `exists_rawPicture_of_ι_eq_one` is nonidentity in the free product
exactly when `a ≠ 1`. -/
theorem letter_ne_one {v : V} {a : C.A v} (ha : a ≠ 1) :
    Monoid.CoprodI.of (i := Sum.inl v) a ≠ (1 : Monoid.CoprodI C.loc) := by
  intro h
  exact ha (Monoid.CoprodI.of_injective (Sum.inl v) (h.trans (map_one _).symm))

end ConeComplex

end TheoremA
