module

public import Mathlib

/-!
# Euler-characteristic counting for bipartite combinatorial maps

This file contains the final counting step of the combinatorial ("reduced picture") proof of the
developability statement behind Lemma 3.1, with the incidence counts proved for an explicit
representation of maps.

## The representation

A `BipartiteMap` is a combinatorial map (rotation system) whose vertices are of two kinds,
*triple vertices* and *index vertices*, every edge joining a triple vertex to an index vertex:

* the edges form a finite type `E`;
* the darts (edge ends) are `E × Bool`; the dart `(e, true)` is the end of `e` at its triple
  vertex, `(e, false)` its end at its index vertex;
* the edge involution is `α (e, b) = (e, !b)`;
* a permutation `σ` of the darts (the cyclic order of darts around each vertex) preserves the
  kind of a dart; the *vertices* are the `σ`-orbits;
* the *faces* are the orbits of `φ = σ * α`; the length of a face boundary is the size of its
  orbit (so a bridge contributes two darts to its face boundary).

The Euler characteristic is `χ = V_T + V_I - E + F`.  A connected map is spherical exactly when
`χ = 2`.

## Results

* `BipartiteMap.three_mul_numTripleVertices_le` : `3 V_T ≤ E` if every triple vertex has degree
  `≥ 3`;
* `BipartiteMap.two_mul_numIndexVertices_le` : `2 (V_I - 1) ≤ E` if every index vertex except
  possibly one has degree `≥ 2`;
* `BipartiteMap.twelve_mul_numFaces_le` : `12 F ≤ 2 E` if every face boundary has `≥ 12` darts;
* `BipartiteMap.euler_le_one` : under these three bounds, `χ ≤ 1`, so the map is not spherical
  (`BipartiteMap.euler_ne_two`); with no exceptional vertex, `χ ≤ 0` (`euler_le_zero`).
* `BipartiteMap.singleEdge_euler` : sanity check — the one-edge map has `χ = 2`;
* `SimpleGraph.egirth_le_length_of_nonBacktracking` : a nonempty closed walk without
  backtracking has length at least the girth.  This is the graph-theoretic input for the face
  bound: large girth bounds the length of a *non-backtracking* closed walk, but not of an
  arbitrary closed walk.
-/

@[expose] public section

open Finset

namespace TheoremA

/-! ### Two counting lemmas -/

/-- If every fibre of `f` on `s` has at least `k` elements, then `k · #f(s) ≤ #s`. -/
theorem mul_card_image_le {ι β : Type*} [DecidableEq β] (f : ι → β) (s : Finset ι) (k : ℕ)
    (h : ∀ a ∈ s, k ≤ #{x ∈ s | f x = f a}) : k * #(s.image f) ≤ #s := by
  rw [card_eq_sum_card_image f s, mul_comm, ← smul_eq_mul]
  refine card_nsmul_le_sum _ _ _ fun b hb => ?_
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
  exact h a ha

/-- If every fibre of `f` on `s` other than the fibre over `b₀` has at least `k` elements, then
`k · (#f(s) - 1) ≤ #s`. -/
theorem mul_card_image_sub_one_le {ι β : Type*} [DecidableEq β] (f : ι → β) (s : Finset ι)
    (k : ℕ) (b₀ : β) (h : ∀ a ∈ s, f a ≠ b₀ → k ≤ #{x ∈ s | f x = f a}) :
    k * (#(s.image f) - 1) ≤ #s := by
  rw [card_eq_sum_card_image f s]
  calc k * (#(s.image f) - 1) ≤ k * #((s.image f).erase b₀) :=
        Nat.mul_le_mul_left _ (pred_card_le_card_erase)
    _ ≤ ∑ b ∈ (s.image f).erase b₀, #{a ∈ s | f a = b} := by
        rw [mul_comm, ← smul_eq_mul]
        refine card_nsmul_le_sum _ _ _ fun b hb => ?_
        obtain ⟨hb0, hb⟩ := mem_erase.mp hb
        obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
        exact h a ha hb0
    _ ≤ ∑ b ∈ s.image f, #{a ∈ s | f a = b} :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => Nat.zero_le _

/-! ### Bipartite combinatorial maps -/

/-- A finite bipartite combinatorial map: edges `E`, darts `E × Bool` (`true` = end at the triple
vertex, `false` = end at the index vertex), and a vertex rotation `σ` preserving the kind of a
dart. -/
structure BipartiteMap where
  /-- The edges. -/
  E : Type
  [instFintype : Fintype E]
  [instDecEq : DecidableEq E]
  /-- The rotation of darts around vertices. -/
  σ : Equiv.Perm (E × Bool)
  /-- The rotation preserves the kind (triple / index) of a dart. -/
  σ_snd : ∀ d, (σ d).2 = d.2

attribute [instance] BipartiteMap.instFintype BipartiteMap.instDecEq

namespace BipartiteMap

open scoped Classical

variable (M : BipartiteMap)

/-- The edge involution `(e, b) ↦ (e, !b)`. -/
def α : Equiv.Perm (M.E × Bool) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv d := by simp
  right_inv d := by simp

/-- The face permutation `φ = σ ∘ α`; faces are its orbits. -/
def φ : Equiv.Perm (M.E × Bool) := M.σ * M.α

/-- The vertex of a dart (its `σ`-orbit). -/
noncomputable def vertexOf (d : M.E × Bool) : Quotient (Equiv.Perm.SameCycle.setoid M.σ) :=
  Quotient.mk _ d

/-- The face of a dart (its `φ`-orbit). -/
noncomputable def faceOf (d : M.E × Bool) : Quotient (Equiv.Perm.SameCycle.setoid M.φ) :=
  Quotient.mk _ d

/-- The darts at triple vertices. -/
noncomputable def tripleDarts : Finset (M.E × Bool) := {d | d.2 = true}

/-- The darts at index vertices. -/
noncomputable def indexDarts : Finset (M.E × Bool) := {d | d.2 = false}

/-- Number of triple vertices. -/
noncomputable def numTripleVertices : ℕ := #(M.tripleDarts.image M.vertexOf)

/-- Number of index vertices. -/
noncomputable def numIndexVertices : ℕ := #(M.indexDarts.image M.vertexOf)

/-- Number of edges. -/
def numEdges : ℕ := Fintype.card M.E

/-- Number of faces. -/
noncomputable def numFaces : ℕ := #((univ : Finset (M.E × Bool)).image M.faceOf)

/-- The Euler characteristic `V_T + V_I - E + F`. -/
noncomputable def euler : ℤ :=
  M.numTripleVertices + M.numIndexVertices - M.numEdges + M.numFaces

/-- The degree of the vertex at a dart: the size of its `σ`-orbit. -/
noncomputable def degree (d : M.E × Bool) : ℕ := #{x | M.σ.SameCycle d x}

/-- The length of the face boundary at a dart: the size of its `φ`-orbit. -/
noncomputable def faceLength (d : M.E × Bool) : ℕ := #{x | M.φ.SameCycle d x}

theorem sameCycle_snd {d x : M.E × Bool} (h : M.σ.SameCycle d x) : x.2 = d.2 := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, M.σ_snd, ih]

theorem card_tripleDarts : #M.tripleDarts = M.numEdges := by
  have : M.tripleDarts = univ.map ⟨fun e => (e, true), fun _ _ h => congrArg Prod.fst h⟩ := by
    ext ⟨e, b⟩
    cases b <;> simp [tripleDarts]
  rw [this, card_map, card_univ, numEdges]

theorem card_indexDarts : #M.indexDarts = M.numEdges := by
  have : M.indexDarts = univ.map ⟨fun e => (e, false), fun _ _ h => congrArg Prod.fst h⟩ := by
    ext ⟨e, b⟩
    cases b <;> simp [indexDarts]
  rw [this, card_map, card_univ, numEdges]

theorem card_darts : Fintype.card (M.E × Bool) = 2 * M.numEdges := by
  simp [numEdges, mul_comm]

/-- The fibre of `vertexOf` through a dart of a given kind, inside the darts of that kind, is its
whole `σ`-orbit. -/
theorem fiber_vertexOf (b : Bool) (d : M.E × Bool) (hd : d.2 = b) :
    #{x ∈ ({d | d.2 = b} : Finset (M.E × Bool)) | M.vertexOf x = M.vertexOf d} = M.degree d := by
  unfold degree
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, vertexOf, Quotient.eq]
  constructor
  · rintro ⟨-, h⟩; exact (Equiv.Perm.SameCycle.symm h)
  · intro h; exact ⟨(M.sameCycle_snd h).trans hd, h.symm⟩

/-- **Triple vertices.** If every triple vertex has degree at least `3`, then `3 V_T ≤ E`. -/
theorem three_mul_numTripleVertices_le (hT : ∀ e : M.E, 3 ≤ M.degree (e, true)) :
    3 * M.numTripleVertices ≤ M.numEdges := by
  rw [← card_tripleDarts]
  refine mul_card_image_le _ _ _ fun a ha => ?_
  have ha' : a.2 = true := by simpa [tripleDarts] using ha
  rw [tripleDarts, fiber_vertexOf M true a ha']
  obtain ⟨e, b⟩ := a
  simp only at ha'
  subst ha'
  exact hT e

/-- **Index vertices, with one exception.** If at most one index vertex has degree `< 2`, then
`2 (V_I - 1) ≤ E`. -/
theorem two_mul_numIndexVertices_le
    (hI : ∀ e e' : M.E, M.degree (e, false) < 2 → M.degree (e', false) < 2 →
      M.σ.SameCycle (e, false) (e', false)) :
    2 * (M.numIndexVertices - 1) ≤ M.numEdges := by
  rw [← card_indexDarts]
  by_cases hex : ∃ e : M.E, M.degree (e, false) < 2
  · obtain ⟨e₀, he₀⟩ := hex
    refine mul_card_image_sub_one_le _ _ _ (M.vertexOf (e₀, false)) fun a ha hne => ?_
    have ha' : a.2 = false := by simpa [indexDarts] using ha
    rw [indexDarts, fiber_vertexOf M false a ha']
    obtain ⟨e, b⟩ := a
    simp only at ha'
    subst ha'
    by_contra hlt
    exact hne (Quotient.sound (hI e e₀ (by omega) he₀))
  · push_neg at hex
    calc 2 * (M.numIndexVertices - 1) ≤ 2 * M.numIndexVertices := by omega
      _ ≤ _ := by
        refine mul_card_image_le _ _ _ fun a ha => ?_
        have ha' : a.2 = false := by simpa [indexDarts] using ha
        rw [indexDarts, fiber_vertexOf M false a ha']
        obtain ⟨e, b⟩ := a
        simp only at ha'
        subst ha'
        exact hex e

/-- **Index vertices, no exception.** If every index vertex has degree `≥ 2`, then `2 V_I ≤ E`. -/
theorem two_mul_numIndexVertices_le' (hI : ∀ e : M.E, 2 ≤ M.degree (e, false)) :
    2 * M.numIndexVertices ≤ M.numEdges := by
  rw [← card_indexDarts]
  refine mul_card_image_le _ _ _ fun a ha => ?_
  have ha' : a.2 = false := by simpa [indexDarts] using ha
  rw [indexDarts, fiber_vertexOf M false a ha']
  obtain ⟨e, b⟩ := a
  simp only at ha'
  subst ha'
  exact hI e

/-- **Faces.** If every face boundary has at least `12` darts, then `12 F ≤ 2 E`. -/
theorem twelve_mul_numFaces_le (hF : ∀ d, 12 ≤ M.faceLength d) :
    12 * M.numFaces ≤ 2 * M.numEdges := by
  rw [← card_darts, ← card_univ]
  refine mul_card_image_le _ _ _ fun a _ => ?_
  refine (hF a).trans_eq ?_
  unfold faceLength
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, faceOf, Quotient.eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- **Euler bound with one exceptional index vertex.**  If every triple vertex has degree `≥ 3`,
every index vertex except possibly one has degree `≥ 2`, and every face boundary has `≥ 12`
darts, then `χ ≤ 1`. -/
theorem euler_le_one (hT : ∀ e : M.E, 3 ≤ M.degree (e, true))
    (hI : ∀ e e' : M.E, M.degree (e, false) < 2 → M.degree (e', false) < 2 →
      M.σ.SameCycle (e, false) (e', false))
    (hF : ∀ d, 12 ≤ M.faceLength d) : M.euler ≤ 1 := by
  have h1 := M.three_mul_numTripleVertices_le hT
  have h2 := M.two_mul_numIndexVertices_le hI
  have h3 := M.twelve_mul_numFaces_le hF
  unfold euler
  omega

/-- Under the hypotheses of `euler_le_one` the map is not spherical. -/
theorem euler_ne_two (hT : ∀ e : M.E, 3 ≤ M.degree (e, true))
    (hI : ∀ e e' : M.E, M.degree (e, false) < 2 → M.degree (e', false) < 2 →
      M.σ.SameCycle (e, false) (e', false))
    (hF : ∀ d, 12 ≤ M.faceLength d) : M.euler ≠ 2 := by
  have := M.euler_le_one hT hI hF
  omega

/-- **Euler bound with no exceptional vertex**: `χ ≤ 0`. -/
theorem euler_le_zero (hT : ∀ e : M.E, 3 ≤ M.degree (e, true))
    (hI : ∀ e : M.E, 2 ≤ M.degree (e, false))
    (hF : ∀ d, 12 ≤ M.faceLength d) : M.euler ≤ 0 := by
  have h1 := M.three_mul_numTripleVertices_le hT
  have h2 := M.two_mul_numIndexVertices_le' hI
  have h3 := M.twelve_mul_numFaces_le hF
  unfold euler
  omega

/-- Sanity check of the definitions: the map with a single edge (a tree on the sphere with two
vertices and one face). -/
def singleEdge : BipartiteMap where
  E := Unit
  σ := 1
  σ_snd _ := rfl

/-- The single-edge map has Euler characteristic `2`, as a spherical map should. -/
theorem singleEdge_euler : singleEdge.euler = 2 := by
  have hall : ∀ d d' : singleEdge.E × Bool, singleEdge.φ.SameCycle d d' := by
    have key : singleEdge.φ.SameCycle ((), true) ((), false) := ⟨1, rfl⟩
    rintro ⟨⟨⟩, b⟩ ⟨⟨⟩, b'⟩
    cases b <;> cases b'
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact key.symm
    · exact key
    · exact Equiv.Perm.SameCycle.refl _ _
  have h1 : singleEdge.numTripleVertices = 1 := by
    rw [numTripleVertices, card_eq_one]
    exact ⟨singleEdge.vertexOf ((), true), by
      ext q; simp only [mem_image, mem_singleton]
      constructor
      · rintro ⟨⟨⟨⟩, b⟩, hb, rfl⟩; simp [tripleDarts] at hb; subst hb; rfl
      · rintro rfl; exact ⟨((), true), by simp [tripleDarts], rfl⟩⟩
  have h2 : singleEdge.numIndexVertices = 1 := by
    rw [numIndexVertices, card_eq_one]
    exact ⟨singleEdge.vertexOf ((), false), by
      ext q; simp only [mem_image, mem_singleton]
      constructor
      · rintro ⟨⟨⟨⟩, b⟩, hb, rfl⟩; simp [indexDarts] at hb; subst hb; rfl
      · rintro rfl; exact ⟨((), false), by simp [indexDarts], rfl⟩⟩
  have h3 : singleEdge.numFaces = 1 := by
    rw [numFaces, card_eq_one]
    exact ⟨singleEdge.faceOf ((), true), by
      ext q; simp only [mem_image, mem_singleton, mem_univ, true_and]
      constructor
      · rintro ⟨d, rfl⟩; exact Quotient.sound (hall _ _)
      · rintro rfl; exact ⟨_, rfl⟩⟩
  have h4 : singleEdge.numEdges = 1 := rfl
  simp [euler, h1, h2, h3, h4]
end BipartiteMap

end TheoremA

/-! ### Non-backtracking closed walks and girth -/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A walk is *non-backtracking* if it never immediately returns along the edge it just used,
i.e. its `(i+2)`-nd vertex differs from its `i`-th vertex. -/
def Walk.NonBacktracking {u v : V} (p : G.Walk u v) : Prop :=
  ∀ i, i + 2 ≤ p.length → p.getVert (i + 2) ≠ p.getVert i

theorem Walk.NonBacktracking.of_cons {u v w : V} {h : G.Adj u v} {q : G.Walk v w}
    (hp : (Walk.cons h q).NonBacktracking) : q.NonBacktracking := by
  intro i hi
  have := hp (i + 1) (by simp [Walk.length_cons]; omega)
  simpa [Walk.getVert_cons_succ] using this

theorem Walk.NonBacktracking.cons_getVert_two {u v w : V} {h : G.Adj u v} {q : G.Walk v w}
    (hp : (Walk.cons h q).NonBacktracking) (hq : 2 ≤ q.length + 1) : q.getVert 1 ≠ u := by
  have := hp 0 (by simp [Walk.length_cons]; omega)
  simpa [Walk.getVert_cons_succ] using this

/-- A non-backtracking walk whose support has a repetition contains a cycle no longer than the
walk. -/
theorem Walk.exists_isCycle_of_nonBacktracking [DecidableEq V] :
    ∀ {u v : V} (p : G.Walk u v), p.NonBacktracking → ¬ p.support.Nodup →
      ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ c.length ≤ p.length
  | _, _, .nil, _, hnd => absurd (by simp) hnd
  | u, _, .cons (v := x) h q, hp, hnd => by
    by_cases hq : q.support.Nodup
    · have hu : u ∈ q.support := by
        rw [Walk.support_cons, List.nodup_cons] at hnd
        by_contra hu
        exact hnd ⟨hu, hq⟩
      have hqp : q.IsPath := Walk.IsPath.mk' hq
      set P := q.takeUntil u hu with hP
      have hPp : P.IsPath := hqp.takeUntil hu
      refine ⟨u, .cons h P, ?_, ?_⟩
      · rw [Walk.cons_isCycle_iff]
        refine ⟨hPp, fun hmem => ?_⟩
        cases hPc : P with
        | nil => rw [hPc] at hmem; simp at hmem
        | cons h' P' =>
          rename_i y
          rw [hPc] at hmem hPp
          rw [Walk.cons_isPath_iff] at hPp
          rw [Walk.edges_cons, List.mem_cons] at hmem
          rcases hmem with he | he
          · -- the edge `s(u, x)` equals `s(x, y)`, so `y = u` and `q` starts `x → u`
            have hyu : y = u := by
              rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact (G.loopless.irrefl _ (h1 ▸ h)).elim
              · exact h1.symm
            have hlen : 1 ≤ P.length := by rw [hPc]; simp
            have hlen' : P.length ≤ q.length := by
              have := q.length_takeUntil_le hu
              rwa [← hP] at this
            apply hp.cons_getVert_two (by omega)
            have := q.getVert_takeUntil hu (n := 1) hlen
            rw [← hP] at this
            rw [← this, hPc]
            simpa using hyu
          · exact hPp.2 (Walk.snd_mem_support_of_mem_edges _ he)
      · simp only [Walk.length_cons]
        have := q.length_takeUntil_le hu
        rw [← hP] at this
        omega
    · obtain ⟨y, c, hc, hlen⟩ := Walk.exists_isCycle_of_nonBacktracking q hp.of_cons hq
      exact ⟨y, c, hc, by simp [Walk.length_cons]; omega⟩

/-- **Girth bounds non-backtracking closed walks.**  A nonempty non-backtracking closed walk has
length at least the (extended) girth of the graph. -/
theorem egirth_le_length_of_nonBacktracking {u : V} (p : G.Walk u u) (hp : p.NonBacktracking)
    (hlen : 0 < p.length) : G.egirth ≤ p.length := by
  classical
  have hnd : ¬ p.support.Nodup := by
    cases p with
    | nil => simp at hlen
    | cons h q =>
      rw [Walk.support_cons, List.nodup_cons, not_and_or, not_not]
      exact Or.inl q.end_mem_support
  obtain ⟨x, c, hc, hcl⟩ := Walk.exists_isCycle_of_nonBacktracking p hp hnd
  exact (egirth_le_length hc).trans (by exact_mod_cast hcl)

end SimpleGraph
