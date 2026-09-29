module

public import Mathlib

/-!
# A certified checker for the girth bound `girth ≥ 12`

This file formalizes the combinatorial argument used in the proof of Proposition 2.1 of the
manuscript: in a bipartite graph, a cycle of length at most `10` produces two *distinct* paths of
the same length `≤ 5` with the same endpoints.  Hence, if for every vertex `x` the paths of length
`≤ 5` ending at `x` have pairwise distinct starting vertices, the graph has girth at least `12`.

The condition on paths is checked by an explicit enumeration (`pathsTo`), whose soundness is
proved here.
-/

@[expose] public section

namespace GirthCheck

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- Extend a (reversed-direction) path `v :: rest` by one new neighbour `w` of `v` placed in
front, provided `w` does not already occur. -/
def extend (nbrs : V → List V) : List V → List (List V)
  | [] => []
  | l@(v :: _) => ((nbrs v).filter (fun w => decide (w ∉ l))).map (fun w => w :: l)

/-- `pathsTo nbrs x n` lists supports of paths of length `n` *ending* at `x`
(the head of each list is the starting vertex). -/
def pathsTo (nbrs : V → List V) (x : V) : ℕ → List (List V)
  | 0 => [[x]]
  | n + 1 => (pathsTo nbrs x n).flatMap (extend nbrs)

/-- The local check at a vertex `x`: paths of length `≤ 5` ending at `x` have pairwise distinct
starting vertices. -/
def localCheck (nbrs : V → List V) (x : V) : Bool :=
  decide (((List.range 6).flatMap (pathsTo nbrs x)).map List.head?).Nodup

variable {G : SimpleGraph V}

theorem support_mem_pathsTo (nbrs : V → List V) (hn : ∀ a b, G.Adj a b ↔ b ∈ nbrs a)
    {u x : V} (p : G.Walk u x) (hp : p.IsPath) : p.support ∈ pathsTo nbrs x p.length := by
  induction p with
  | nil => simp [pathsTo]
  | @cons a b c h q ih =>
    rw [Walk.cons_isPath_iff] at hp
    have hq := ih hp.1
    simp only [Walk.length_cons, pathsTo, List.mem_flatMap, Walk.support_cons]
    refine ⟨q.support, hq, ?_⟩
    rw [Walk.support_eq_cons q]
    simp only [extend, List.mem_map, List.mem_filter, decide_eq_true_eq, List.cons.injEq,
      and_true]
    refine ⟨a, ⟨(hn b a).1 h.symm, ?_⟩, rfl⟩
    rw [← Walk.support_eq_cons q]
    exact hp.2

omit [DecidableEq V] in
/-- Parity of walks in a properly 2-coloured graph. -/
theorem even_length_iff (col : V → Bool) (hcol : ∀ a b, G.Adj a b → col a ≠ col b)
    {u x : V} (p : G.Walk u x) : Even p.length ↔ col u = col x := by
  induction p with
  | nil => simp
  | @cons a b c h q ih =>
    have := hcol a b h
    rw [Walk.length_cons, Nat.even_add_one, ih]
    cases hA : col a <;> cases hB : col b <;> cases hC : col c <;> simp_all

omit [DecidableEq V] in
/-- Two distinct paths of length `≤ 5` with the same endpoints, extracted from a short even cycle. -/
theorem exists_two_paths_of_cycle {u : V} (w : G.Walk u u) (hw : w.IsCycle)
    (he : Even w.length) :
    ∃ (y : V) (p q : G.Walk u y), p.IsPath ∧ q.IsPath ∧ p ≠ q ∧
      p.length = w.length / 2 ∧ q.length = w.length / 2 := by
  have h3 := hw.three_le_length
  obtain ⟨m, hm⟩ := he
  have hn : w.length = m + m := hm
  refine ⟨w.getVert m, w.take m, (w.drop m).reverse, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Walk.IsPath.getVert_injOn_iff]
    intro i hi j hj hij
    simp only [Walk.take_length, Set.mem_setOf_eq, Walk.take_getVert] at hi hj hij
    have := hw.getVert_injOn' (show m ⊓ i ≤ w.length - 1 by simp; omega)
      (show m ⊓ j ≤ w.length - 1 by simp; omega) hij
    omega
  · rw [← Walk.IsPath.getVert_injOn_iff]
    intro i hi j hj hij
    simp only [Walk.length_reverse, Walk.drop_length, Set.mem_setOf_eq, Walk.getVert_reverse,
      Walk.drop_getVert] at hi hj hij
    have := hw.getVert_injOn (show m + (w.length - m - i) ∈ {i | 1 ≤ i ∧ i ≤ w.length} by
        simp; omega)
      (show m + (w.length - m - j) ∈ {i | 1 ≤ i ∧ i ≤ w.length} by simp; omega) hij
    omega
  · intro h
    have h1 := congrArg (fun p => p.getVert 1) h
    simp only [Walk.take_getVert, Walk.getVert_reverse, Walk.drop_length, Walk.drop_getVert] at h1
    have := hw.getVert_injOn (show m ⊓ 1 ∈ {i | 1 ≤ i ∧ i ≤ w.length} by simp; omega)
      (show m + (w.length - m - 1) ∈ {i | 1 ≤ i ∧ i ≤ w.length} by simp; omega) h1
    omega
  · simp [Walk.take_length]; omega
  · simp [Walk.drop_length]; omega

/-- **Girth criterion.**  If the graph is properly 2-coloured and the local check succeeds at
every vertex, then every cycle has length at least `12`. -/
theorem twelve_le_egirth (nbrs : V → List V) (hn : ∀ a b, G.Adj a b ↔ b ∈ nbrs a)
    (col : V → Bool) (hcol : ∀ a b, G.Adj a b → col a ≠ col b)
    (hcheck : ∀ x, localCheck nbrs x = true) : 12 ≤ G.egirth := by
  rw [le_egirth]
  intro u w hw
  have he : Even w.length := (even_length_iff col hcol w).2 rfl
  by_contra hlt
  push_neg at hlt
  have hlt' : w.length ≤ 10 := by
    have : w.length < 12 := by exact_mod_cast hlt
    obtain ⟨k, hk⟩ := he
    omega
  obtain ⟨y, p, q, hp, hq, hpq, hpl, hql⟩ := exists_two_paths_of_cycle w hw he
  have hc := hcheck y
  simp only [localCheck, decide_eq_true_eq] at hc
  have memp : p.support ∈ (List.range 6).flatMap (pathsTo nbrs y) :=
    List.mem_flatMap.2 ⟨p.length, List.mem_range.2 (by omega), support_mem_pathsTo nbrs hn p hp⟩
  have memq : q.support ∈ (List.range 6).flatMap (pathsTo nbrs y) :=
    List.mem_flatMap.2 ⟨q.length, List.mem_range.2 (by omega), support_mem_pathsTo nbrs hn q hq⟩
  have hhead : p.support.head? = q.support.head? := by
    rw [Walk.support_eq_cons p, Walk.support_eq_cons q]; rfl
  exact hpq (Walk.ext_support (List.inj_on_of_nodup_map hc memp memq hhead))

end GirthCheck

end
