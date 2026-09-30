module

public import RequestProject.GirthCheck

/-!
# Oriented triple systems (Section 2 of the manuscript)

An oriented triple system on `V = {0, …, r-1}` is a finite list of triples `(i, j, k)`, read as
`(i, j) ⟶ k`.  We formalize

* its bipartite incidence graph `incidenceGraph r T` (vertex set `Fin r ⊕ Fin T.length`),
* the signed row `W_ℓ = e_i + e_j - e_k` of equation (2.1),
* the two hypotheses (2.2): `girth(L) ≥ 12` and `a W = e_0` for an integer vector `a`,

together with executable checkers (`girthCheck`, `rowCheck`, `wellFormedCheck`) whose soundness is
proved.  A concrete certificate can then be verified by evaluating the checkers.
-/

@[expose] public section

namespace TripleSystem

open SimpleGraph

/-- A triple `(i, j, k)` stands for `(i, j) ⟶ k`: inputs `i, j`, output `k`. -/
abbrev Triple := ℕ × ℕ × ℕ

/-- The three entries of a triple. -/
def Triple.entries (t : Triple) : List ℕ := [t.1, t.2.1, t.2.2]

/-- All entries lie in `{0, …, r-1}` and the three entries of each triple are distinct. -/
def WellFormed (r : ℕ) (T : List Triple) : Prop :=
  ∀ t ∈ T, t.1 < r ∧ t.2.1 < r ∧ t.2.2 < r ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

/-- The bipartite incidence graph `L`: one vertex per index `v < r`, one vertex per triple, and an
edge between `v` and `ℓ` when `v` is an entry of `ℓ`. -/
def incidenceGraph (r : ℕ) (T : List Triple) : SimpleGraph (Fin r ⊕ Fin T.length) where
  Adj x y := match x, y with
    | .inl v, .inr l => (v : ℕ) ∈ T[l].entries
    | .inr l, .inl v => (v : ℕ) ∈ T[l].entries
    | _, _ => False
  symm := ⟨by
    rintro (a | a) (b | b) h <;> simp_all⟩
  loopless := ⟨fun v => by cases v <;> simp⟩

/-- The signed row `W_ℓ = e_i + e_j - e_k ∈ ℤ^V` of a triple `ℓ = (i, j) ⟶ k`, eq. (2.1). -/
def row (t : Triple) (v : ℕ) : ℤ :=
  (if v = t.1 then 1 else 0) + (if v = t.2.1 then 1 else 0) - (if v = t.2.2 then 1 else 0)

/-- The integral row identity `a W = e_0` of (2.2). -/
def RowIdentity (r : ℕ) (T : List Triple) (a : Fin T.length → ℤ) : Prop :=
  ∀ v : Fin r, ∑ l : Fin T.length, a l * row T[l] v = if (v : ℕ) = 0 then 1 else 0

/-! ### Executable checkers -/

/-- Neighbours of a vertex of the incidence graph (index side computed by a scan). -/
def nbrsSlow (r : ℕ) (T : List Triple) : Fin r ⊕ Fin T.length → List (Fin r ⊕ Fin T.length)
  | .inl v => ((List.finRange T.length).filter (fun (l : Fin T.length) => decide ((v : ℕ) ∈ T[l].entries))).map
      Sum.inr
  | .inr l => ((List.finRange r).filter (fun (v : Fin r) => decide ((v : ℕ) ∈ T[l].entries))).map Sum.inl

/-- Table of neighbours of index vertices (computed once). -/
def nbrTable (r : ℕ) (T : List Triple) : Array (List (Fin r ⊕ Fin T.length)) :=
  Array.ofFn (fun v : Fin r => nbrsSlow r T (.inl v))

/-- Fast neighbour function using a precomputed table. -/
def nbrsFast (r : ℕ) (T : List Triple) (tbl : Array (List (Fin r ⊕ Fin T.length))) :
    Fin r ⊕ Fin T.length → List (Fin r ⊕ Fin T.length)
  | .inl v => tbl.getD v []
  | .inr l => ((T[l].entries).filterMap
      (fun v => if h : v < r then some (Sum.inl ⟨v, h⟩) else none))

/-- All vertices of the incidence graph. -/
def allVerts (r s : ℕ) : List (Fin r ⊕ Fin s) :=
  (List.finRange r).map Sum.inl ++ (List.finRange s).map Sum.inr

/-- The girth checker (the path test of Appendix A, run from every vertex). -/
def girthCheck (r : ℕ) (T : List Triple) : Bool :=
  let tbl := nbrTable r T
  (allVerts r T.length).all (fun x => GirthCheck.localCheck (nbrsFast r T tbl) x)

/-- The row-identity checker: computes `a W` coordinate by coordinate and compares with `e_0`. -/
def rowCheck (r : ℕ) (T : List Triple) (a : Fin T.length → ℤ) : Bool :=
  (List.finRange r).all (fun v =>
    (List.ofFn (fun l : Fin T.length => a l * row (T.toArray[l.1]'(by simp)) v)).sum ==
      if (v : ℕ) = 0 then 1 else 0)

/-- The well-formedness checker. -/
def wellFormedCheck (r : ℕ) (T : List Triple) : Bool :=
  T.all (fun t => decide (t.1 < r ∧ t.2.1 < r ∧ t.2.2 < r ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧
    t.2.1 ≠ t.2.2))

/-! ### Soundness -/

theorem adj_iff_mem_nbrsFast (r : ℕ) (T : List Triple) (a b : Fin r ⊕ Fin T.length) :
    (incidenceGraph r T).Adj a b ↔ b ∈ nbrsFast r T (nbrTable r T) a := by
  rcases a with v | l <;> rcases b with w | m
  · simp [incidenceGraph, nbrsFast, nbrTable, nbrsSlow]
  · simp [incidenceGraph, nbrsFast, nbrTable, nbrsSlow, Array.getD_eq_getD_getElem?]
  · simp only [incidenceGraph, nbrsFast, List.mem_filterMap]
    constructor
    · intro h; exact ⟨w, h, by simp⟩
    · rintro ⟨x, hx, hx'⟩
      split_ifs at hx' with h
      simp only [Option.some.injEq, Sum.inl.injEq] at hx'
      subst hx'; exact hx
  · simp [incidenceGraph, nbrsFast]

theorem mem_allVerts (r s : ℕ) (x : Fin r ⊕ Fin s) : x ∈ allVerts r s := by
  rcases x with v | l <;> simp [allVerts]

theorem twelve_le_egirth_of_girthCheck (r : ℕ) (T : List Triple) (h : girthCheck r T = true) :
    12 ≤ (incidenceGraph r T).egirth := by
  refine GirthCheck.twelve_le_egirth (nbrsFast r T (nbrTable r T)) (adj_iff_mem_nbrsFast r T)
    (fun x => x.isLeft) ?_ ?_
  · rintro (a | a) (b | b) h <;> simp_all [incidenceGraph]
  · intro x
    simp only [girthCheck, List.all_eq_true] at h
    exact h x (mem_allVerts _ _ x)

theorem rowIdentity_of_rowCheck (r : ℕ) (T : List Triple) (a : Fin T.length → ℤ)
    (h : rowCheck r T a = true) : RowIdentity r T a := by
  intro v
  simp only [rowCheck, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies] at h
  have := h v
  rw [List.sum_ofFn] at this
  simpa using this

theorem wellFormed_of_wellFormedCheck (r : ℕ) (T : List Triple)
    (h : wellFormedCheck r T = true) : WellFormed r T := by
  intro t ht
  simp only [wellFormedCheck, List.all_eq_true, decide_eq_true_eq] at h
  exact h t ht

end TripleSystem

end
