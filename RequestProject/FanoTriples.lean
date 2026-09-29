module

public import RequestProject.GirthKernel

/-!
# The Fano-plane triple system (Proposition 3.2 of the revised manuscript)

Points and lines are numbered modulo seven, with `L_j = {j, j+1, j+3}`.
The retained flags are numbered as follows:

* `0` is the distinguished index, `1` is `a`, and `2` is `b`;
* `f_{j,0}` has number `3+j`, and `f_{j,1}` has number `10+j`;
* `f_{j,3}` has number `16+j`, for `1 ≤ j ≤ 6`.

The missing flag `f_{0,3}` is replaced by `b` in the point triple at `3`,
and by `a` in the line triple at `0`. The extra triple is `(b,0) → a`.
The definitions below follow these formulas, rather than using a searched example.

All finite checks are evaluated by the Lean kernel. The existing soundness
theorems turn the checks into the actual girth bound and integral row identity.
No externally executed computation is part of the proof.
-/

@[expose] public section

namespace FanoTriples

open TripleSystem

def a : ℕ := 1
def b : ℕ := 2
def flag0 (j : ℕ) : ℕ := 3 + j
def flag1 (j : ℕ) : ℕ := 10 + j
/-- Used only for the retained flags, i.e. `1 ≤ j ≤ 6`. -/
def flag3 (j : ℕ) : ℕ := 16 + j

/-- The twenty retained flags and the three additional indices give exactly `Fin 23`. -/
theorem index_labels :
    [0, a, b] ++ (List.range 7).map flag0 ++ (List.range 7).map flag1 ++
      (List.range 6).map (fun j => flag3 (j + 1)) = List.range 23 := by
  decide +kernel

/-- The triple `π_p` of flags through point `p`, replacing `f_{0,3}` by `b`. -/
def pointTriple (p : ℕ) : Triple :=
  (flag0 p, flag1 ((p + 6) % 7), if p = 3 then b else flag3 ((p + 4) % 7))

/-- The triple `λ_j` of flags on line `L_j`, replacing `f_{0,3}` by `a`. -/
def lineTriple (j : ℕ) : Triple :=
  (flag0 j, flag1 j, if j = 0 then a else flag3 j)

/-- The triple subdividing the removed flag, with the distinguished pendant index. -/
def gamma : Triple := (b, 0, a)

/-- The order is `π_0,...,π_6,λ_0,...,λ_6,γ`. -/
def triples : List Triple :=
  (List.range 7).map pointTriple ++ (List.range 7).map lineTriple ++ [gamma]

theorem triples_length : triples.length = 15 := by decide +kernel

/-- The list represents a set of fifteen different triples, as in Definition 3.1. -/
theorem triples_nodup : triples.Nodup := by decide +kernel

/-- The coefficients are `+1` at point triples and `γ`, and `-1` at line triples. -/
def nu (l : Fin triples.length) : ℤ :=
  if l.val < 7 then 1 else if l.val < 14 then -1 else 1

theorem nu_unit (l : Fin triples.length) : nu l = 1 ∨ nu l = -1 := by
  simp only [nu]
  split_ifs <;> simp

theorem wellFormed_check : wellFormedCheck 23 triples = true := by decide +kernel

theorem wellFormed : WellFormed 23 triples :=
  wellFormed_of_wellFormedCheck 23 triples wellFormed_check

set_option maxRecDepth 100000 in
theorem row_check : rowCheck 23 triples nu = true := by decide +kernel

/-- Equation (3.2), with the signs prescribed in the manuscript. -/
theorem rowIdentity : RowIdentity 23 triples nu :=
  rowIdentity_of_rowCheck 23 triples nu row_check

/-- The incidence neighbors, numbered `0,...,22` and then `23,...,37`. -/
def neighbors (v : ℕ) : List ℕ :=
  if v < 23 then
    triples.zipIdx.filterMap (fun (t, l) =>
      if GirthKernel.memN v t.entries then some (23 + l) else none)
  else if v < 38 then (triples[v - 23]?.getD (0, 0, 0)).entries else []

/-- Store a finite table in the kernel-friendly binary-tree representation. -/
def tableTree : ℕ → (ℕ → List ℕ) → GirthKernel.NTree
  | 0, _ => .leaf
  | k + 1, f => .node (tableTree k (fun i => f (2 * i + 1))) (f 0)
      (tableTree k (fun i => f (2 * i + 2)))

def tree : GirthKernel.NTree := tableTree 6 neighbors

set_option maxRecDepth 100000 in
theorem incidence_check : GirthKernel.incCheck tree 23 0 triples = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem girth_check : GirthKernel.girthCheckN 38 tree 23 = true := by decide +kernel

/-- Equation (3.1), for the actual incidence graph on the 23 indices and 15 triples. -/
theorem girth : 12 ≤ (incidenceGraph 23 triples).egirth :=
  GirthKernel.twelve_le_egirth_incidence 38 tree 23 triples
    (by rw [triples_length]) incidence_check girth_check

/-- **Proposition 3.2**, including the sizes and the unit coefficients. -/
theorem proposition_3_2 : triples.length = 15 ∧ triples.Nodup ∧
    WellFormed 23 triples ∧ 12 ≤ (incidenceGraph 23 triples).egirth ∧
    RowIdentity 23 triples nu ∧ (∀ l, nu l = 1 ∨ nu l = -1) :=
  ⟨triples_length, triples_nodup, wellFormed, girth, rowIdentity, nu_unit⟩

/-- The exact interface used by the general degree-raising argument. -/
theorem exists_tripleSystem : ∃ (r : ℕ) (T : List Triple), 0 < r ∧ WellFormed r T ∧
    12 ≤ (incidenceGraph r T).egirth ∧ ∃ c, RowIdentity r T c :=
  ⟨23, triples, by decide, wellFormed, girth, nu, rowIdentity⟩

end FanoTriples
