module

public import Mathlib

/-!
# A column (heap) model of right-angled Artin group elements

Let `adj` be a symmetric, irreflexive relation on `Fin N` (the edges of a graph `Γ`).  A letter is
a pair `(v, ε)` (the generator `v` or its inverse).  A *column* is an index pair `(a, b)` with
`a = b` or `a, b` non-adjacent; the letter `v` *lives* in the columns containing `v`.  A tuple of
lists (one stack per column) is the projection `proj w` of a word `w`.

* `step x` — left multiplication by the letter `x`: if every column of `x` has top `x⁻¹` the tops are
  removed, otherwise `x` is pushed onto every column of `x`.
* `IsPos` — tuples that are projections of *reduced* words (no cancellable pair `x … x⁻¹` whose
  intermediate letters all commute with `x`).
* `step_inv_step` — on `IsPos`, `step x⁻¹ ∘ step x = id`; `step_comm` — letters of adjacent vertices
  act on disjoint columns, so their steps commute (on all tuples).
* `gen v : Equiv.Perm (Pos adj)` — the resulting action of the generators.

No normal form theorem is needed: only these two facts are used, together with the
*last-letter set* `Ivert p` (vertices `s` such that every column of `s` ends with the same letter
of `s`) and the `K`-stripped tuple `rest K p`.
-/

@[expose] public section

namespace TheoremA.Leary.Heap

open Classical

variable {N : ℕ}

/-- A letter: a vertex and a sign (`true` = positive). -/
abbrev Letter (N : ℕ) := Fin N × Bool

/-- The inverse letter. -/
def Letter.inv (x : Letter N) : Letter N := (x.1, !x.2)

@[simp] theorem Letter.inv_fst (x : Letter N) : x.inv.1 = x.1 := rfl

@[simp] theorem Letter.inv_inv (x : Letter N) : x.inv.inv = x := by
  simp [Letter.inv]

theorem Letter.inv_ne (x : Letter N) : x.inv ≠ x := by
  intro h
  have := congrArg Prod.snd h
  simp [Letter.inv] at this

/-- Tuples of stacks indexed by (ordered) vertex pairs. -/
abbrev Tup (N : ℕ) := Fin N → Fin N → List (Letter N)

variable (adj : Fin N → Fin N → Prop)

/-- Symmetric irreflexive relation. -/
structure IsGraph : Prop where
  symm : ∀ a b, adj a b → adj b a
  irrefl : ∀ a, ¬ adj a a

/-- A column index. -/
def Valid (a b : Fin N) : Prop := a = b ∨ ¬ adj a b

/-- The letters of `s` live in the column `(a, b)`. -/
def InCol (s a b : Fin N) : Prop := (a = s ∨ b = s) ∧ Valid adj a b

/-- The projection of a word to the columns. -/
noncomputable def proj (w : List (Letter N)) : Tup N := fun a b =>
  if Valid adj a b then w.filter (fun x => decide (x.1 = a ∨ x.1 = b)) else []

/-- Push `x` onto the columns of `x`. -/
noncomputable def push (x : Letter N) (p : Tup N) : Tup N := fun a b =>
  if InCol adj x.1 a b then x :: p a b else p a b

/-- Pop the columns of `x`. -/
noncomputable def pop (x : Letter N) (p : Tup N) : Tup N := fun a b =>
  if InCol adj x.1 a b then (p a b).tail else p a b

/-- Every column of `x` has top `x⁻¹`. -/
def CanPop (x : Letter N) (p : Tup N) : Prop := ∀ a b, InCol adj x.1 a b → (p a b).head? = some x.inv

/-- Left multiplication by a letter. -/
noncomputable def step (x : Letter N) (p : Tup N) : Tup N :=
  if CanPop adj x p then pop adj x p else push adj x p

/-- A cancellable pair `x … x⁻¹` whose intermediate letters commute with `x`. -/
def Cancellable (w : List (Letter N)) : Prop :=
  ∃ B x A₁ A₂, w = B ++ x :: (A₁ ++ x.inv :: A₂) ∧ ∀ y ∈ A₁, adj x.1 y.1

/-- Reduced words. -/
def Reduced (w : List (Letter N)) : Prop := ¬ Cancellable adj w

/-- Projections of reduced words. -/
def IsPos (p : Tup N) : Prop := ∃ w, Reduced adj w ∧ proj adj w = p

variable {adj}

theorem inCol_self (s : Fin N) : InCol adj s s s := ⟨Or.inl rfl, Or.inl rfl⟩

theorem inCol_disjoint (hG : IsGraph adj) {u v a b : Fin N} (huv : adj u v)
    (hu : InCol adj u a b) (hv : InCol adj v a b) : False := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, -⟩ := hv
  have hne : u ≠ v := fun h => hG.irrefl u (h ▸ huv)
  rcases hu2 with hab | hab
  · subst hab
    apply hne
    rcases hu1 with h | h <;> rcases hv1 with h' | h' <;> exact h.symm.trans h'
  · rcases hu1 with h1 | h1 <;> rcases hv1 with h2 | h2
    · exact hne (h1.symm.trans h2)
    · subst h1; subst h2; exact hab huv
    · subst h1; subst h2; exact hab (hG.symm _ _ huv)
    · exact hne (h1.symm.trans h2)

/-- Letters of vertices adjacent to `s` do not occur in the columns of `s`. -/
theorem filter_eq_nil_of_adj (hG : IsGraph adj) {B : List (Letter N)} {s a b : Fin N}
    (hc : InCol adj s a b) (hB : ∀ y ∈ B, adj s y.1) :
    B.filter (fun y => decide (y.1 = a ∨ y.1 = b)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro y hy
  have h := hB y hy
  obtain ⟨h1, h2⟩ := hc
  simp only [decide_eq_true_eq, not_or]
  constructor
  · rintro rfl
    rcases h1 with rfl | rfl
    · exact hG.irrefl _ h
    · rcases h2 with rfl | h2
      · exact hG.irrefl _ h
      · exact h2 (hG.symm _ _ h)
  · rintro rfl
    rcases h1 with rfl | rfl
    · rcases h2 with rfl | h2
      · exact hG.irrefl _ h
      · exact h2 h
    · exact hG.irrefl _ h

theorem proj_cons (x : Letter N) (w : List (Letter N)) :
    proj adj (x :: w) = push adj x (proj adj w) := by
  funext a b
  simp only [proj, push, InCol]
  by_cases hv : Valid adj a b
  · simp only [hv, if_true, and_true, List.filter_cons]
    by_cases h : x.1 = a ∨ x.1 = b
    · have h' : a = x.1 ∨ b = x.1 := h.imp Eq.symm Eq.symm
      simp [h, h']
    · have h' : ¬ (a = x.1 ∨ b = x.1) := fun h' => h (h'.imp Eq.symm Eq.symm)
      simp [h, h']
  · simp [hv]

theorem proj_nil : proj adj ([] : List (Letter N)) = fun _ _ => [] := by
  funext a b; simp [proj]

theorem canPop_proj_of (hG : IsGraph adj) {x : Letter N} {B A : List (Letter N)}
    (hB : ∀ y ∈ B, adj x.1 y.1) : CanPop adj x (proj adj (B ++ x.inv :: A)) := by
  intro a b hc
  have hv := hc.2
  simp only [proj, hv, if_true, List.filter_append, filter_eq_nil_of_adj hG hc hB, List.nil_append,
    List.filter_cons]
  have : (x.1 = a ∨ x.1 = b) := hc.1.imp Eq.symm Eq.symm
  simp [this, Letter.inv]

theorem push_eq_of_not {x : Letter N} {p : Tup N} {a b : Fin N} (h : ¬ InCol adj x.1 a b) :
    push adj x p a b = p a b := by simp [push, h]

theorem pop_eq_of_not {x : Letter N} {p : Tup N} {a b : Fin N} (h : ¬ InCol adj x.1 a b) :
    pop adj x p a b = p a b := by simp [pop, h]

theorem step_eq_of_not {x : Letter N} {p : Tup N} {a b : Fin N} (h : ¬ InCol adj x.1 a b) :
    step adj x p a b = p a b := by
  unfold step; split_ifs
  · exact pop_eq_of_not h
  · exact push_eq_of_not h

/-- Decomposition when all columns of `x` have top `x⁻¹`. -/
theorem exists_split_of_canPop (hG : IsGraph adj) {x : Letter N} :
    ∀ {w : List (Letter N)}, CanPop adj x (proj adj w) →
      ∃ B A, w = B ++ x.inv :: A ∧ ∀ y ∈ B, adj x.1 y.1
  | [], h => by
    have := h x.1 x.1 (inCol_self _)
    simp [proj, Valid] at this
  | y :: w, h => by
    by_cases hy : y = x.inv
    · exact ⟨[], w, by simp [hy], by simp⟩
    by_cases hx : y.1 = x.1
    · exfalso
      have := h x.1 x.1 (inCol_self _)
      simp only [proj, Valid, true_or, if_true, List.filter_cons, hx, or_self, decide_true,
        List.head?_cons, Option.some.injEq] at this
      exact hy this
    by_cases hadj : adj x.1 y.1
    · have h' : CanPop adj x (proj adj w) := by
        intro a b hc
        have := h a b hc
        rw [proj_cons] at this
        have hn : ¬ InCol adj y.1 a b := fun hy' => inCol_disjoint hG hadj hc hy'
        rwa [push_eq_of_not hn] at this
      obtain ⟨B, A, rfl, hB⟩ := exists_split_of_canPop hG h'
      refine ⟨y :: B, A, rfl, ?_⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hadj
      · exact hB z hz
    · exfalso
      have hc : InCol adj x.1 x.1 y.1 := ⟨Or.inl rfl, Or.inr hadj⟩
      have := h x.1 y.1 hc
      simp only [proj, hc.2, if_true, List.filter_cons, or_true, decide_true,
        List.head?_cons, Option.some.injEq] at this
      exact hy this

theorem pop_proj (hG : IsGraph adj) {x : Letter N} {B A : List (Letter N)}
    (hB : ∀ y ∈ B, adj x.1 y.1) : pop adj x (proj adj (B ++ x.inv :: A)) = proj adj (B ++ A) := by
  funext a b
  by_cases hc : InCol adj x.1 a b
  · have hv := hc.2
    simp only [pop, hc, if_true, proj, hv, List.filter_append, filter_eq_nil_of_adj hG hc hB,
      List.nil_append, List.filter_cons]
    have : (x.1 = a ∨ x.1 = b) := hc.1.imp Eq.symm Eq.symm
    simp [this, Letter.inv]
  · rw [pop_eq_of_not hc]
    simp only [proj]
    split_ifs with hv
    · simp only [List.filter_append, List.filter_cons]
      have h1 : ¬ x.1 = a := fun h => hc ⟨Or.inl h.symm, hv⟩
      have h2 : ¬ x.1 = b := fun h => hc ⟨Or.inr h.symm, hv⟩
      simp [h1, h2, Letter.inv]
    · rfl

theorem proj_cons_comm (hG : IsGraph adj) {x : Letter N} {B A : List (Letter N)}
    (hB : ∀ y ∈ B, adj x.1 y.1) : proj adj (x :: (B ++ A)) = proj adj (B ++ x :: A) := by
  funext a b
  simp only [proj]
  split_ifs with hv
  · by_cases hc : InCol adj x.1 a b
    · simp only [List.filter_cons, List.filter_append, filter_eq_nil_of_adj hG hc hB,
        List.nil_append]
    · have : ¬ (x.1 = a ∨ x.1 = b) := by
        rintro (h | h) <;> exact hc ⟨by simp_all, hv⟩
      simp [List.filter_append, this]
  · rfl

/-! ### Reducedness -/

theorem cancellable_cons {w : List (Letter N)} (b : Letter N) (h : Cancellable adj w) :
    Cancellable adj (b :: w) := by
  obtain ⟨B, x, A₁, A₂, rfl, h⟩ := h
  exact ⟨b :: B, x, A₁, A₂, by simp, h⟩

theorem reduced_cons (hG : IsGraph adj) {x : Letter N} {w : List (Letter N)}
    (hw : Reduced adj w) (hx : ¬ CanPop adj x (proj adj w)) : Reduced adj (x :: w) := by
  rintro ⟨B, y, A₁, A₂, hB, hA⟩
  rcases B with _ | ⟨b, B⟩
  · simp only [List.nil_append, List.cons.injEq] at hB
    obtain ⟨rfl, rfl⟩ := hB
    exact hx (canPop_proj_of hG hA)
  · simp only [List.cons_append, List.cons.injEq] at hB
    obtain ⟨rfl, rfl⟩ := hB
    exact hw ⟨B, y, A₁, A₂, rfl, hA⟩

theorem cancellable_insert (hG : IsGraph adj) (z : Letter N) :
    ∀ {B A : List (Letter N)}, (∀ y ∈ B, adj z.1 y.1) → Cancellable adj (B ++ A) →
      Cancellable adj (B ++ z :: A)
  | [], A, _, h => by
    simpa using cancellable_cons z h
  | b :: B, A, hB, h => by
    obtain ⟨B0, y, A₁, A₂, hw, hA⟩ := h
    rcases B0 with _ | ⟨b', B0⟩
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hw
      obtain ⟨hby, hw⟩ := hw
      subst hby
      have hzb : adj b.1 z.1 := hG.symm _ _ (hB b (by simp))
      rcases List.append_eq_append_iff.1 hw with ⟨a', rfl, rfl⟩ | ⟨c', rfl, hc⟩
      · refine ⟨[], b, B ++ z :: a', A₂, by simp, ?_⟩
        intro u hu
        simp only [List.mem_append, List.mem_cons] at hu
        rcases hu with hu | rfl | hu
        · exact hA u (by simp [hu])
        · exact hzb
        · exact hA u (by simp [hu])
      · rcases c' with _ | ⟨d, c'⟩
        · simp only [List.nil_append] at hc
          subst hc
          refine ⟨[], b, A₁ ++ [z], A₂, by simp, ?_⟩
          intro u hu
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with hu | rfl
          · exact hA u hu
          · exact hzb
        · simp only [List.cons_append, List.cons.injEq] at hc
          obtain ⟨hd, hc⟩ := hc
          subst hd; subst hc
          exact ⟨[], b, A₁, c' ++ z :: A, by simp, hA⟩
    · simp only [List.cons_append, List.cons.injEq] at hw
      obtain ⟨hbb, hw⟩ := hw
      have := cancellable_insert hG z (fun y hy => hB y (by simp [hy])) ⟨B0, y, A₁, A₂, hw, hA⟩
      simpa using cancellable_cons b this

theorem reduced_erase (hG : IsGraph adj) {x : Letter N} {B A : List (Letter N)}
    (hB : ∀ y ∈ B, adj x.1 y.1) (hw : Reduced adj (B ++ x.inv :: A)) : Reduced adj (B ++ A) :=
  fun h => hw (cancellable_insert hG x.inv (by simpa using hB) h)

theorem not_canPop_after_pop (hG : IsGraph adj) {x : Letter N} {B A : List (Letter N)}
    (hB : ∀ y ∈ B, adj x.1 y.1) (hw : Reduced adj (B ++ x.inv :: A)) :
    ¬ CanPop adj x.inv (proj adj (B ++ A)) := by
  intro h
  obtain ⟨B', A', hs, hB'⟩ := exists_split_of_canPop hG h
  simp only [Letter.inv_inv, Letter.inv_fst] at hs hB'
  rcases List.append_eq_append_iff.1 hs with ⟨a', rfl, rfl⟩ | ⟨c', rfl, hc⟩
  · exact hw ⟨B, x.inv, a', A', by simp, fun y hy => by simpa using hB' y (by simp [hy])⟩
  · rcases c' with _ | ⟨d, c'⟩
    · simp only [List.nil_append] at hc
      subst hc
      exact hw ⟨B', x.inv, [], A', by simp, by simp⟩
    · simp only [List.cons_append, List.cons.injEq] at hc
      obtain ⟨hd, -⟩ := hc
      subst hd
      exact hG.irrefl _ (hB _ (by simp))

/-! ### The action -/

theorem isPos_step (hG : IsGraph adj) (x : Letter N) {p : Tup N} (hp : IsPos adj p) :
    IsPos adj (step adj x p) := by
  obtain ⟨w, hw, rfl⟩ := hp
  unfold step
  split_ifs with h
  · obtain ⟨B, A, rfl, hB⟩ := exists_split_of_canPop hG h
    exact ⟨B ++ A, reduced_erase hG hB hw, (pop_proj hG hB).symm⟩
  · exact ⟨x :: w, reduced_cons hG hw h, proj_cons x w⟩

theorem step_inv_step (hG : IsGraph adj) (x : Letter N) {p : Tup N} (hp : IsPos adj p) :
    step adj x.inv (step adj x p) = p := by
  by_cases h : CanPop adj x p
  · obtain ⟨w, hw, rfl⟩ := hp
    obtain ⟨B, A, rfl, hB⟩ := exists_split_of_canPop hG h
    have e1 : step adj x (proj adj (B ++ x.inv :: A)) = proj adj (B ++ A) := by
      rw [step, if_pos h, pop_proj hG hB]
    rw [e1, step, if_neg (not_canPop_after_pop hG hB hw), ← proj_cons,
      proj_cons_comm hG (by simpa using hB)]
  · have hpush : step adj x p = push adj x p := by rw [step, if_neg h]
    have hc : CanPop adj x.inv (push adj x p) := by
      intro a b hc
      simp only [Letter.inv_fst] at hc
      simp [push, hc]
    rw [hpush, step, if_pos hc]
    funext a b
    by_cases hc' : InCol adj x.1 a b
    · simp [pop, push, hc']
    · simp [pop, push, hc']

theorem step_comm (hG : IsGraph adj) {x y : Letter N} (hxy : adj x.1 y.1) (p : Tup N) :
    step adj x (step adj y p) = step adj y (step adj x p) := by
  have hx : ∀ q : Tup N, CanPop adj x (step adj y q) ↔ CanPop adj x q := by
    intro q
    refine forall_congr' fun a => forall_congr' fun b => imp_congr_right fun hc => ?_
    rw [step_eq_of_not (fun hy => inCol_disjoint hG hxy hc hy)]
  have hy : ∀ q : Tup N, CanPop adj y (step adj x q) ↔ CanPop adj y q := by
    intro q
    refine forall_congr' fun a => forall_congr' fun b => imp_congr_right fun hc => ?_
    rw [step_eq_of_not (fun hx' => inCol_disjoint hG hxy hx' hc)]
  funext a b
  by_cases hca : InCol adj x.1 a b
  · have hnb : ¬ InCol adj y.1 a b := fun h => inCol_disjoint hG hxy hca h
    rw [step_eq_of_not hnb]
    conv_lhs => rw [step]
    conv_rhs => rw [step]
    rw [hx p]
    split_ifs <;> simp [pop, push, hca, step_eq_of_not hnb]
  · rw [step_eq_of_not hca]
    by_cases hcb : InCol adj y.1 a b
    · conv_lhs => rw [step]
      conv_rhs => rw [step]
      rw [hy p]
      split_ifs <;> simp [pop, push, hcb, step_eq_of_not hca]
    · rw [step_eq_of_not hcb, step_eq_of_not hcb, step_eq_of_not hca]


/-! ### Positions and generators -/

variable (adj) in
/-- Positions: projections of reduced words. -/
def Pos := {p : Tup N // IsPos adj p}

theorem reduced_nil : Reduced adj ([] : List (Letter N)) := by
  rintro ⟨B, x, A₁, A₂, h, -⟩
  simp at h

variable (adj) in
/-- The empty position (the identity element). -/
noncomputable def emptyPos : Pos adj := ⟨proj adj [], [], reduced_nil, rfl⟩

/-- The generator `v`, acting by left multiplication. -/
noncomputable def gen (hG : IsGraph adj) (v : Fin N) : Equiv.Perm (Pos adj) where
  toFun p := ⟨step adj (v, true) p.1, isPos_step hG _ p.2⟩
  invFun p := ⟨step adj (v, false) p.1, isPos_step hG _ p.2⟩
  left_inv p := Subtype.ext (step_inv_step hG (v, true) p.2)
  right_inv p := Subtype.ext (step_inv_step hG (v, false) p.2)

theorem gen_apply (hG : IsGraph adj) (v : Fin N) (p : Pos adj) :
    (gen hG v p).1 = step adj (v, true) p.1 := rfl

theorem gen_inv_apply (hG : IsGraph adj) (v : Fin N) (p : Pos adj) :
    ((gen hG v)⁻¹ p).1 = step adj (v, false) p.1 := rfl

theorem gen_commute (hG : IsGraph adj) {u v : Fin N} (h : adj u v) :
    Commute (gen hG u) (gen hG v) := by
  refine Equiv.ext fun p => Subtype.ext ?_
  show step adj (u, true) (step adj (v, true) p.1) = step adj (v, true) (step adj (u, true) p.1)
  exact step_comm hG (x := (u, true)) (y := (v, true)) h p.1

/-! ### Last letters and `K`-stripped columns -/

variable (adj) in
/-- The vertices `s` such that every column of `s` ends with one and the same letter of `s`. -/
def Ivert (p : Tup N) : Set (Fin N) :=
  {s | ∃ e : Bool, ∀ a b, InCol adj s a b → (p a b).getLast? = some (s, e)}

/-- Strip from every column the maximal top segment of letters of vertices in `K`. -/
noncomputable def rest (K : Finset (Fin N)) (p : Tup N) : Tup N := fun a b =>
  (p a b).dropWhile (fun x => decide (x.1 ∈ K))

theorem rest_step {K : Finset (Fin N)} {x : Letter N} (hx : x.1 ∈ K) (p : Tup N) :
    rest K (step adj x p) = rest K p := by
  funext a b
  by_cases hc : InCol adj x.1 a b
  · unfold step
    split_ifs with hp
    · have hh := hp a b hc
      simp only [rest, pop, hc, if_true]
      rcases hq : p a b with _ | ⟨y, t⟩
      · rw [hq] at hh; simp at hh
      · rw [hq] at hh
        simp only [List.head?_cons, Option.some.injEq] at hh
        subst hh
        simp [hx]
    · simp [rest, push, hc, hx]
  · simp only [rest, step_eq_of_not hc]

variable (adj) in
/-- The subgroup of permutations preserving `rest K`. -/
noncomputable def restSub (K : Finset (Fin N)) : Subgroup (Equiv.Perm (Pos adj)) where
  carrier := {g | ∀ p, rest K (g p).1 = rest K p.1}
  one_mem' := fun p => rfl
  mul_mem' := by
    intro g h hg hh p
    change rest K (g (h p)).1 = _
    rw [hg, hh]
  inv_mem' := by
    intro g hg p
    simpa using (hg (g⁻¹ p)).symm

theorem closure_le_restSub (hG : IsGraph adj) (K : Finset (Fin N)) :
    Subgroup.closure (gen hG '' (K : Set (Fin N))) ≤ restSub adj K := by
  rw [Subgroup.closure_le]
  rintro _ ⟨v, hv, rfl⟩ p
  exact rest_step (x := (v, true)) hv p.1

theorem rest_of_mem_closure (hG : IsGraph adj) {K : Finset (Fin N)} {g : Equiv.Perm (Pos adj)}
    (hg : g ∈ Subgroup.closure (gen hG '' (K : Set (Fin N)))) (p : Pos adj) :
    rest K (g p).1 = rest K p.1 :=
  closure_le_restSub hG K hg p

theorem getLast?_dropWhile_of {P : Letter N → Bool} :
    ∀ {l : List (Letter N)} {y : Letter N}, l.getLast? = some y → P y = false →
      (l.dropWhile P).getLast? = some y
  | [], y, h, _ => by simp at h
  | x :: l, y, h, hy => by
    rw [List.dropWhile_cons]
    split_ifs with hx
    · rcases l with _ | ⟨z, l⟩
      · simp only [List.getLast?_singleton, Option.some.injEq] at h
        subst h; simp_all
      · exact getLast?_dropWhile_of (by simpa [List.getLast?_cons] using h) hy
    · exact h

theorem getLast?_of_dropWhile {P : Letter N → Bool} :
    ∀ {l : List (Letter N)} {y : Letter N}, (l.dropWhile P).getLast? = some y → l.getLast? = some y
  | [], y, h => by simp at h
  | x :: l, y, h => by
    rw [List.dropWhile_cons] at h
    split_ifs at h with hx
    · have := getLast?_of_dropWhile h
      rcases l with _ | ⟨z, l⟩
      · simp at this
      · simpa [List.getLast?_cons] using this
    · exact h

/-- **Clique lemma.**  If `rest K p = rest K q` and `K` is a clique, then last-letter vertices of `p`
and of `q` are equal or adjacent. -/
theorem ivert_adj_of_rest_eq {K : Finset (Fin N)} (hK : ∀ u ∈ K, ∀ v ∈ K, u = v ∨ adj u v)
    {p q : Tup N} (h : rest K p = rest K q) {s t : Fin N} (hs : s ∈ Ivert adj p)
    (ht : t ∈ Ivert adj q) : s = t ∨ adj s t := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hne, hna⟩ := hcon
  have c1 : InCol adj s s t := ⟨Or.inl rfl, Or.inr hna⟩
  have c2 : InCol adj t s t := ⟨Or.inr rfl, Or.inr hna⟩
  obtain ⟨e, hs⟩ := hs
  obtain ⟨e', ht⟩ := ht
  have hs' := hs s t c1
  have ht' := ht s t c2
  by_cases hsK : s ∈ K
  · by_cases htK : t ∈ K
    · rcases hK s hsK t htK with h' | h'
      · exact hne h'
      · exact hna h'
    · have h1 : (rest K q s t).getLast? = some (t, e') :=
        getLast?_dropWhile_of ht' (by simp [htK])
      rw [← h] at h1
      have h2 := getLast?_of_dropWhile h1
      rw [hs'] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      exact hne h2.1
  · have h1 : (rest K p s t).getLast? = some (s, e) :=
      getLast?_dropWhile_of hs' (by simp [hsK])
    rw [h] at h1
    have h2 := getLast?_of_dropWhile h1
    rw [ht'] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact hne h2.1.symm

/-- If all columns of `p` consist of letters of `v`, then `Ivert p ⊆ {v}`. -/
theorem ivert_subset_of_rest_nil {v : Fin N} {p : Tup N}
    (h : rest {v} p = fun _ _ => []) {s : Fin N} (hs : s ∈ Ivert adj p) : s = v := by
  obtain ⟨e, hs⟩ := hs
  have h1 := hs s s (inCol_self s)
  have h2 := congrFun (congrFun h s) s
  simp only [rest, List.dropWhile_eq_nil_iff, decide_eq_true_eq, Finset.mem_singleton] at h2
  have hm : (s, e) ∈ p s s := List.mem_of_getLast? h1
  exact h2 _ hm

theorem rest_proj_nil (K : Finset (Fin N)) : rest K (proj adj []) = fun _ _ => [] := by
  funext a b; simp [rest, proj]

/-! ### Heights -/

/-- The sign of a letter. -/
def sgn (x : Letter N) : ℤ := if x.2 then 1 else -1

/-- The exponent sum of a column. -/
def colSum (l : List (Letter N)) : ℤ := (l.map sgn).sum

/-- The height: total exponent sum, read off the diagonal columns. -/
noncomputable def height (p : Tup N) : ℤ := ∑ s : Fin N, colSum (p s s)

theorem height_step (x : Letter N) (p : Tup N) : height (step adj x p) = height p + sgn x := by
  have key : ∀ s, colSum (step adj x p s s) = colSum (p s s) + if s = x.1 then sgn x else 0 := by
    intro s
    by_cases hs : s = x.1
    · subst hs
      have hc := inCol_self (adj := adj) x.1
      simp only [if_true]
      unfold step
      split_ifs with hp
      · have hh := hp x.1 x.1 hc
        simp only [pop, hc, if_true]
        rcases hq : p x.1 x.1 with _ | ⟨y, t⟩
        · rw [hq] at hh; simp at hh
        · rw [hq] at hh
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst hh
          cases hx : x.2 <;> simp [colSum, sgn, Letter.inv, hx]
      · simp [push, hc, colSum]
        ring
    · have hc : ¬ InCol adj x.1 s s := by
        rintro ⟨h1, -⟩; rcases h1 with h1 | h1 <;> exact hs h1
      simp [step_eq_of_not hc, hs]
  simp only [height, key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem height_proj_nil : height (proj adj ([] : List (Letter N))) = 0 := by
  simp [height, proj, colSum]

theorem height_gen (hG : IsGraph adj) (v : Fin N) (p : Pos adj) :
    height (gen hG v p).1 = height p.1 + 1 := by
  rw [gen_apply, height_step]; rfl

theorem height_gen_inv (hG : IsGraph adj) (v : Fin N) (p : Pos adj) :
    height ((gen hG v)⁻¹ p).1 = height p.1 - 1 := by
  rw [gen_inv_apply, height_step]; simp [sgn]; ring

theorem height_gen_zpow (hG : IsGraph adj) (v : Fin N) (k : ℤ) (p : Pos adj) :
    height ((gen hG v ^ k) p).1 = height p.1 + k := by
  induction k using Int.induction_on generalizing p with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih, height_gen]; ring
  | pred k ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih, height_gen_inv]; ring

/-- A position of nonzero height has a last letter. -/
theorem ivert_nonempty {p : Tup N} (hp : IsPos adj p) (hh : height p ≠ 0) :
    (Ivert adj p).Nonempty := by
  obtain ⟨w, -, rfl⟩ := hp
  rcases List.eq_nil_or_concat w with rfl | ⟨w', y, rfl⟩
  · exact absurd height_proj_nil hh
  refine ⟨y.1, y.2, fun a b hc => ?_⟩
  have hv := hc.2
  have hy : (y.1 = a ∨ y.1 = b) := hc.1.imp Eq.symm Eq.symm
  simp [proj, hv, List.filter_append, hy]

end TheoremA.Leary.Heap
