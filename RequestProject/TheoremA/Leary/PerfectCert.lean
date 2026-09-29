module

public import RequestProject.TheoremA.Leary.LongRelators

/-!
# Kernel-checkable perfection certificates for edge-path groups

* `isPerfect_presentedGroup_of_abelianization` — a presented group whose generators all die in the
  abelianization is perfect.
* `EdgeData.PerfCert` — a *symbolic propagation* certificate: every directed edge `a` gets a value
  `val a ∈ ℤ²` (its class in terms of two base edges), a rank and a justification (tree edge, base
  edge, reversal of a lower-ranked edge, or a triangle whose two other edges have lower rank and
  whose values sum to zero).  Two integer combinations `cert0`, `cert1` of triangle value-sums
  must equal the unit vectors.  All conditions are Boolean and are checked by kernel evaluation.
* `PerfCert.sound` — in any abelian group, a family satisfying the edge-path relations equals the
  symbolic values; `PerfCert.all_zero` — it vanishes identically.
* `PerfCert.isPerfect` — a valid certificate proves that `Π_L` is perfect.
-/

@[expose] public section

namespace TheoremA.Leary

open Subgroup

/-- A presented group whose generators all die in the abelianization is perfect. -/
theorem isPerfect_presentedGroup_of_abelianization {α : Type*} (rels : Set (FreeGroup α))
    (h : ∀ a, Abelianization.of (PresentedGroup.of a : PresentedGroup rels) = 1) :
    IsPerfectGroup (PresentedGroup rels) := by
  intro x _
  have hle : closure (Set.range (PresentedGroup.of (rels := rels))) ≤
      commutator (PresentedGroup rels) := by
    rw [closure_le]
    rintro _ ⟨a, rfl⟩
    rw [← Abelianization.ker_of]
    exact h a
  rw [PresentedGroup.closure_range_of, commutator_def] at hle
  exact hle trivial

namespace EdgeData

variable (D : EdgeData)

theorem piGrp_rel {r : FreeGroup (Fin D.m)} (hr : r ∈ D.piRels) :
    FreeGroup.lift (fun a => (PresentedGroup.of a : D.PiGrp)) r = 1 := by
  have hl : FreeGroup.lift (fun a => (PresentedGroup.of a : D.PiGrp)) =
      PresentedGroup.mk D.piRels := by ext i; rfl
  rw [hl]
  exact (QuotientGroup.eq_one_iff r).2 (subset_normalClosure hr)

theorem piGrp_mul_rev (a : Fin D.m) :
    (PresentedGroup.of a : D.PiGrp) * PresentedGroup.of (D.rev a) = 1 := by
  simpa using D.piGrp_rel (Or.inl (Or.inl ⟨a, rfl⟩))

theorem piGrp_tree {a : Fin D.m} (ha : a ∈ D.tree) : (PresentedGroup.of a : D.PiGrp) = 1 := by
  simpa using D.piGrp_rel (Or.inl (Or.inr ⟨a, ha, rfl⟩))

theorem piGrp_tri {t} (ht : t ∈ D.tri) :
    (PresentedGroup.of t.1 : D.PiGrp) * PresentedGroup.of t.2.1 * PresentedGroup.of t.2.2 = 1 := by
  simpa using D.piGrp_rel (Or.inr ⟨t, ht, rfl⟩)

/-- Symbolic-propagation perfection certificate. -/
structure PerfCert where
  val : Fin D.m → ℤ × ℤ
  rank : Fin D.m → ℕ
  just : Fin D.m → ℕ × ℕ × ℕ
  base0 : Fin D.m
  base1 : Fin D.m
  cert0 : List (ℕ × ℤ)
  cert1 : List (ℕ × ℤ)

variable {D}

namespace PerfCert

variable (C : PerfCert D)

/-- Sum of the values along a triangle. -/
def triSum (t : Fin D.m × Fin D.m × Fin D.m) : ℤ × ℤ := C.val t.1 + C.val t.2.1 + C.val t.2.2

/-- The `p`-th edge of a triangle is `a`, and the other two have lower rank. -/
def posOK (t : Fin D.m × Fin D.m × Fin D.m) (p : ℕ) (a : Fin D.m) : Bool :=
  if p = 0 then decide (t.1 = a) && decide (C.rank t.2.1 < C.rank a) &&
    decide (C.rank t.2.2 < C.rank a)
  else if p = 1 then decide (t.2.1 = a) && decide (C.rank t.1 < C.rank a) &&
    decide (C.rank t.2.2 < C.rank a)
  else decide (t.2.2 = a) && decide (C.rank t.1 < C.rank a) && decide (C.rank t.2.1 < C.rank a)

/-- Local validity of the justification of `a`. -/
def justOK (a : Fin D.m) : Bool :=
  if (C.just a).1 = 0 then decide (a ∈ D.tree) && decide (C.val a = 0)
  else if (C.just a).1 = 1 then
    (if (C.just a).2.1 = 0 then decide (a = C.base0) && decide (C.val a = (1, 0))
     else decide (a = C.base1) && decide (C.val a = (0, 1)))
  else if (C.just a).1 = 2 then
    decide (C.rank (D.rev a) < C.rank a) && decide (C.val a = -C.val (D.rev a))
  else match D.tri[(C.just a).2.1]? with
    | none => false
    | some t => decide (C.triSum t = 0) && C.posOK t (C.just a).2.2 a

/-- Value-sum of the `i`-th triangle (zero for an invalid index). -/
def relSum (i : ℕ) : ℤ × ℤ :=
  match D.tri[i]? with
  | none => 0
  | some t => C.triSum t

/-- Integer combination of triangle value-sums. -/
def combo (L : List (ℕ × ℤ)) : ℤ × ℤ := (L.map fun p => p.2 • C.relSum p.1).sum

/-- Global validity of the certificate. -/
def Valid : Prop :=
  (∀ a, C.justOK a = true) ∧ C.combo C.cert0 = (1, 0) ∧ C.combo C.cert1 = (0, 1)

instance : Decidable C.Valid := by unfold Valid; infer_instance

variable {C}
variable {V : Type*} [AddCommGroup V] (e : Fin D.m → V)

/-- Evaluation of a symbolic value. -/
def sv (x : ℤ × ℤ) : V := x.1 • e C.base0 + x.2 • e C.base1

theorem sound (hC : ∀ a, C.justOK a = true) (hr : ∀ a, e a + e (D.rev a) = 0)
    (htree : ∀ a ∈ D.tree, e a = 0) (htri : ∀ t ∈ D.tri, e t.1 + e t.2.1 + e t.2.2 = 0) :
    ∀ a, e a = (C.val a).1 • e C.base0 + (C.val a).2 • e C.base1 := by
  intro a
  induction hn : C.rank a using Nat.strong_induction_on generalizing a with
  | _ n ih =>
  have ih' : ∀ b, C.rank b < C.rank a →
      e b = (C.val b).1 • e C.base0 + (C.val b).2 • e C.base1 :=
    fun b hb => ih _ (hn ▸ hb) b rfl
  have h := hC a
  unfold justOK at h
  split_ifs at h with h0 h1 h10 h2
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [htree a h.1, h.2]; simp
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.2, h.1]; simp
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.2, h.1]; simp
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hv := h.2
    have i1 := ih' _ h.1
    have hra := hr a
    have c1 : (C.val a).1 = -(C.val (D.rev a)).1 := by rw [hv]; rfl
    have c2 : (C.val a).2 = -(C.val (D.rev a)).2 := by rw [hv]; rfl
    linear_combination (norm := module) hra - i1 - c1 • e C.base0 - c2 • e C.base1
  · revert h
    rcases ht : D.tri[(C.just a).2.1]? with _ | t
    · simp
    · intro h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hs, hp⟩ := h
      have htm : t ∈ D.tri := List.mem_of_getElem? ht
      have hsum := htri t htm
      have s1 : (C.val t.1).1 + (C.val t.2.1).1 + (C.val t.2.2).1 = 0 := by
        have := congrArg Prod.fst hs; simpa [triSum] using this
      have s2 : (C.val t.1).2 + (C.val t.2.1).2 + (C.val t.2.2).2 = 0 := by
        have := congrArg Prod.snd hs; simpa [triSum] using this
      unfold posOK at hp
      split_ifs at hp
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
        obtain ⟨⟨rfl, r2⟩, r3⟩ := hp
        have i2 := ih' _ r2; have i3 := ih' _ r3
        linear_combination (norm := module) hsum - i2 - i3 - s1 • e C.base0 - s2 • e C.base1
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
        obtain ⟨⟨rfl, r2⟩, r3⟩ := hp
        have i2 := ih' _ r2; have i3 := ih' _ r3
        linear_combination (norm := module) hsum - i2 - i3 - s1 • e C.base0 - s2 • e C.base1
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
        obtain ⟨⟨rfl, r2⟩, r3⟩ := hp
        have i2 := ih' _ r2; have i3 := ih' _ r3
        linear_combination (norm := module) hsum - i2 - i3 - s1 • e C.base0 - s2 • e C.base1

theorem sv_add (x y : ℤ × ℤ) : sv (C := C) e (x + y) = sv (C := C) e x + sv (C := C) e y := by
  simp only [sv, Prod.fst_add, Prod.snd_add, add_smul]; abel

theorem sv_smul (c : ℤ) (x : ℤ × ℤ) : sv (C := C) e (c • x) = c • sv (C := C) e x := by
  simp only [sv, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, smul_add]

theorem sv_zero : sv (C := C) e 0 = 0 := by simp [sv]

theorem sv_relSum (hC : ∀ a, C.justOK a = true) (hr : ∀ a, e a + e (D.rev a) = 0)
    (htree : ∀ a ∈ D.tree, e a = 0) (htri : ∀ t ∈ D.tri, e t.1 + e t.2.1 + e t.2.2 = 0)
    (i : ℕ) : sv (C := C) e (C.relSum i) = 0 := by
  unfold relSum
  rcases ht : D.tri[i]? with _ | t
  · exact sv_zero e
  · have htm : t ∈ D.tri := List.mem_of_getElem? ht
    have hs := sound e hC hr htree htri
    simp only [triSum, sv_add]
    unfold sv
    rw [← hs, ← hs, ← hs]
    exact htri t htm

theorem sv_combo (hC : ∀ a, C.justOK a = true) (hr : ∀ a, e a + e (D.rev a) = 0)
    (htree : ∀ a ∈ D.tree, e a = 0) (htri : ∀ t ∈ D.tri, e t.1 + e t.2.1 + e t.2.2 = 0)
    (L : List (ℕ × ℤ)) : sv (C := C) e (C.combo L) = 0 := by
  induction L with
  | nil => exact sv_zero e
  | cons p L ih =>
    simp only [combo, List.map_cons, List.sum_cons] at ih ⊢
    rw [sv_add, ih, sv_smul, sv_relSum e hC hr htree htri, smul_zero, add_zero]

/-- A valid certificate forces every edge value to vanish. -/
theorem all_zero (hC : C.Valid) (hr : ∀ a, e a + e (D.rev a) = 0)
    (htree : ∀ a ∈ D.tree, e a = 0) (htri : ∀ t ∈ D.tri, e t.1 + e t.2.1 + e t.2.2 = 0) :
    ∀ a, e a = 0 := by
  obtain ⟨h1, h2, h3⟩ := hC
  have g0 : e C.base0 = 0 := by
    have := sv_combo e h1 hr htree htri C.cert0
    rw [h2] at this; simpa [sv] using this
  have g1 : e C.base1 = 0 := by
    have := sv_combo e h1 hr htree htri C.cert1
    rw [h3] at this; simpa [sv] using this
  intro a
  rw [sound e h1 hr htree htri a, g0, g1]; simp

/-- **A valid certificate proves that the edge-path group is perfect.** -/
theorem isPerfect (hC : C.Valid) : IsPerfectGroup D.PiGrp := by
  apply isPerfect_presentedGroup_of_abelianization
  let e : Fin D.m → Additive (Abelianization D.PiGrp) := fun i =>
    Additive.ofMul (Abelianization.of (PresentedGroup.of i : D.PiGrp))
  have hr : ∀ a, e a + e (D.rev a) = 0 := fun a => by
    simp only [e, ← ofMul_mul, ← map_mul]
    rw [D.piGrp_mul_rev a]; rfl
  have htree : ∀ a ∈ D.tree, e a = 0 := fun a ha => by
    simp only [e]; rw [D.piGrp_tree ha]; rfl
  have htri : ∀ t ∈ D.tri, e t.1 + e t.2.1 + e t.2.2 = 0 := fun t h => by
    simp only [e, ← ofMul_mul, ← map_mul]
    rw [D.piGrp_tri h]; rfl
  intro a
  exact all_zero e hC hr htree htri a

end PerfCert

end EdgeData

end TheoremA.Leary
