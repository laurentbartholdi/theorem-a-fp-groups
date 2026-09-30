module

public import RequestProject.TheoremA.Lemma31.Picture.Minimal

/-!
# Erasing darts from a permutation

For a permutation `π` of darts and a dart `a`, `erasePt π a` is the permutation obtained by
**removing `a` from its cycle**: `a` becomes a fixed point, and the dart that used to go to `a`
now goes to `π a` (first return).  It is `π * swap a (π⁻¹ a)`, i.e. `swap (π a) a * π`.
`erase2 π a b` removes two darts in turn.

On the retained darts (`x ≠ a, b`), `erase2 π a b` is the first-return map of `π` to the
complement of `{a, b}` (`erase2_apply_*`, `erase2_firstReturn`), and it fixes `a` and `b`, so it
restricts to a permutation of the retained darts.  Its cycles are the old cycles with `a, b`
omitted; a cycle wholly contained in `{a, b}` disappears:

* `numOrbits_erasePt`, `numOrbits_erase2_restrict` : the cycle count of the restriction to the
  retained darts is the old count minus the number of old cycles contained in `{a, b}`;
* `sameCycle_erasePt_iff`, `sameCycle_erase2_iff` : retained darts are in the same new cycle iff
  they were in the same old cycle;
* `cycleWord_erasePt`, `cycleWord_erase2` : the cycle word of a retained dart is the old cycle word
  with the removed darts omitted (stated for labels that are `1` on the removed darts, the words
  being otherwise identical).

Some general facts about cycle words are also proved here: changing the first letter
(`cycleWord_update_first`), merging two consecutive letters (`cycleWord_merge_consecutive`).
-/

@[expose] public section

namespace TheoremA.Picture

open Equiv Function

section Erase

variable {D : Type*} [DecidableEq D]

/-- Remove the dart `a` from its cycle of `π`: `a` becomes a fixed point, and the dart that went
to `a` now goes to `π a`. -/
def erasePt (π : Perm D) (a : D) : Perm D := π * swap a (π⁻¹ a)

variable {π : Perm D} {a b x y : D}

theorem erasePt_eq_swap_mul (π : Perm D) (a : D) : erasePt π a = swap (π a) a * π := by
  unfold erasePt
  rw [mul_swap_eq_swap_mul]; simp

@[simp] theorem erasePt_apply_self : erasePt π a a = a := by
  simp [erasePt]

theorem erasePt_apply_of_ne (hx : x ≠ a) (hπx : π x ≠ a) : erasePt π a x = π x := by
  unfold erasePt
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hx]
  intro h
  exact hπx (by rw [h]; simp)

theorem erasePt_apply_of_eq (hπx : π x = a) : erasePt π a x = π a := by
  unfold erasePt
  have : x = π⁻¹ a := by rw [← hπx]; simp
  rw [Perm.mul_apply, this, swap_apply_right]

theorem erasePt_of_fixed (h : π a = a) : erasePt π a = π := by
  have : π⁻¹ a = a := by rw [Perm.inv_eq_iff_eq, h]
  simp [erasePt, this, ← Perm.one_def]

theorem erasePt_apply_ne (hx : x ≠ a) : erasePt π a x ≠ a := by
  intro h
  exact hx ((erasePt π a).injective (h.trans erasePt_apply_self.symm))

/-- A fixed point other than `a` stays fixed. -/
theorem erasePt_apply_of_fixed (hy : π y = y) (hya : y ≠ a) : erasePt π a y = y := by
  rw [erasePt_apply_of_ne hya (by rwa [hy])]; exact hy

omit [DecidableEq D] in
theorem not_sameCycle_apply_of_not {π : Perm D} {a x : D} (h : ¬ π.SameCycle a x) :
    ¬ π.SameCycle a (π x) := fun h' => h (h'.trans ⟨-1, by simp⟩)

/-- Away from the cycle of `a`, erasing `a` changes nothing. -/
theorem erasePt_pow_apply_of_not_sameCycle (h : ¬ π.SameCycle a x) (n : ℕ) :
    (erasePt π a ^ n) x = (π ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply]
    have h1 : (π ^ n) x ≠ a := fun e =>
      h (e ▸ Perm.sameCycle_pow_left.2 (Perm.SameCycle.refl _ _))
    have h2 : π ((π ^ n) x) ≠ a := fun e =>
      h (e ▸ Perm.sameCycle_apply_left.2 (Perm.sameCycle_pow_left.2 (Perm.SameCycle.refl _ _)))
    exact erasePt_apply_of_ne h1 h2

theorem numOrbits_erasePt [Finite D] (h : π a ≠ a) :
    numOrbits (erasePt π a) = numOrbits π + 1 := by
  rw [erasePt_eq_swap_mul]
  exact numOrbits_swap_mul_split h ⟨-1, by simp⟩

/-- Retained darts are in the same cycle after erasing `a` iff they were before. -/
theorem sameCycle_erasePt_iff [Finite D] (hx : x ≠ a) (hy : y ≠ a) :
    (erasePt π a).SameCycle x y ↔ π.SameCycle x y := by
  by_cases h : π a = a
  · rw [erasePt_of_fixed h]
  have hfix : ∀ z, (erasePt π a).SameCycle a z → z = a := by
    intro z hz
    obtain ⟨n, rfl⟩ := hz.exists_nat_pow_eq
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Perm.mul_apply, ih ⟨n, rfl⟩, erasePt_apply_self]
  have key := sameCycle_swap_mul_split_iff (π := π) (x := x) (y := y) h ⟨-1, by simp⟩
  rw [← erasePt_eq_swap_mul] at key
  rw [key]
  constructor
  · exact Or.inl
  · rintro (h1 | ⟨h1, h2⟩)
    · exact h1
    · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact h1.symm.trans h2
      · exact absurd (hfix y h2) hy
      · exact absurd (hfix x h1) hx
      · exact absurd (hfix x h1) hx

/-- **Word after erasing a dart with trivial label**: for a retained dart, the cycle word is
unchanged (the erased letter was `1`). -/
theorem cycleWord_erasePt {G : Type*} [Group G] [Finite D] (f : D → G) (hx : x ≠ a)
    (hf : f a = 1) : cycleWord (erasePt π a) f x = cycleWord π f x := by
  by_cases hc : π.SameCycle a x
  swap
  · exact cycleWord_congr _ (erasePt_pow_apply_of_not_sameCycle hc)
  by_cases hfix : π a = a
  · rw [erasePt_of_fixed hfix]
  have hbase : cycleWord (erasePt π a) f (π a) = cycleWord π f (π a) := by
    have := cycleWord_swap_mul_split (π := π) f hfix ⟨-1, by simp⟩
    rw [← erasePt_eq_swap_mul, cycleWord_of_fixed f erasePt_apply_self, hf, mul_one] at this
    exact this.symm
  have hstep : ∀ n : ℕ, (π ^ n) (π a) ≠ a →
      cycleWord (erasePt π a) f ((π ^ n) (π a)) = cycleWord π f ((π ^ n) (π a)) := by
    intro n
    induction n with
    | zero => intro _; simpa using hbase
    | succ n ih =>
      intro hn
      rw [pow_succ', Perm.mul_apply] at hn ⊢
      by_cases hya : (π ^ n) (π a) = a
      · rw [hya]; exact hbase
      have e : erasePt π a ((π ^ n) (π a)) = π ((π ^ n) (π a)) := erasePt_apply_of_ne hya hn
      rw [← e, cycleWord_apply, ih hya, e, cycleWord_apply]
  have hxa : π.SameCycle (π a) x := (Perm.sameCycle_apply_left.2 (Perm.SameCycle.refl π a)).trans hc
  obtain ⟨n, rfl⟩ := hxa.exists_nat_pow_eq
  exact hstep n hx

/-- The word of the cycle from which `a` was erased, read from `π a`. -/
theorem cycleWord_erasePt_apply {G : Type*} [Monoid G] [Finite D] (f : D → G) (h : π a ≠ a) :
    cycleWord π f (π a) = cycleWord (erasePt π a) f (π a) * f a := by
  have := cycleWord_swap_mul_split (π := π) f h ⟨-1, by simp⟩
  rwa [← erasePt_eq_swap_mul, cycleWord_of_fixed f erasePt_apply_self] at this

/-! ### Erasing two darts -/

/-- Remove the darts `a` and then `b`. -/
def erase2 (π : Perm D) (a b : D) : Perm D := erasePt (erasePt π a) b

theorem erase2_apply_right : erase2 π a b b = b := erasePt_apply_self

theorem erase2_apply_left (hab : a ≠ b) : erase2 π a b a = a :=
  erasePt_apply_of_fixed erasePt_apply_self hab

theorem erase2_apply_of_notMem (hx : x ≠ a) (hxb : x ≠ b) (h1 : π x ≠ a) (h2 : π x ≠ b) :
    erase2 π a b x = π x := by
  unfold erase2
  rw [erasePt_apply_of_ne hxb, erasePt_apply_of_ne hx h1]
  rwa [erasePt_apply_of_ne hx h1]

theorem erase2_apply_of_eq_left (hxb : x ≠ b) (h1 : π x = a) (h2 : π a ≠ b) :
    erase2 π a b x = π a := by
  unfold erase2
  rw [erasePt_apply_of_ne hxb, erasePt_apply_of_eq h1]
  rwa [erasePt_apply_of_eq h1]

theorem erase2_apply_of_eq_left_right (hab : a ≠ b) (hxb : x ≠ b) (h1 : π x = a)
    (h2 : π a = b) : erase2 π a b x = π b := by
  unfold erase2
  have hb : π b ≠ a := fun h => hxb (π.injective (h1.trans h.symm))
  rw [erasePt_apply_of_eq (by rw [erasePt_apply_of_eq h1, h2]), erasePt_apply_of_ne hab.symm hb]

theorem erase2_apply_of_eq_right (hab : a ≠ b) (hx : x ≠ a) (h1 : π x = b) (h2 : π b ≠ a) :
    erase2 π a b x = π b := by
  unfold erase2
  rw [erasePt_apply_of_eq (by rw [erasePt_apply_of_ne hx (by rw [h1]; exact hab.symm), h1]),
    erasePt_apply_of_ne hab.symm h2]

theorem erase2_apply_of_eq_right_left (hab : a ≠ b) (hx : x ≠ a) (h1 : π x = b)
    (h2 : π b = a) : erase2 π a b x = π a := by
  unfold erase2
  rw [erasePt_apply_of_eq (by rw [erasePt_apply_of_ne hx (by rw [h1]; exact hab.symm), h1]),
    erasePt_apply_of_eq h2]

theorem erase2_apply_ne_left (hab : a ≠ b) (hx : x ≠ a) : erase2 π a b x ≠ a := by
  intro h
  exact hx ((erase2 π a b).injective (h.trans (erase2_apply_left (π := π) hab).symm))

theorem erase2_apply_ne_right (hxb : x ≠ b) : erase2 π a b x ≠ b := by
  intro h
  exact hxb ((erase2 π a b).injective (h.trans erase2_apply_right.symm))

/-- The retained darts are invariant. -/
theorem erase2_retained_iff (hab : a ≠ b) (x : D) :
    (erase2 π a b x ≠ a ∧ erase2 π a b x ≠ b) ↔ (x ≠ a ∧ x ≠ b) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => h1 (by rw [h]; exact erase2_apply_left hab),
      fun h => h2 (by rw [h]; exact erase2_apply_right)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨erase2_apply_ne_left hab h1, erase2_apply_ne_right h2⟩

/-- **First return.**  On a retained dart, `erase2 π a b` is the first iterate of `π` that is
again retained. -/
theorem erase2_firstReturn (hab : a ≠ b) (hx : x ≠ a) (hxb : x ≠ b) :
    ∃ k : ℕ, 0 < k ∧ erase2 π a b x = (π ^ k) x ∧ (erase2 π a b x ≠ a ∧ erase2 π a b x ≠ b) ∧
      ∀ j, 0 < j → j < k → ((π ^ j) x = a ∨ (π ^ j) x = b) := by
  have hret := (erase2_retained_iff (π := π) hab x).2 ⟨hx, hxb⟩
  have p2 : (π ^ 2) x = π (π x) := by rw [pow_two]; rfl
  have p3 : (π ^ 3) x = π (π (π x)) := by rw [pow_succ, pow_two]; rfl
  by_cases h1 : π x = a
  · by_cases h2 : π a = b
    · refine ⟨3, by norm_num, ?_, hret, ?_⟩
      · rw [erase2_apply_of_eq_left_right hab hxb h1 h2, p3, h1, h2]
      · intro j hj hj'
        interval_cases j
        · left; simpa using h1
        · right; rw [p2, h1, h2]
    · refine ⟨2, by norm_num, ?_, hret, ?_⟩
      · rw [erase2_apply_of_eq_left hxb h1 h2, p2, h1]
      · intro j hj hj'
        interval_cases j
        left; simpa using h1
  by_cases h3 : π x = b
  · by_cases h2 : π b = a
    · refine ⟨3, by norm_num, ?_, hret, ?_⟩
      · rw [erase2_apply_of_eq_right_left hab hx h3 h2, p3, h3, h2]
      · intro j hj hj'
        interval_cases j
        · right; simpa using h3
        · left; rw [p2, h3, h2]
    · refine ⟨2, by norm_num, ?_, hret, ?_⟩
      · rw [erase2_apply_of_eq_right hab hx h3 h2, p2, h3]
      · intro j hj hj'
        interval_cases j
        right; simpa using h3
  · refine ⟨1, by norm_num, ?_, hret, fun j hj hj' => by omega⟩
    rw [erase2_apply_of_notMem hx hxb h1 h3]
    simp

theorem sameCycle_erase2_iff [Finite D] (hx : x ≠ a) (hxb : x ≠ b) (hy : y ≠ a) (hyb : y ≠ b) :
    (erase2 π a b).SameCycle x y ↔ π.SameCycle x y :=
  (sameCycle_erasePt_iff hxb hyb).trans (sameCycle_erasePt_iff hx hy)

theorem cycleWord_erase2 {G : Type*} [Group G] [Finite D] (f : D → G) (hx : x ≠ a) (hxb : x ≠ b)
    (ha : f a = 1) (hb : f b = 1) : cycleWord (erase2 π a b) f x = cycleWord π f x :=
  (cycleWord_erasePt f hxb hb).trans (cycleWord_erasePt f hx ha)

/-- Removing two fixed points from a permutation removes two orbits. -/
theorem numOrbits_subtypePerm_fix2 [Finite D] (hab : a ≠ b) (ha : π a = a) (hb : π b = b)
    (h : ∀ x, (π x ≠ a ∧ π x ≠ b) ↔ (x ≠ a ∧ x ≠ b)) :
    numOrbits (π.subtypePerm (p := fun x => x ≠ a ∧ x ≠ b) h) + 2 = numOrbits π := by
  rw [numOrbits_subtypePerm_add π (fun x => x ≠ a ∧ x ≠ b) h]
  suffices numOrbits (π.subtypePerm (p := fun x => ¬ (x ≠ a ∧ x ≠ b))
      fun x => not_congr (h x)) = 2 by omega
  have hmem : ∀ z : {x // ¬ (x ≠ a ∧ x ≠ b)}, z.val = a ∨ z.val = b := by
    rintro ⟨z, hz⟩
    by_contra h'
    push_neg at h'
    exact hz h'
  have hfix : ∀ z : {x // ¬ (x ≠ a ∧ x ≠ b)}, π z.val = z.val := by
    intro z
    rcases hmem z with e | e <;> rw [e]
    · exact ha
    · exact hb
  rw [numOrbits_eq_of_iff _ (fun z => decide (z.val = a)), Nat.card_eq_fintype_card,
    Fintype.card_bool]
  · rintro (_ | _)
    · exact ⟨⟨b, by simp⟩, by simp [hab.symm]⟩
    · exact ⟨⟨a, by simp⟩, by simp⟩
  · intro z w
    rw [Perm.sameCycle_subtypePerm]
    constructor
    · intro hzw
      have : z = w := by
        rcases hmem z with e1 | e1 <;> rcases hmem w with e2 | e2
        · exact Subtype.ext (e1.trans e2.symm)
        · simp [e1, e2, hab.symm] at hzw
        · simp [e1, e2, hab.symm] at hzw
        · exact Subtype.ext (e1.trans e2.symm)
      rw [this]
    · intro hzw
      have := hzw.eq_of_left (hfix z)
      rw [Subtype.ext this]

/-- The orbit count after erasing two darts, before discarding them. -/
theorem numOrbits_erase2 [Finite D] (π : Perm D) (a b : D) :
    numOrbits (erase2 π a b) = numOrbits π + (if π a = a then 0 else 1) +
      (if erasePt π a b = b then 0 else 1) := by
  unfold erase2
  have h1 : numOrbits (erasePt π a) = numOrbits π + (if π a = a then 0 else 1) := by
    split_ifs with h
    · rw [erasePt_of_fixed h]; rfl
    · exact numOrbits_erasePt h
  split_ifs at h1 ⊢ with h2 h3 h3
  · rw [erasePt_of_fixed h3, h1]
  · rw [numOrbits_erasePt h3, h1]
  · rw [erasePt_of_fixed h3, h1]
  · rw [numOrbits_erasePt h3, h1]

/-- **Cycle count of an erasure.**  Restricting `erase2 π a b` to the retained darts loses
exactly the old cycles contained in `{a, b}`: the fixed points among `a, b`, and the cycle
`(a b)` if it is one. -/
theorem numOrbits_erase2_restrict [Finite D] (hab : a ≠ b) :
    numOrbits ((erase2 π a b).subtypePerm (p := fun x => x ≠ a ∧ x ≠ b)
        (erase2_retained_iff hab)) +
      ((if π a = a then 1 else 0) + (if π b = b then 1 else 0) +
        (if π a = b ∧ π b = a then 1 else 0)) = numOrbits π := by
  have hr := numOrbits_subtypePerm_fix2 (π := erase2 π a b) hab (erase2_apply_left hab)
    erase2_apply_right (erase2_retained_iff hab)
  have he := numOrbits_erase2 π a b
  have hb1 : erasePt π a b = if π b = a then π a else π b := by
    split_ifs with h
    · exact erasePt_apply_of_eq h
    · exact erasePt_apply_of_ne hab.symm h
  rw [hb1] at he
  by_cases h1 : π a = a
  · have h4 : π b ≠ a := fun h => hab (π.injective (h1.trans h.symm))
    have h5 : ¬ (π a = b ∧ π b = a) := fun h => h4 h.2
    rw [if_pos h1, if_neg h4] at he
    rw [if_pos h1, if_neg h5]
    by_cases h6 : π b = b
    · rw [if_pos h6] at he ⊢; omega
    · rw [if_neg h6] at he ⊢; omega
  · rw [if_neg h1] at he ⊢
    by_cases h2 : π a = b ∧ π b = a
    · have h6 : π b ≠ b := fun h => hab (π.injective (h2.1.trans h.symm))
      rw [if_pos h2.2, if_pos h2.1] at he
      rw [if_neg h6, if_pos h2]
      omega
    · rw [if_neg h2]
      by_cases h7 : π b = a
      · have h8 : π a ≠ b := fun h => h2 ⟨h, h7⟩
        have h9 : π b ≠ b := fun h => hab (h7.symm.trans h)
        rw [if_pos h7, if_neg h8] at he
        rw [if_neg h9]
        omega
      · rw [if_neg h7] at he
        by_cases h6 : π b = b
        · rw [if_pos h6] at he ⊢; omega
        · rw [if_neg h6] at he ⊢; omega

/-! ### Faces after deleting an edge -/

/-- **First return and the edge involution.**  If `α` is an involution with `α a = b`, then the
first-return map of `π` to the complement of `{a, b}`, precomposed with `α`, is the first-return
map of `swap a b * π * α`.  (For a map, this is the face permutation after deleting the edge
`{a, b}`.) -/
theorem erase2_apply_α {α : Perm D} (hα : ∀ z, α (α z) = z) (hab : a ≠ b) (hαa : α a = b)
    (hx : x ≠ a) (hxb : x ≠ b) :
    erase2 π a b (α x) = erase2 (swap a b * π * α) a b x := by
  have hαb : α b = a := by rw [← hαa, hα]
  have hy : α x ≠ a := fun h => hxb (by rw [← hα x, h, hαa])
  have hyb : α x ≠ b := fun h => hx (by rw [← hα x, h, hαb])
  have hχ : ∀ z, (swap a b * π * α) z = swap a b (π (α z)) := fun z => rfl
  by_cases h1 : π (α x) = a
  · by_cases h2 : π a = b
    · rw [erase2_apply_of_eq_left_right hab hyb h1 h2]
      have hb : π b ≠ a := fun h => hyb (π.injective (h1.trans h.symm))
      have hb' : π b ≠ b := fun h => hab (π.injective (h2.trans h.symm))
      rw [erase2_apply_of_eq_right_left hab hx (by rw [hχ, h1, swap_apply_left])
        (by rw [hχ, hαb, h2, swap_apply_right]), hχ, hαa, swap_apply_of_ne_of_ne hb hb']
    · have ha' : π a ≠ a := fun h => hy (π.injective (h1.trans h.symm))
      rw [erase2_apply_of_eq_left hyb h1 h2,
        erase2_apply_of_eq_right hab hx (by rw [hχ, h1, swap_apply_left])
          (by rw [hχ, hαb, swap_apply_of_ne_of_ne ha' h2]; exact ha'),
        hχ, hαb, swap_apply_of_ne_of_ne ha' h2]
  by_cases h3 : π (α x) = b
  · by_cases h2 : π b = a
    · rw [erase2_apply_of_eq_right_left hab hy h3 h2]
      have ha1 : π a ≠ a := fun h => hab (π.injective (h.trans h2.symm))
      have ha2 : π a ≠ b := fun h => hy (π.injective (h3.trans h.symm))
      rw [erase2_apply_of_eq_left_right hab hxb (by rw [hχ, h3, swap_apply_right])
        (by rw [hχ, hαa, h2, swap_apply_left]), hχ, hαb, swap_apply_of_ne_of_ne ha1 ha2]
    · have hb' : π b ≠ b := fun h => hyb (π.injective (h3.trans h.symm))
      rw [erase2_apply_of_eq_right hab hy h3 h2,
        erase2_apply_of_eq_left hxb (by rw [hχ, h3, swap_apply_right])
          (by rw [hχ, hαa, swap_apply_of_ne_of_ne h2 hb']; exact hb'),
        hχ, hαa, swap_apply_of_ne_of_ne h2 hb']
  · rw [erase2_apply_of_notMem hy hyb h1 h3, erase2_apply_of_notMem hx hxb
      (by rw [hχ, swap_apply_of_ne_of_ne h1 h3]; exact h1)
      (by rw [hχ, swap_apply_of_ne_of_ne h1 h3]; exact h3), hχ, swap_apply_of_ne_of_ne h1 h3]

end Erase

/-! ### General facts about cycle words -/

section Words

variable {D G : Type*} [Finite D]

omit [Finite D] in
theorem cycleWord_congr_fun [Monoid G] {π : Perm D} {f g : D → G} {x : D}
    (h : ∀ y, π.SameCycle x y → f y = g y) : cycleWord π f x = cycleWord π g x := by
  unfold cycleWord
  congr 1
  refine List.map_congr_left fun i _ => h _ (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _))

/-- **Changing the first letter** of a cycle word. -/
theorem cycleWord_update_first [Group G] (π : Perm D) {f g : D → G} {x : D}
    (h : ∀ y, π.SameCycle x y → y ≠ x → g y = f y) :
    cycleWord π g x = g x * (f x)⁻¹ * cycleWord π f x := by
  unfold cycleWord
  obtain ⟨m, hm⟩ : ∃ m, minimalPeriod π x = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (minimalPeriod_perm_pos π x)).symm⟩
  rw [hm, List.range_succ_eq_map, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
    List.map_map, List.map_map]
  have : ((List.range m).map ((fun i => g ((π ^ i) x)) ∘ Nat.succ)) =
      ((List.range m).map ((fun i => f ((π ^ i) x)) ∘ Nat.succ)) := by
    refine List.map_congr_left fun i hi => ?_
    simp only [Function.comp_apply]
    refine h _ (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)) ?_
    exact pow_apply_ne_self_of_lt (Nat.succ_pos i) (by rw [hm]; simpa using List.mem_range.mp hi)
  rw [this]
  simp only [pow_zero, Perm.one_apply]
  group

/-- **Merging two consecutive letters.**  If `π d ≠ d`, and `g` differs from `f` only at `d` and
`π d` (within the cycle), with `g d * g (π d) = f d * f (π d)`, then the cycle word read from any
dart of the cycle other than `π d` is unchanged. -/
theorem cycleWord_merge_consecutive [Group G] [DecidableEq D] {π : Perm D} {f g : D → G} {d b : D}
    (hde : π d ≠ d) (hb : π.SameCycle d b) (hbe : b ≠ π d)
    (hfg : ∀ y, π.SameCycle d y → y ≠ d → y ≠ π d → g y = f y)
    (hmul : g d * g (π d) = f d * f (π d)) : cycleWord π g b = cycleWord π f b := by
  set e := π d with he_def
  have hed : e ≠ d := hde
  -- first at `d`
  have hd : cycleWord π g d = cycleWord π f d := by
    set f₁ := Function.update f e (g e) with hf₁
    have h1 : cycleWord π g d = g d * (f₁ d)⁻¹ * cycleWord π f₁ d := by
      refine cycleWord_update_first π fun y hy hyd => ?_
      by_cases hye : y = e
      · rw [hye, hf₁, Function.update_self]
      · rw [hf₁, Function.update_of_ne hye]; exact hfg y hy hyd hye
    have hf₁d : f₁ d = f d := by rw [hf₁, Function.update_of_ne hed.symm]
    have h2 : cycleWord π f₁ e = (f₁ d)⁻¹ * cycleWord π f₁ d * f₁ d := cycleWord_apply _ _ _
    have h3 : cycleWord π f₁ e = f₁ e * (f e)⁻¹ * cycleWord π f e := by
      refine cycleWord_update_first π fun y _ hye => ?_
      rw [hf₁, Function.update_of_ne hye]
    have hf₁e : f₁ e = g e := by rw [hf₁, Function.update_self]
    have h4 : cycleWord π f e = (f d)⁻¹ * cycleWord π f d * f d := cycleWord_apply _ _ _
    have h5 : cycleWord π f₁ d = f d * cycleWord π f₁ e * (f d)⁻¹ := by
      rw [h2, hf₁d]; group
    rw [h1, h5, h3, h4, hf₁d, hf₁e]
    have hm : g d * g e = f d * f e := hmul
    calc g d * (f d)⁻¹ * (f d * (g e * (f e)⁻¹ * ((f d)⁻¹ * cycleWord π f d * f d)) * (f d)⁻¹)
        = (g d * g e) * (f e)⁻¹ * (f d)⁻¹ * cycleWord π f d := by group
      _ = cycleWord π f d := by rw [hm]; group
  -- then backwards around the cycle
  have hstep : ∀ n : ℕ, (π⁻¹ ^ n) d ≠ e →
      cycleWord π g ((π⁻¹ ^ n) d) = cycleWord π f ((π⁻¹ ^ n) d) := by
    intro n
    induction n with
    | zero => intro _; simpa using hd
    | succ n ih =>
      intro hn
      set z := (π⁻¹ ^ (n + 1)) d with hz
      have hzn : π z = (π⁻¹ ^ n) d := by
        rw [hz, pow_succ', Perm.mul_apply]
        exact π.apply_symm_apply _
      by_cases hzn' : (π⁻¹ ^ n) d = e
      · have : z = d := by
          apply π.injective; rw [hzn, hzn']
        rw [this]; exact hd
      by_cases hzd : z = d
      · rw [hzd]; exact hd
      have hzc : π.SameCycle d z := by
        refine ⟨-((n + 1 : ℕ) : ℤ), ?_⟩
        rw [hz, zpow_neg, zpow_natCast, inv_pow]
      have hgz : g z = f z := hfg z hzc hzd hn
      have e1 : cycleWord π g z = g z * cycleWord π g (π z) * (g z)⁻¹ := by
        rw [cycleWord_apply]; group
      have e2 : cycleWord π f z = f z * cycleWord π f (π z) * (f z)⁻¹ := by
        rw [cycleWord_apply]; group
      rw [e1, e2, hzn, ih hzn', hgz]
  have hb' : π⁻¹.SameCycle d b := Perm.sameCycle_inv.2 hb
  obtain ⟨n, rfl⟩ := hb'.exists_nat_pow_eq
  exact hstep n hbe

end Words

end TheoremA.Picture
