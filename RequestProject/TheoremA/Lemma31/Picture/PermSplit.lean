module

public import RequestProject.TheoremA.Lemma31.Picture.PermOrbits

/-!
# Splitting a permutation cycle

If `a ≠ b` lie in the **same** cycle `(a, x₁, …, x_r, b, y₁, …, y_s)` of `π`, then
`swap a b * π` replaces it by the two cycles `(a, x₁, …, x_r)` and `(b, y₁, …, y_s)` and leaves all
other cycles unchanged.  This is the converse surgery to the merge of `PermOrbits.lean`.

* `sameCycle_swap_mul_split` : `a` and `b` lie in different cycles of `swap a b * π` (proved
  directly, by following the first arc `a, π a, …` up to the first visit of `b`);
* `numOrbits_swap_mul_split` : `numOrbits (swap a b * π) = numOrbits π + 1`;
* `cycleWord_swap_mul_split` : the old word based at `a` is the new word based at `a` followed by
  the new word based at `b`;
* `sameCycle_swap_mul_split_iff` : the complete description of the new cycles.
-/

@[expose] public section

namespace TheoremA.Picture

open Equiv Function

section Split

variable {D : Type*} [DecidableEq D] [Finite D] {π : Perm D} {a b : D}

omit [DecidableEq D] in
theorem exists_pow_eq_of_sameCycle (h : π.SameCycle a b) : ∃ n : ℕ, (π ^ n) a = b :=
  h.exists_nat_pow_eq

/-- **Splitting a cycle.**  If `a ≠ b` lie in the same cycle of `π`, they lie in different cycles
of `swap a b * π`. -/
theorem sameCycle_swap_mul_split (hab : a ≠ b) (h : π.SameCycle a b) :
    ¬ (swap a b * π).SameCycle a b := by
  classical
  have hex : ∃ n : ℕ, (π ^ n) a = b := exists_pow_eq_of_sameCycle h
  set k := Nat.find hex with hk
  have hkb : (π ^ k) a = b := Nat.find_spec hex
  have hmin : ∀ j < k, (π ^ j) a ≠ b := fun j hj => Nat.find_min hex hj
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hkb; exact absurd hkb (by simpa using hab)
    · exact h0
  -- along the first arc the new permutation agrees with the old one
  have harc : ∀ j < k, ((swap a b * π) ^ j) a = (π ^ j) a := by
    intro j hj
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', Perm.mul_apply, ih (by omega), Perm.mul_apply, ← Perm.mul_apply π,
        ← pow_succ']
      apply swap_apply_of_ne_of_ne
      · intro hja
        -- then `π ^ (k - (j+1))` already sends `a` to `b`
        apply hmin (k - (j + 1)) (by omega)
        have : (π ^ k) a = (π ^ (k - (j + 1))) ((π ^ (j + 1)) a) := by
          rw [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (by omega)]
        rw [← hkb, this, hja]
      · exact hmin (j + 1) hj
  have hper : ((swap a b * π) ^ k) a = a := by
    obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [hm] at hkb ⊢
    rw [pow_succ', Perm.mul_apply, harc m (by omega), Perm.mul_apply, ← Perm.mul_apply π,
      ← pow_succ', hkb, swap_apply_right]
  intro hs
  obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
  have hq : ∀ q : ℕ, ((swap a b * π) ^ (k * q)) a = a := by
    intro q
    induction q with
    | zero => rfl
    | succ q ih => rw [Nat.mul_succ, pow_add, Perm.mul_apply, hper, ih]
  have hmod : ((swap a b * π) ^ (n % k)) a = ((swap a b * π) ^ n) a := by
    conv_rhs => rw [← Nat.mod_add_div n k, pow_add, Perm.mul_apply, hq]
  rw [← hmod, harc _ (Nat.mod_lt _ hk0)] at hn
  exact hmin _ (Nat.mod_lt _ hk0) hn

omit [Finite D] in
theorem swap_mul_swap_mul (a b : D) (π : Perm D) : swap a b * (swap a b * π) = π := by
  rw [← mul_assoc, swap_mul_self, one_mul]

/-- **Splitting a cycle adds exactly one orbit.** -/
theorem numOrbits_swap_mul_split (hab : a ≠ b) (h : π.SameCycle a b) :
    numOrbits (swap a b * π) = numOrbits π + 1 := by
  have := numOrbits_swap_mul (sameCycle_swap_mul_split hab h)
  rw [swap_mul_swap_mul] at this
  exact this

/-- **The words of a split cycle.**  The old word based at `a` is the new word based at `a`
followed by the new word based at `b`. -/
theorem cycleWord_swap_mul_split {M : Type*} [Monoid M] (f : D → M) (hab : a ≠ b)
    (h : π.SameCycle a b) :
    cycleWord π f a = cycleWord (swap a b * π) f a * cycleWord (swap a b * π) f b := by
  have := cycleWord_swap_mul f (sameCycle_swap_mul_split hab h)
  rwa [swap_mul_swap_mul] at this

/-- **Cycles after splitting.**  Two darts are in the same cycle of `swap a b * π` iff they are in
the same cycle of `π` and are not separated by the split (the cycle of `a` splits into the new
cycle of `a` and the new cycle of `b`). -/
theorem sameCycle_swap_mul_split_iff (hab : a ≠ b) (h : π.SameCycle a b) {x y : D} :
    π.SameCycle x y ↔ (swap a b * π).SameCycle x y ∨
      (((swap a b * π).SameCycle a x ∨ (swap a b * π).SameCycle b x) ∧
        ((swap a b * π).SameCycle a y ∨ (swap a b * π).SameCycle b y)) := by
  have := sameCycle_swap_mul_iff (π := swap a b * π) (x := x) (y := y)
    (sameCycle_swap_mul_split hab h)
  rwa [swap_mul_swap_mul] at this

/-- One transposition changes the number of cycles by at most one. -/
theorem numOrbits_swap_mul_le (a b : D) (π : Perm D) :
    numOrbits (swap a b * π) ≤ numOrbits π + 1 := by
  by_cases hab : a = b
  · subst hab; rw [Equiv.swap_self]; change numOrbits π ≤ numOrbits π + 1; omega
  by_cases h : π.SameCycle a b
  · rw [numOrbits_swap_mul_split hab h]
  · have := numOrbits_swap_mul h; omega

end Split

end TheoremA.Picture
