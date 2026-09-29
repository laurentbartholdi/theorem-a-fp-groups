module

public import Mathlib

/-!
# Orbits of permutations under the surgeries used for pictures

Combinatorial maps are described by permutations of a finite set of darts; vertices, edges and
faces are orbits of permutations.  This file contains the permutation facts needed to glue maps:

* `numOrbits π` : the number of orbits (cycles, including fixed points) of `π`;
* `numOrbits_eq_of_iff` : counting orbits through a complete invariant;
* `numOrbits_sumCongr` : orbits of a disjoint union of permutations;
* `sameCycle_swap_mul_iff`, `numOrbits_swap_mul` : **merging two cycles**.  If `a` and `b` lie in
  different cycles of `π`, then `swap a b * π` has exactly the same cycles as `π`, except that the
  cycles of `a` and `b` are merged into one; in particular it has one orbit fewer;
* `cycleWord` : the product of labels read once around the cycle of a dart, with the rules for
  merged cycles (`cycleWord_swap_mul`), unchanged cycles (`cycleWord_congr`) and a change of the
  starting dart (`cycleWord_apply`).
-/

@[expose] public section

namespace TheoremA.Picture

open Equiv Function

section Basic

variable {D : Type*}

/-- The number of orbits (cycles, including fixed points) of a permutation. -/
noncomputable def numOrbits (π : Perm D) : ℕ := Nat.card (Quotient (Perm.SameCycle.setoid π))

/-- Counting orbits through a complete invariant. -/
theorem numOrbits_eq_of_iff {Q : Type*} (π : Perm D) (f : D → Q) (hf : Surjective f)
    (h : ∀ x y, f x = f y ↔ π.SameCycle x y) : numOrbits π = Nat.card Q := by
  unfold numOrbits
  refine Nat.card_congr (Equiv.ofBijective (Quotient.lift f fun x y hxy => (h x y).2 hxy)
    ⟨?_, ?_⟩)
  · rintro ⟨x⟩ ⟨y⟩ hxy
    exact Quotient.sound ((h x y).1 hxy)
  · intro q
    obtain ⟨x, rfl⟩ := hf q
    exact ⟨⟦x⟧, rfl⟩

theorem sameCycle_of_pow_eq {π : Perm D} {x y : D} (n : ℕ) (h : (π ^ n) x = y) :
    π.SameCycle x y :=
  ⟨n, by simpa using h⟩

/-- A function invariant under `π` is constant on the cycles of `π`. -/
theorem SameCycle.eq_of_invariant [Finite D] {Q : Type*} {π : Perm D} {f : D → Q}
    (hf : ∀ x, f (π x) = f x) {x y : D} (h : π.SameCycle x y) : f x = f y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, hf, ih]

variable [Finite D]

theorem mem_periodicPts_perm (π : Perm D) (x : D) : x ∈ periodicPts π :=
  ⟨orderOf π, orderOf_pos π, by
    rw [IsPeriodicPt, IsFixedPt, ← Perm.coe_pow, pow_orderOf_eq_one, Perm.one_apply]⟩

theorem minimalPeriod_perm_pos (π : Perm D) (x : D) : 0 < minimalPeriod π x :=
  minimalPeriod_pos_of_mem_periodicPts (mem_periodicPts_perm π x)

omit [Finite D] in
theorem pow_minimalPeriod_apply (π : Perm D) (x : D) : (π ^ minimalPeriod π x) x = x := by
  rw [Perm.coe_pow]; exact iterate_minimalPeriod

omit [Finite D] in
theorem pow_apply_ne_self_of_lt {π : Perm D} {x : D} {k : ℕ} (hk : 0 < k)
    (hk' : k < minimalPeriod π x) : (π ^ k) x ≠ x := by
  rw [Perm.coe_pow]
  exact not_isPeriodicPt_of_pos_of_lt_minimalPeriod (Nat.pos_iff_ne_zero.mp hk) hk'

/-- Characterisation of the minimal period of a point of a finite permutation. -/
theorem minimalPeriod_eq_of {π : Perm D} {x : D} {n : ℕ} (hn : 0 < n) (hper : (π ^ n) x = x)
    (hne : ∀ k, 0 < k → k < n → (π ^ k) x ≠ x) : minimalPeriod π x = n := by
  apply le_antisymm
  · exact IsPeriodicPt.minimalPeriod_le hn
      (by rw [IsPeriodicPt, IsFixedPt, ← Perm.coe_pow]; exact hper)
  · by_contra hlt
    push_neg at hlt
    exact hne _ (minimalPeriod_perm_pos π x) hlt (pow_minimalPeriod_apply π x)

/-- If two permutations have the same iterates at `x`, they have the same period at `x`. -/
theorem minimalPeriod_congr {π π' : Perm D} {x : D} (h : ∀ n : ℕ, (π' ^ n) x = (π ^ n) x) :
    minimalPeriod π' x = minimalPeriod π x := by
  refine minimalPeriod_eq_of (minimalPeriod_perm_pos π x) ?_ ?_
  · rw [h]; exact pow_minimalPeriod_apply π x
  · intro k hk hk'
    rw [h]
    exact pow_apply_ne_self_of_lt hk hk'

end Basic

/-! ### Words read around a cycle -/

section CycleWord

variable {D : Type*} {M : Type*}

/-- The product of the labels `f d` of the darts `x, π x, π² x, …` read once around the cycle of
`x`. -/
noncomputable def cycleWord [Monoid M] (π : Perm D) (f : D → M) (x : D) : M :=
  ((List.range (minimalPeriod π x)).map fun i => f ((π ^ i) x)).prod

variable [Finite D]

theorem cycleWord_congr [Monoid M] {π π' : Perm D} (f : D → M) {x : D}
    (h : ∀ n : ℕ, (π' ^ n) x = (π ^ n) x) : cycleWord π' f x = cycleWord π f x := by
  unfold cycleWord
  rw [minimalPeriod_congr h]
  simp only [h]

/-- Changing the starting dart of a cycle word conjugates it. -/
theorem cycleWord_apply [Group M] (π : Perm D) (f : D → M) (x : D) :
    cycleWord π f (π x) = (f x)⁻¹ * cycleWord π f x * f x := by
  unfold cycleWord
  rw [minimalPeriod_apply (mem_periodicPts_perm π x)]
  obtain ⟨m, hm⟩ : ∃ m, minimalPeriod π x = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (minimalPeriod_perm_pos π x)).symm⟩
  have hper := pow_minimalPeriod_apply π x
  rw [hm] at hper ⊢
  have e : ∀ i : ℕ, (π ^ i) (π x) = (π ^ (i + 1)) x := fun i => by
    rw [pow_succ, Perm.mul_apply]
  simp only [e]
  conv_lhs => rw [List.range_succ, List.map_append, List.prod_append]
  conv_rhs => rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  simp only [List.map_singleton, List.prod_singleton, hper, pow_zero, Perm.one_apply]
  simp only [Function.comp_def, Nat.succ_eq_add_one]
  group

end CycleWord

/-! ### Disjoint unions -/

section Sum

variable {α β : Type*} (σ : Perm α) (τ : Perm β)

theorem sumCongr_zpow' (i : ℤ) : Perm.sumCongr σ τ ^ i = Perm.sumCongr (σ ^ i) (τ ^ i) :=
  (map_zpow (Perm.sumCongrHom α β) (σ, τ) i).symm

theorem sumCongr_pow' (n : ℕ) : Perm.sumCongr σ τ ^ n = Perm.sumCongr (σ ^ n) (τ ^ n) :=
  (map_pow (Perm.sumCongrHom α β) (σ, τ) n).symm

variable {σ τ}

theorem sameCycle_sumCongr_inl {x y : α} :
    (Perm.sumCongr σ τ).SameCycle (Sum.inl x) (Sum.inl y) ↔ σ.SameCycle x y := by
  simp [Perm.SameCycle, sumCongr_zpow']

theorem sameCycle_sumCongr_inr {x y : β} :
    (Perm.sumCongr σ τ).SameCycle (Sum.inr x) (Sum.inr y) ↔ τ.SameCycle x y := by
  simp [Perm.SameCycle, sumCongr_zpow']

theorem not_sameCycle_sumCongr_inl_inr {x : α} {y : β} :
    ¬ (Perm.sumCongr σ τ).SameCycle (Sum.inl x) (Sum.inr y) := by
  simp [Perm.SameCycle, sumCongr_zpow']

theorem not_sameCycle_sumCongr_inr_inl {x : β} {y : α} :
    ¬ (Perm.sumCongr σ τ).SameCycle (Sum.inr x) (Sum.inl y) := by
  simp [Perm.SameCycle, sumCongr_zpow']

variable (σ τ)

theorem numOrbits_sumCongr [Finite α] [Finite β] :
    numOrbits (Perm.sumCongr σ τ) = numOrbits σ + numOrbits τ := by
  rw [numOrbits_eq_of_iff (Perm.sumCongr σ τ)
    (Sum.map (Quotient.mk (Perm.SameCycle.setoid σ)) (Quotient.mk (Perm.SameCycle.setoid τ)))]
  · rw [Nat.card_sum]; rfl
  · rintro (q | q)
    · obtain ⟨x, rfl⟩ := Quotient.exists_rep q
      exact ⟨Sum.inl x, rfl⟩
    · obtain ⟨x, rfl⟩ := Quotient.exists_rep q
      exact ⟨Sum.inr x, rfl⟩
  · rintro (x | x) (y | y)
    · simp only [Sum.map_inl, Sum.inl.injEq, sameCycle_sumCongr_inl]
      exact Quotient.eq
    · simp [not_sameCycle_sumCongr_inl_inr]
    · simp [not_sameCycle_sumCongr_inr_inl]
    · simp only [Sum.map_inr, Sum.inr.injEq, sameCycle_sumCongr_inr]
      exact Quotient.eq

end Sum

section SumWord

variable {α β M : Type*} [Finite α] [Finite β] (σ : Perm α) (τ : Perm β)

theorem minimalPeriod_sumCongr_inl (x : α) :
    minimalPeriod (Perm.sumCongr σ τ) (Sum.inl x) = minimalPeriod σ x := by
  refine minimalPeriod_eq_of (minimalPeriod_perm_pos σ x) ?_ ?_
  · rw [sumCongr_pow', Perm.sumCongr_apply, Sum.map_inl, pow_minimalPeriod_apply]
  · intro k hk hk'
    rw [sumCongr_pow', Perm.sumCongr_apply, Sum.map_inl, Ne, Sum.inl.injEq]
    exact pow_apply_ne_self_of_lt hk hk'

theorem minimalPeriod_sumCongr_inr (x : β) :
    minimalPeriod (Perm.sumCongr σ τ) (Sum.inr x) = minimalPeriod τ x := by
  refine minimalPeriod_eq_of (minimalPeriod_perm_pos τ x) ?_ ?_
  · rw [sumCongr_pow', Perm.sumCongr_apply, Sum.map_inr, pow_minimalPeriod_apply]
  · intro k hk hk'
    rw [sumCongr_pow', Perm.sumCongr_apply, Sum.map_inr, Ne, Sum.inr.injEq]
    exact pow_apply_ne_self_of_lt hk hk'

theorem cycleWord_sumCongr_inl [Monoid M] (f : α ⊕ β → M) (x : α) :
    cycleWord (Perm.sumCongr σ τ) f (Sum.inl x) = cycleWord σ (f ∘ Sum.inl) x := by
  unfold cycleWord
  rw [minimalPeriod_sumCongr_inl]
  simp [sumCongr_pow']

theorem cycleWord_sumCongr_inr [Monoid M] (f : α ⊕ β → M) (x : β) :
    cycleWord (Perm.sumCongr σ τ) f (Sum.inr x) = cycleWord τ (f ∘ Sum.inr) x := by
  unfold cycleWord
  rw [minimalPeriod_sumCongr_inr]
  simp [sumCongr_pow']

end SumWord

/-- The word of a cycle of length two. -/
theorem cycleWord_of_apply_apply {D M : Type*} [Finite D] [Monoid M] (π : Perm D) (f : D → M)
    (x : D) (h1 : π x ≠ x) (h2 : π (π x) = x) : cycleWord π f x = f x * f (π x) := by
  have : minimalPeriod π x = 2 := by
    refine minimalPeriod_eq_of (by norm_num) (by rw [pow_two, Perm.mul_apply]; exact h2) ?_
    intro k hk hk'
    interval_cases k
    simpa using h1
  simp [cycleWord, this, List.range_succ]

/-! ### Merging two cycles -/

section Merge

variable {D : Type*} [DecidableEq D] {π : Perm D} {a b : D}

/-- Away from the cycles of `a` and `b`, `swap a b * π` acts like `π`. -/
theorem swap_mul_pow_apply_of_not_sameCycle {x : D} (hxa : ¬ π.SameCycle a x)
    (hxb : ¬ π.SameCycle b x) (n : ℕ) : ((swap a b * π) ^ n) x = (π ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, Perm.mul_apply, pow_succ', Perm.mul_apply]
    apply swap_apply_of_ne_of_ne
    · rintro h
      exact hxa (sameCycle_of_pow_eq (n + 1) (by rw [pow_succ', Perm.mul_apply, h])).symm
    · rintro h
      exact hxb (sameCycle_of_pow_eq (n + 1) (by rw [pow_succ', Perm.mul_apply, h])).symm

variable [Finite D]

omit [Finite D] in
/-- Along the cycle of `a`, `swap a b * π` acts like `π` until the cycle closes. -/
theorem swap_mul_pow_apply_of_lt (hab : ¬ π.SameCycle a b) {k : ℕ}
    (hk : k < minimalPeriod π a) : ((swap a b * π) ^ k) a = (π ^ k) a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, ih (by omega), Perm.mul_apply, ← Perm.mul_apply π,
      ← pow_succ']
    apply swap_apply_of_ne_of_ne
    · exact pow_apply_ne_self_of_lt (Nat.succ_pos k) hk
    · intro h
      exact hab (sameCycle_of_pow_eq (k + 1) h)

/-- After a full turn around the cycle of `a`, `swap a b * π` jumps to `b`. -/
theorem swap_mul_pow_minimalPeriod_apply (hab : ¬ π.SameCycle a b) :
    ((swap a b * π) ^ minimalPeriod π a) a = b := by
  obtain ⟨m, hm⟩ : ∃ m, minimalPeriod π a = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (minimalPeriod_perm_pos π a)).symm⟩
  have hper := pow_minimalPeriod_apply π a
  rw [hm] at hper
  rw [hm, pow_succ', Perm.mul_apply, swap_mul_pow_apply_of_lt hab (by omega), Perm.mul_apply,
    ← Perm.mul_apply π, ← pow_succ', hper, swap_apply_left]

omit [Finite D] in
theorem swap_comm_mul (a b : D) : swap a b * π = swap b a * π := by rw [swap_comm]

/-- The merged cycle, read from `a`: first the cycle of `a`, then the cycle of `b`. -/
theorem swap_mul_pow_add_apply (hab : ¬ π.SameCycle a b) {j : ℕ}
    (hj : j < minimalPeriod π b) :
    ((swap a b * π) ^ (minimalPeriod π a + j)) a = (π ^ j) b := by
  rw [add_comm, pow_add, Perm.mul_apply, swap_mul_pow_minimalPeriod_apply hab, swap_comm_mul,
    swap_mul_pow_apply_of_lt (fun h => hab h.symm) hj]

theorem swap_mul_pow_period_add_period (hab : ¬ π.SameCycle a b) :
    ((swap a b * π) ^ (minimalPeriod π a + minimalPeriod π b)) a = a := by
  rw [add_comm, pow_add, Perm.mul_apply, swap_mul_pow_minimalPeriod_apply hab, swap_comm_mul,
    swap_mul_pow_minimalPeriod_apply (fun h => hab h.symm)]

/-- The merged cycle has length the sum of the two lengths. -/
theorem minimalPeriod_swap_mul (hab : ¬ π.SameCycle a b) :
    minimalPeriod (swap a b * π) a = minimalPeriod π a + minimalPeriod π b := by
  refine minimalPeriod_eq_of (by have := minimalPeriod_perm_pos π a; omega)
    (swap_mul_pow_period_add_period hab) ?_
  intro k hk hk'
  by_cases hka : k < minimalPeriod π a
  · rw [swap_mul_pow_apply_of_lt hab hka]
    exact pow_apply_ne_self_of_lt hk hka
  · obtain ⟨j, rfl⟩ : ∃ j, k = minimalPeriod π a + j := ⟨k - minimalPeriod π a, by omega⟩
    rw [swap_mul_pow_add_apply hab (by omega)]
    intro h
    exact hab (sameCycle_of_pow_eq j h).symm

theorem sameCycle_swap_mul_left_right (hab : ¬ π.SameCycle a b) :
    (swap a b * π).SameCycle a b :=
  sameCycle_of_pow_eq _ (swap_mul_pow_minimalPeriod_apply hab)

/-- Every dart of the cycle of `a` lies on the merged cycle. -/
theorem sameCycle_swap_mul_of_sameCycle_left (hab : ¬ π.SameCycle a b) {x : D}
    (hx : π.SameCycle a x) : (swap a b * π).SameCycle a x := by
  obtain ⟨n, rfl⟩ := hx.exists_nat_pow_eq
  have e : (π ^ (n % minimalPeriod π a)) a = (π ^ n) a := by
    rw [Perm.coe_pow, Perm.coe_pow]; exact iterate_mod_minimalPeriod_eq
  rw [← e]
  exact sameCycle_of_pow_eq _
    (swap_mul_pow_apply_of_lt hab (Nat.mod_lt _ (minimalPeriod_perm_pos π a)))

/-- **Cycles after merging.**  If `a` and `b` are in different cycles of `π`, the cycles of
`swap a b * π` are those of `π`, except that the cycles of `a` and `b` are merged. -/
theorem sameCycle_swap_mul_iff (hab : ¬ π.SameCycle a b) {x y : D} :
    (swap a b * π).SameCycle x y ↔ π.SameCycle x y ∨
      ((π.SameCycle a x ∨ π.SameCycle b x) ∧ (π.SameCycle a y ∨ π.SameCycle b y)) := by
  set M : D → Prop := fun z => π.SameCycle a z ∨ π.SameCycle b z with hM
  have hMa : ∀ z, π.SameCycle a z → (swap a b * π).SameCycle a z :=
    fun z hz => sameCycle_swap_mul_of_sameCycle_left hab hz
  have hMb : ∀ z, π.SameCycle b z → (swap a b * π).SameCycle a z := fun z hz =>
    (sameCycle_swap_mul_left_right hab).trans
      (by rw [swap_comm_mul]; exact sameCycle_swap_mul_of_sameCycle_left (fun h => hab h.symm) hz)
  have hM' : ∀ z, M z → (swap a b * π).SameCycle a z := fun z hz => hz.elim (hMa z) (hMb z)
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => exact Or.inl (Perm.SameCycle.refl _ _)
    | succ n ih =>
      set z := ((swap a b * π) ^ n) x
      rw [pow_succ', Perm.mul_apply, Perm.mul_apply]
      have step : π.SameCycle z (swap a b (π z)) ∨ (M z ∧ M (swap a b (π z))) := by
        by_cases hza : π z = a
        · right
          rw [hza, swap_apply_left]
          exact ⟨Or.inl (Perm.SameCycle.symm (⟨1, by simpa using hza⟩ : π.SameCycle z a)),
            Or.inr (Perm.SameCycle.refl _ _)⟩
        · by_cases hzb : π z = b
          · right
            rw [hzb, swap_apply_right]
            exact ⟨Or.inr (Perm.SameCycle.symm (⟨1, by simpa using hzb⟩ : π.SameCycle z b)),
              Or.inl (Perm.SameCycle.refl _ _)⟩
          · left
            rw [swap_apply_of_ne_of_ne hza hzb]
            exact ⟨1, by simp⟩
      have Minv : ∀ u w, π.SameCycle u w → (M u ↔ M w) := fun u w huw => by
        simp only [hM]
        exact ⟨fun h => h.imp (·.trans huw) (·.trans huw),
          fun h => h.imp (·.trans huw.symm) (·.trans huw.symm)⟩
      rcases ih with h1 | ⟨h1, h2⟩ <;> rcases step with h3 | ⟨h3, h4⟩
      · exact Or.inl (h1.trans h3)
      · exact Or.inr ⟨(Minv _ _ h1).2 h3, h4⟩
      · exact Or.inr ⟨h1, (Minv _ _ h3).1 h2⟩
      · exact Or.inr ⟨h1, h4⟩
  · rintro (h | ⟨hx, hy⟩)
    · by_cases hx : M x
      · exact (hM' x hx).symm.trans (hM' y (hx.elim (fun h' => Or.inl (h'.trans h))
          (fun h' => Or.inr (h'.trans h))))
      · obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
        refine sameCycle_of_pow_eq n ?_
        exact swap_mul_pow_apply_of_not_sameCycle (fun h' => hx (Or.inl h'))
          (fun h' => hx (Or.inr h')) n
    · exact (hM' x hx).symm.trans (hM' y hy)

/-- A counting lemma: a surjection that is injective except for identifying two points loses
exactly one element. -/
theorem nat_card_eq_add_one_of_merge {X Y : Type*} [Finite X] (g : X → Y) (hg : Surjective g)
    {p q : X} (hpq : p ≠ q)
    (h : ∀ x y, g x = g y ↔ x = y ∨ ((x = p ∨ x = q) ∧ (y = p ∨ y = q))) :
    Nat.card X = Nat.card Y + 1 := by
  have hY : Nat.card {x : X // x ≠ q} = Nat.card Y := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => g x.1) ⟨?_, ?_⟩)
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      rcases (h x y).1 hxy with rfl | ⟨hx' | hx', hy' | hy'⟩
      · rfl
      · subst hx'; subst hy'; rfl
      · exact absurd hy' hy
      · exact absurd hx' hx
      · exact absurd hx' hx
    · intro z
      obtain ⟨x, rfl⟩ := hg z
      by_cases hx : x = q
      · exact ⟨⟨p, hpq⟩, (h p x).2 (Or.inr ⟨Or.inl rfl, Or.inr hx⟩)⟩
      · exact ⟨⟨x, hx⟩, rfl⟩
  have := Fintype.ofFinite X
  classical
  rw [← hY, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]
  have : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨p⟩
  omega

/-- **Merging two cycles removes exactly one orbit.** -/
theorem numOrbits_swap_mul (hab : ¬ π.SameCycle a b) :
    numOrbits π = numOrbits (swap a b * π) + 1 := by
  unfold numOrbits
  refine nat_card_eq_add_one_of_merge
    (Quotient.map id fun x y (hxy : π.SameCycle x y) =>
      ((sameCycle_swap_mul_iff hab).2 (Or.inl hxy)))
    (p := ⟦a⟧) (q := ⟦b⟧) ?_ ?_ ?_
  · rintro ⟨x⟩; exact ⟨⟦x⟧, rfl⟩
  · intro h; exact hab (Quotient.exact h)
  · intro x y
    induction x using Quotient.inductionOn with | h x => ?_
    induction y using Quotient.inductionOn with | h y => ?_
    have e : ∀ z w, (⟦z⟧ : Quotient (Perm.SameCycle.setoid π)) = ⟦w⟧ ↔ π.SameCycle z w :=
      fun z w => Quotient.eq
    have e' : ∀ z w, (⟦z⟧ : Quotient (Perm.SameCycle.setoid (swap a b * π))) = ⟦w⟧ ↔
        (swap a b * π).SameCycle z w := fun z w => Quotient.eq
    simp only [Quotient.map_mk, id, e, e']
    rw [sameCycle_swap_mul_iff hab]
    constructor
    · rintro (h | ⟨hx, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hx.imp Perm.SameCycle.symm Perm.SameCycle.symm,
          hy.imp Perm.SameCycle.symm Perm.SameCycle.symm⟩
    · rintro (h | ⟨hx, hy⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hx.imp Perm.SameCycle.symm Perm.SameCycle.symm,
          hy.imp Perm.SameCycle.symm Perm.SameCycle.symm⟩

/-- **The word of a merged cycle**, read from `a`, is the word of the cycle of `a` followed by
the word of the cycle of `b`. -/
theorem cycleWord_swap_mul {M : Type*} [Monoid M] (f : D → M) (hab : ¬ π.SameCycle a b) :
    cycleWord (swap a b * π) f a = cycleWord π f a * cycleWord π f b := by
  unfold cycleWord
  rw [minimalPeriod_swap_mul hab, List.range_add, List.map_append, List.prod_append,
    List.map_map]
  congr 1
  · refine congrArg List.prod (List.map_congr_left fun k hk => ?_)
    rw [swap_mul_pow_apply_of_lt hab (List.mem_range.mp hk)]
  · refine congrArg List.prod (List.map_congr_left fun j hj => ?_)
    simp only [Function.comp_apply]
    rw [swap_mul_pow_add_apply hab (List.mem_range.mp hj)]

end Merge

end TheoremA.Picture
