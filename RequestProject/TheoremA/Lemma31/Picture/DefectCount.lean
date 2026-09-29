module

public import RequestProject.TheoremA.Lemma31.Picture.DefectConsolidate
public import RequestProject.TheoremA.Lemma31.EulerCounting

/-!
# Degree and face bounds, and the Euler count (Sections 6–8)

Let `M, lab` be a least defect of a non-positively curved cone complex of groups `C`.

* **Section 6** (`IsLeastDefect.σσ_ne`): an *ordinary* triple vertex has degree at least three.
  At a degree-two ordinary triple vertex the two neighbours have different index types
  (Section 5), the two labels lie in the corresponding incidence images and multiply to `1`, so by
  the pairwise-trivial-intersection part of `NPC` they are trivial, contradicting Section 4.
* **Section 7** (`IsLeastDefect.twelve_le_faceLength`): every face has at least twelve darts.  The
  types of the darts `d, φ d, φ² d, …` of a face form a closed walk in the incidence graph
  (`faceWalk`), which is non-backtracking by Section 5 applied at the darts `α (φʲ d)`; its length
  is the length of the face, so the girth bound of `NPC` applies
  (`SimpleGraph.egirth_le_length_of_nonBacktracking`).
* **Section 8** (`IsLeastDefect.false`): with `V = Σ_d 1/deg d`, `E = Σ_d 1/2`, `F = Σ_d 1/len d`
  (`numOrbits_eq_sum_inv`), the bounds `1/deg ≤ 1/2` at ordinary index darts, `1/deg ≤ 1/3` at
  ordinary triple darts, `1/len ≤ 1/12`, the pairing of index and triple darts by `α`, and
  `Σ_{d at the exceptional vertex} 1/deg d = 1` give `χ ≤ 1`, contradicting `χ = 2`.  The
  exceptional vertex may be of either kind; no degree bound is used there.

Main result: `ConeComplex.no_nonidentity_defect_of_npc` — under `NPC` there is no defect picture
with nonidentity defect, of any type.
-/

@[expose] public section

namespace TheoremA

universe u w

open Equiv Function

namespace Picture

/-! ### Counting orbits by periods -/

section Orbits

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The cycle of `x` has `minimalPeriod π x` elements. -/
theorem card_sameCycle_eq (π : Perm D) (x : D) :
    (Finset.univ.filter (fun y => π.SameCycle x y)).card = minimalPeriod π x := by
  have hpos := minimalPeriod_perm_pos π x
  have e : Finset.univ.filter (fun y => π.SameCycle x y) =
      (Finset.range (minimalPeriod π x)).image (fun i => (π ^ i) x) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
    constructor
    · intro h
      obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
      refine ⟨n % minimalPeriod π x, Nat.mod_lt _ hpos, ?_⟩
      rw [Perm.coe_pow, Perm.coe_pow, iterate_mod_minimalPeriod_eq]
    · rintro ⟨i, -, rfl⟩
      exact ⟨i, by simp⟩
  rw [e, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  simp only at hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : (π ^ (j - i)) x = x := (π ^ i).injective (by
      rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hlt.le]; exact hij.symm)
    exact pow_apply_ne_self_of_lt (by omega) (by omega) this
  · have : (π ^ (i - j)) x = x := (π ^ j).injective (by
      rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hlt.le]; exact hij)
    exact pow_apply_ne_self_of_lt (by omega) (by omega) this

theorem minimalPeriod_eq_of_sameCycle {π : Perm D} {x y : D} (h : π.SameCycle x y) :
    minimalPeriod π y = minimalPeriod π x := by
  rw [← card_sameCycle_eq, ← card_sameCycle_eq]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h' => h.trans h', fun h' => h.symm.trans h'⟩

/-- **Orbits by periods**: the number of cycles is `Σ_x 1 / (length of the cycle of x)`. -/
theorem numOrbits_eq_sum_inv (π : Perm D) :
    (numOrbits π : ℚ) = ∑ x, 1 / (minimalPeriod π x : ℚ) := by
  classical
  set Q := Quotient (Perm.SameCycle.setoid π)
  have hcard : numOrbits π = Fintype.card Q := by
    unfold numOrbits; exact Nat.card_eq_fintype_card
  rw [hcard]
  rw [← Finset.sum_fiberwise Finset.univ (fun x => (Quotient.mk _ x : Q))]
  rw [Finset.card_univ.symm, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨x0, rfl⟩ := Quotient.exists_rep q
  have hfib : ∀ x ∈ Finset.univ.filter (fun x => (Quotient.mk _ x : Q) = Quotient.mk _ x0),
      (1 : ℚ) / (minimalPeriod π x : ℚ) = 1 / (minimalPeriod π x0 : ℚ) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [minimalPeriod_eq_of_sameCycle (Quotient.exact hx).symm]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter (fun x => (Quotient.mk _ x : Q) = Quotient.mk _ x0)).card =
      minimalPeriod π x0 := by
    rw [← card_sameCycle_eq]
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h' => (Quotient.exact h').symm, fun h' => Quotient.sound h'.symm⟩
  rw [hc]
  have : (minimalPeriod π x0 : ℚ) ≠ 0 := by exact_mod_cast (minimalPeriod_perm_pos π x0).ne'
  field_simp
  simp

/-- The darts of one cycle contribute `1` to `Σ_x 1 / (length of the cycle of x)`. -/
theorem sum_inv_sameCycle (π : Perm D) (b : D) :
    ∑ x ∈ Finset.univ.filter (fun y => π.SameCycle b y), (1 : ℚ) / (minimalPeriod π x : ℚ) = 1 := by
  have hfib : ∀ x ∈ Finset.univ.filter (fun y => π.SameCycle b y),
      (1 : ℚ) / (minimalPeriod π x : ℚ) = 1 / (minimalPeriod π b : ℚ) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [minimalPeriod_eq_of_sameCycle hx]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul, card_sameCycle_eq]
  have : (minimalPeriod π b : ℚ) ≠ 0 := by exact_mod_cast (minimalPeriod_perm_pos π b).ne'
  field_simp

end Orbits

end Picture

end TheoremA

/-! ### Walks from sequences -/

namespace SimpleGraph

variable {W : Type*} {G : SimpleGraph W}

/-- The walk `f 0, f 1, …, f n` along a sequence with consecutive terms adjacent. -/
def walkOfSeq : (f : ℕ → W) → (∀ j, G.Adj (f j) (f (j + 1))) → (n : ℕ) → G.Walk (f 0) (f n)
  | _, _, 0 => Walk.nil
  | f, h, n + 1 => Walk.cons (h 0) (walkOfSeq (fun j => f (j + 1)) (fun j => h (j + 1)) n)

theorem walkOfSeq_length (f : ℕ → W) (h : ∀ j, G.Adj (f j) (f (j + 1))) (n : ℕ) :
    (walkOfSeq f h n).length = n := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp [walkOfSeq, ih]

theorem walkOfSeq_getVert (f : ℕ → W) (h : ∀ j, G.Adj (f j) (f (j + 1))) (n : ℕ) :
    ∀ i ≤ n, (walkOfSeq f h n).getVert i = f i := by
  induction n generalizing f with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := by omega
    rfl
  | succ n ih =>
    intro i hi
    cases i with
    | zero => rfl
    | succ i =>
      simp only [walkOfSeq]
      rw [Walk.getVert_cons_succ]
      exact ih (fun j => f (j + 1)) (fun j => h (j + 1)) i (by omega)

end SimpleGraph

namespace TheoremA

universe u w

open Equiv Function

namespace ConeComplex

open Picture

variable {V T : Type w} {C : ConeComplex.{u, w} V T}

namespace IsLeastDefect

variable {M : CombMap} {lab : M.D → C.Letter} (h : C.IsLeastDefect M lab) (hC : C.NPC)

include h hC

/-- **Section 6: ordinary triple vertices have degree at least three.** -/
theorem σσ_ne (d : M.D) (hT : (lab d).1.isLeft = false)
    (hord : cycleWord M.σ (C.letterWord ∘ lab) d = 1) : M.σ (M.σ d) ≠ d := by
  intro h2
  have hde := h.σ_ne hC d
  rw [cycleWord_of_apply_apply _ _ d hde h2] at hord
  have orient : ∀ x, (lab x).1.isLeft = false → C.RelEdge (lab (M.α x)) (lab x) := by
    intro x hx
    rcases h.1.edge x with he | he
    · rw [(relEdge_isLeft he).1] at hx; exact absurd hx (by simp)
    · exact he
  have hT' : (lab (M.σ d)).1.isLeft = false := by rw [h.1.type_σ]; exact hT
  obtain ⟨i, t, hit, a, hd1, hd2⟩ := orient d hT
  obtain ⟨j, t', hjt, b, he1, he2⟩ := orient (M.σ d) hT'
  have htt : t' = t := by
    have := h.1.type_σ d
    rw [hd2, he2] at this
    simpa using this
  subst htt
  have hij : j ≠ i := by
    have := h.type_α_σ_ne hC d
    rw [hd1, he1] at this
    intro e
    subst e
    exact this rfl
  have hw : (C.φ i t' hit a)⁻¹ * (C.φ j t' hjt b)⁻¹ = 1 := by
    simp only [Function.comp_apply, hd2, he2] at hord
    refine Monoid.CoprodI.of_injective (M := C.loc) (i := Sum.inr t') ?_
    rw [map_mul, map_one]
    exact hord
  have hb : C.φ j t' hjt b = C.φ i t' hit a⁻¹ := by
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_left (by rw [← mul_inv_rev] at hw; exact inv_eq_one.1 hw))
  have hb1 : b = 1 := hC.inter_trivial j i t' hjt hit hij b a⁻¹ hb
  apply h.letterWord_ne_one hC (M.α (M.σ d))
  rw [he1, hb1]
  exact letterWord_mk_one _

/-- The types of the darts of a face. -/
def faceSeq (M : CombMap) (lab : M.D → C.Letter) (d : M.D) (j : ℕ) : V ⊕ T :=
  (lab ((M.φ ^ j) d)).1

omit hC in
theorem faceSeq_adj (d : M.D) (j : ℕ) :
    C.graph.Adj (faceSeq M lab d j) (faceSeq M lab d (j + 1)) := by
  have e : faceSeq M lab d (j + 1) = (lab (M.α ((M.φ ^ j) d))).1 := by
    unfold faceSeq
    rw [pow_succ', Perm.mul_apply]
    exact h.1.type_σ _
  rw [e]
  unfold faceSeq
  rcases h.1.edge ((M.φ ^ j) d) with ⟨v, t, hvt, a, h1, h2⟩ | ⟨v, t, hvt, a, h1, h2⟩
  · rw [h1, h2]; exact hvt
  · rw [h1, h2]; exact hvt

theorem faceSeq_ne (d : M.D) (j : ℕ) : faceSeq M lab d (j + 2) ≠ faceSeq M lab d j := by
  set x := (M.φ ^ j) d with hx
  have e1 : faceSeq M lab d (j + 2) = (lab (M.α (M.σ (M.α x)))).1 := by
    unfold faceSeq
    rw [show j + 2 = (j + 1) + 1 from rfl, pow_succ', Perm.mul_apply, pow_succ', Perm.mul_apply,
      ← hx]
    change (lab (M.σ (M.α (M.σ (M.α x))))).1 = _
    exact h.1.type_σ _
  have e2 : faceSeq M lab d j = (lab (M.α (M.α x))).1 := by
    unfold faceSeq; rw [M.α_α]
  rw [e1, e2]
  exact h.type_α_σ_ne hC (M.α x)

/-- **Section 7: every face has at least twelve darts.** -/
theorem twelve_le_faceLength (d : M.D) : 12 ≤ minimalPeriod M.φ d := by
  set n := minimalPeriod M.φ d with hn
  have hpos : 0 < n := minimalPeriod_perm_pos _ _
  have hclosed : faceSeq M lab d n = faceSeq M lab d 0 := by
    unfold faceSeq
    rw [hn, pow_minimalPeriod_apply, pow_zero, Perm.one_apply]
  let p := (SimpleGraph.walkOfSeq (faceSeq M lab d) (faceSeq_adj h d) n).copy rfl hclosed
  have hlen : p.length = n := by
    simp only [p, SimpleGraph.Walk.length_copy, SimpleGraph.walkOfSeq_length]
  have hnb : p.NonBacktracking := by
    intro i hi
    rw [hlen] at hi
    simp only [p, SimpleGraph.Walk.getVert_copy]
    rw [SimpleGraph.walkOfSeq_getVert _ _ n _ hi, SimpleGraph.walkOfSeq_getVert _ _ n _ (by omega)]
    exact faceSeq_ne h hC d i
  have hg := SimpleGraph.egirth_le_length_of_nonBacktracking p hnb (by omega)
  rw [hlen] at hg
  have := hC.girth.trans hg
  exact_mod_cast this

/-- **Section 8: the Euler count.**  A least defect of a non-positively curved cone complex of
groups does not exist. -/
theorem false : False := by
  classical
  obtain ⟨b0, hb0, hexc⟩ := h.1.exc
  set n : ℚ := (Fintype.card M.D : ℚ) with hn
  have hsum_const : ∀ c : ℚ, ∑ _x : M.D, c = n * c := fun c => by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- periods
  have hV := numOrbits_eq_sum_inv M.σ
  have hE := numOrbits_eq_sum_inv M.α
  have hF := numOrbits_eq_sum_inv M.φ
  have hα2 : ∀ x, minimalPeriod M.α x = 2 := fun x =>
    minimalPeriod_eq_of (by norm_num) (by rw [pow_two, Perm.mul_apply, M.α_α]) fun k hk hk' => by
      obtain rfl : k = 1 := by omega
      rw [pow_one]; exact M.α_ne x
  -- bounds
  set c : M.D → ℚ := fun x => if (lab x).1.isLeft then 1 / 2 else 1 / 3 with hc
  have hdeg : ∀ x, (1 : ℚ) / (minimalPeriod M.σ x : ℚ) ≤
      c x + if M.σ.SameCycle b0 x then 1 / (minimalPeriod M.σ x : ℚ) else 0 := by
    intro x
    have hc0 : 0 ≤ c x := by simp only [hc]; split_ifs <;> norm_num
    by_cases hx : M.σ.SameCycle b0 x
    · rw [if_pos hx]; linarith
    rw [if_neg hx, add_zero]
    have hord : cycleWord M.σ (C.letterWord ∘ lab) x = 1 := by
      by_contra hne; exact hx (hexc x hne)
    have h1 : minimalPeriod M.σ x ≠ 1 := fun e => h.σ_ne hC x (by
      have := pow_minimalPeriod_apply M.σ x; rwa [e, pow_one] at this)
    have hp := minimalPeriod_perm_pos M.σ x
    simp only [hc]
    split_ifs with hk
    · have h2 : (2 : ℚ) ≤ minimalPeriod M.σ x := by exact_mod_cast (show 2 ≤ _ by omega)
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    · have h2 : minimalPeriod M.σ x ≠ 2 := fun e => h.σσ_ne hC x (by simpa using hk) hord (by
        have := pow_minimalPeriod_apply M.σ x; rwa [e, pow_two, Perm.mul_apply] at this)
      have h3 : (3 : ℚ) ≤ minimalPeriod M.σ x := by exact_mod_cast (show 3 ≤ _ by omega)
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hface : ∀ x, (1 : ℚ) / (minimalPeriod M.φ x : ℚ) ≤ 1 / 12 := by
    intro x
    have h12 : (12 : ℚ) ≤ minimalPeriod M.φ x := by exact_mod_cast h.twelve_le_faceLength hC x
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  -- the pairing of index and triple darts
  have hcsum : ∑ x, c x = n * (5 / 12) := by
    have hperm : ∑ x, c (M.α x) = ∑ x, c x := Equiv.sum_comp M.α c
    have hpair : ∀ x, c x + c (M.α x) = 5 / 6 := by
      intro x
      simp only [hc, h.1.kind_α x]
      cases (lab x).1.isLeft <;> norm_num
    have : ∑ x, (c x + c (M.α x)) = n * (5 / 6) := by
      rw [Finset.sum_congr rfl fun x _ => hpair x, hsum_const]
    rw [Finset.sum_add_distrib, hperm] at this
    linarith
  have hexcsum : ∑ x, (if M.σ.SameCycle b0 x then 1 / (minimalPeriod M.σ x : ℚ) else 0) = 1 := by
    rw [← Finset.sum_filter]
    exact sum_inv_sameCycle M.σ b0
  have hVle : (numOrbits M.σ : ℚ) ≤ n * (5 / 12) + 1 := by
    rw [hV]
    calc ∑ x, (1 : ℚ) / (minimalPeriod M.σ x : ℚ)
        ≤ ∑ x, (c x + if M.σ.SameCycle b0 x then 1 / (minimalPeriod M.σ x : ℚ) else 0) :=
          Finset.sum_le_sum fun x _ => hdeg x
      _ = n * (5 / 12) + 1 := by rw [Finset.sum_add_distrib, hcsum, hexcsum]
  have hEeq : (numOrbits M.α : ℚ) = n * (1 / 2) := by
    rw [hE, ← hsum_const]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hα2]; norm_num
  have hFle : (numOrbits M.φ : ℚ) ≤ n * (1 / 12) := by
    rw [hF, ← hsum_const]
    exact Finset.sum_le_sum fun x _ => hface x
  have hχ := h.1.spherical
  unfold CombMap.euler CombMap.numVertices CombMap.numEdges CombMap.numFaces at hχ
  have hχq : ((numOrbits M.σ : ℤ) : ℚ) - (numOrbits M.α : ℤ) + (numOrbits M.φ : ℤ) = 2 := by
    exact_mod_cast hχ
  push_cast at hχq
  linarith

end IsLeastDefect

/-- **No nonidentity defect under `NPC`.**  In a non-positively curved cone complex of groups
there is no defect picture, of any local type (index or triple), whose defect is nonidentity. -/
theorem no_nonidentity_defect_of_npc (hC : C.NPC) {s : V ⊕ T} {P : C.loc s}
    (Δ : C.DefectPicture s P) : P = 1 := by
  by_contra hP
  obtain ⟨M, lab, hL⟩ := exists_isLeastDefect_of_defectPicture Δ hP
  exact hL.false hC

/-- **Developability at the index vertices, from the geometric argument.**  In a non-positively
curved cone complex of groups every index group embeds in the colimit. -/
theorem NPC.ι_inl_injective (hC : C.NPC) (v : V) : Function.Injective (C.ι (Sum.inl v)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  by_contra hne
  obtain ⟨s, P, hP, ⟨Δ⟩⟩ := exists_defectPicture_of_ι_eq_one hne ha
  exact hP (no_nonidentity_defect_of_npc hC Δ)

end ConeComplex

end TheoremA
