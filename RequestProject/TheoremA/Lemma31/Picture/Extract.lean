module

public import RequestProject.TheoremA.Lemma31.Picture.Cap
public import RequestProject.TheoremA.Lemma31.Picture.Components

/-!
# Same-face split extraction with a strict size bound

Let `R` be a raw picture and split an **interior** vertex of `R` at distinct darts `a`, `b` of the
same vertex and of the same face.  By `CombMap.split_sameFace_spherical` the split map `S` has two
connected components of `χ = 2`: `M_o = S.component R.base` (the component of the marked vertex)
and `M_u = S.componentCompl R.base`.  The split vertex has one piece in each of them:
`RawPicture.splitU` is the one of `a`, `b` in `M_u` and `RawPicture.splitO` the one in `M_o`.

* `RawPicture.splitQ` : the product `Q` at the `u`-piece (read from `splitU`), as an element of
  the local group `H_t`, `t = (R.lab a).1`, of the split vertex (`splitQ_spec`);
  `RawPicture.split_word_o` : the product at the `o`-piece, read from `splitO`, is `Q⁻¹`.
* **Case `Q = 1`** (`RawPicture.splitRetain`) : `M_o` with the original mark and labels is a raw
  picture for the same element, with strictly fewer edges (`splitRetain_numEdges_lt`).
* **Case `Q ≠ 1`** (`RawPicture.splitDefect`) : `M_u` with the restricted labels is a
  `DefectPicture` of type `t` and product `Q`; capping it (`DefectPicture.cap`) gives a raw
  picture for the single letter `Q` with `E(M_u) + 1` edges; if `E(M_o) ≥ 2` this is at most
  `E(R) - 1` (`splitDefect_cap_numEdges_add_one_le`).
* `RawPicture.sameFace_extract` : the two-case statement.

The local group `H_t` of the second case can differ from the group of the marked word and can be
a `B t` rather than an `A v`.  Nonidentity of the new marked word comes from injectivity of the
local factor into the **free product** (`DefectPicture.cap_word_ne_one`).
-/

@[expose] public section

namespace TheoremA

namespace Picture

open Equiv Function

/-! ### Restrictions: iterates, cycles, words and edge counts -/

theorem numOrbits_pos {D : Type*} [Finite D] (π : Perm D) (d : D) : 0 < numOrbits π := by
  unfold numOrbits
  haveI : Nonempty (Quotient (Perm.SameCycle.setoid π)) := ⟨⟦d⟧⟩
  exact Nat.card_pos

theorem two_le_numOrbits {D : Type*} [Finite D] (π : Perm D) {d e : D} (h : ¬ π.SameCycle d e) :
    2 ≤ numOrbits π := by
  unfold numOrbits
  haveI : Nontrivial (Quotient (Perm.SameCycle.setoid π)) :=
    ⟨⟨⟦d⟧, ⟦e⟧, fun he => h (Quotient.exact he)⟩⟩
  exact Finite.one_lt_card_iff_nontrivial.2 this

namespace CombMap

variable {M : CombMap} (p : M.D → Prop) [DecidablePred p] (hσ : ∀ x, p (M.σ x) ↔ p x)
  (hα : ∀ x, p (M.α x) ↔ p x)

theorem restrict_σ_pow_val (x : (M.restrict p hσ hα).D) (n : ℕ) :
    (((M.restrict p hσ hα).σ ^ n) x).val = (M.σ ^ n) x.val := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, pow_succ', Perm.mul_apply, ← ih]; rfl

theorem restrict_sameCycle_iff {x y : (M.restrict p hσ hα).D} :
    (M.restrict p hσ hα).σ.SameCycle x y ↔ M.σ.SameCycle x.val y.val :=
  Perm.sameCycle_subtypePerm (h := hσ)

theorem restrict_α_sameCycle_iff {x y : (M.restrict p hσ hα).D} :
    (M.restrict p hσ hα).α.SameCycle x y ↔ M.α.SameCycle x.val y.val :=
  Perm.sameCycle_subtypePerm (h := hα)

/-- The word around a vertex of a restriction is the word around the same vertex of `M`. -/
theorem restrict_cycleWord {G : Type*} [Monoid G] (f : M.D → G) (x : (M.restrict p hσ hα).D) :
    cycleWord (M.restrict p hσ hα).σ (f ∘ Subtype.val) x = cycleWord M.σ f x.val := by
  unfold cycleWord
  have hmp : minimalPeriod (M.restrict p hσ hα).σ x = minimalPeriod M.σ x.val := by
    refine minimalPeriod_eq_of (minimalPeriod_perm_pos _ _) ?_ ?_
    · exact Subtype.ext (by rw [restrict_σ_pow_val]; exact pow_minimalPeriod_apply _ _)
    · intro k hk hk' h
      exact pow_apply_ne_self_of_lt hk hk' (by rw [← restrict_σ_pow_val, h])
  rw [hmp]
  simp only [Function.comp_apply, restrict_σ_pow_val]

/-- Edges are counted separately on an invariant set and on its complement. -/
theorem numEdges_restrict_add : M.numEdges = (M.restrict p hσ hα).numEdges +
    (M.restrict (fun x => ¬ p x) (not_invariant_σ p hσ) (not_invariant_α p hα)).numEdges :=
  numOrbits_subtypePerm_add M.α p hα

variable (M) (c : M.D)

theorem numEdges_component_add :
    M.numEdges = (M.component c).numEdges + (M.componentCompl c).numEdges := by
  classical
  exact numEdges_restrict_add _ (M.component_invariant_σ c) (M.component_invariant_α c)

variable {M} {a b : M.D}

/-- After a same-face split of a spherical map, the component of any dart and its complement are
both connected spheres. -/
theorem split_sameFace_component (hM : M.Connected) (hχ : M.euler = 2) (hab : a ≠ b)
    (hσ : M.σ.SameCycle a b) (hφ : M.φ.SameCycle a b) (c : M.D) :
    ((M.split a b).component c).euler = 2 ∧ ((M.split a b).componentCompl c).Connected ∧
      ((M.split a b).componentCompl c).euler = 2 := by
  obtain ⟨hdis, h4, hreach, -⟩ := split_sameFace_spherical hM hχ hab hσ hφ
  have hc1 := (M.split a b).component_connected c
  have hc2 : ((M.split a b).componentCompl c).Connected := by
    rcases hreach c with hca | hcb
    · refine (M.split a b).componentCompl_connected c b
        (fun h => hdis (hca.trans _ _ _ h)) fun y hy => ?_
      rcases hreach y with hy' | hy'
      · exact absurd ((hca.symm _ _).trans _ _ _ hy') hy
      · exact hy'
    · refine (M.split a b).componentCompl_connected c a
        (fun h => hdis ((hcb.trans _ _ _ h).symm _ _)) fun y hy => ?_
      rcases hreach y with hy' | hy'
      · exact hy'
      · exact absurd ((hcb.symm _ _).trans _ _ _ hy') hy
  have hadd := (M.split a b).euler_component_add c
  have hle1 := ((M.split a b).component c).euler_le_two hc1
  have hle2 := ((M.split a b).componentCompl c).euler_le_two hc2
  refine ⟨?_, hc2, ?_⟩ <;> omega

end CombMap

end Picture

universe u w

namespace ConeComplex

open Picture Equiv Function

variable {V T : Type w} {C : ConeComplex.{u, w} V T}

/-- A cycle whose letters all lie in the local group `t` has its word in the image of that
local group in the free product. -/
theorem exists_cycleWord_eq_letter {D : Type*} [Finite D] (π : Perm D) (lab : D → C.Letter)
    (t : V ⊕ T) (x : D) (h : ∀ n : ℕ, (lab ((π ^ n) x)).1 = t) :
    ∃ Q : C.loc t, cycleWord π (C.letterWord ∘ lab) x = C.letterWord ⟨t, Q⟩ := by
  have hmem : cycleWord π (C.letterWord ∘ lab) x ∈
      MonoidHom.mrange (Monoid.CoprodI.of (M := C.loc) (i := t)) := by
    unfold cycleWord
    refine Submonoid.list_prod_mem _ fun y hy => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    have hi := h i
    rcases hl : lab ((π ^ i) x) with ⟨k, g⟩
    rw [hl] at hi
    subst hi
    refine ⟨g, ?_⟩
    simp only [Function.comp_apply, hl]
    rfl
  obtain ⟨Q, hQ⟩ := hmem
  exact ⟨Q, hQ.symm⟩

namespace RawPicture

variable {x : Monoid.CoprodI C.loc} (R : C.RawPicture x) {a b : R.M.D}

/-! ### Labels of an interior split -/

/-- Letter types are constant around every interior vertex of the split map. -/
theorem split_type_σ (hσ : R.M.σ.SameCycle a b) (hint : ¬ R.M.σ.SameCycle R.base a) {d : R.M.D}
    (hd : ¬ (R.M.split a b).σ.SameCycle R.base d) :
    (R.lab ((R.M.split a b).σ d)).1 = (R.lab d).1 := by
  rw [RawPicture.split_sameCycle_base_iff hint hσ] at hd
  show (R.lab (swap a b (R.M.σ d))).1 = (R.lab d).1
  have hd1 : ∀ e, R.M.σ d = e → R.M.σ.SameCycle d e := fun e he => ⟨1, by simpa using he⟩
  by_cases ha : R.M.σ d = a
  · rw [ha, swap_apply_left]
    exact R.type_eq_of_sameCycle hd ((hd1 a ha).trans hσ)
  · by_cases hb : R.M.σ d = b
    · rw [hb, swap_apply_right]
      exact R.type_eq_of_sameCycle hd ((hd1 b hb).trans hσ.symm)
    · rw [swap_apply_of_ne_of_ne ha hb]
      exact R.type_σ d hd

/-- Interior vertices of the split map other than the two new pieces keep product `1`. -/
theorem split_local_eq (hσ : R.M.σ.SameCycle a b) (hint : ¬ R.M.σ.SameCycle R.base a)
    {d : R.M.D} (hd : ¬ (R.M.split a b).σ.SameCycle R.base d)
    (hda : ¬ (R.M.split a b).σ.SameCycle a d) (hdb : ¬ (R.M.split a b).σ.SameCycle b d) :
    cycleWord (R.M.split a b).σ (C.letterWord ∘ R.lab) d = 1 := by
  rw [RawPicture.split_sameCycle_base_iff hint hσ] at hd
  have hpow : ∀ n : ℕ, (R.M.σ ^ n) d = ((R.M.split a b).σ ^ n) d := by
    intro n
    have := swap_mul_pow_apply_of_not_sameCycle hda hdb n
    rwa [CombMap.split_σ, swap_mul_swap_mul] at this
  rw [cycleWord_congr _ (fun n => (hpow n).symm)]
  exact R.local_eq d hd

/-- A dart not connected to the marked vertex in the split map is interior in `R`. -/
theorem split_interior_of_not_conn (hσ : R.M.σ.SameCycle a b)
    (hint : ¬ R.M.σ.SameCycle R.base a) {d : R.M.D}
    (hd : ¬ Relation.EqvGen (R.M.split a b).Step R.base d) :
    ¬ (R.M.split a b).σ.SameCycle R.base d ∧ ¬ R.M.σ.SameCycle R.base d := by
  have h1 : ¬ (R.M.split a b).σ.SameCycle R.base d :=
    fun h => hd ((R.M.split a b).eqvGen_of_sameCycle h)
  exact ⟨h1, by rwa [RawPicture.split_sameCycle_base_iff hint hσ] at h1⟩

/-! ### The two pieces of the split vertex -/

variable (a b)

open Classical in
/-- The piece of the split vertex lying in the component **not** containing the mark. -/
noncomputable def splitU : R.M.D :=
  if Relation.EqvGen (R.M.split a b).Step R.base a then b else a

open Classical in
/-- The piece of the split vertex lying in the component containing the mark. -/
noncomputable def splitO : R.M.D :=
  if Relation.EqvGen (R.M.split a b).Step R.base a then a else b

variable {a b}

theorem splitU_splitO : (R.splitU a b = a ∧ R.splitO a b = b) ∨
    (R.splitU a b = b ∧ R.splitO a b = a) := by
  unfold splitU splitO
  split_ifs
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

theorem splitO_conn : Relation.EqvGen (R.M.split a b).Step R.base (R.splitO a b) := by
  unfold splitO
  split_ifs with h
  · exact h
  · rcases CombMap.split_reach (a := a) (b := b) R.connected R.base with h' | h'
    · exact absurd (h'.symm _ _) h
    · exact h'.symm _ _

section Pieces

variable (hab : a ≠ b) (hσ : R.M.σ.SameCycle a b) (hφ : R.M.φ.SameCycle a b)

include hab hσ hφ

theorem split_not_conn_ab : ¬ Relation.EqvGen (R.M.split a b).Step a b :=
  (CombMap.split_sameFace_spherical R.connected R.spherical hab hσ hφ).1

theorem splitU_not_conn : ¬ Relation.EqvGen (R.M.split a b).Step R.base (R.splitU a b) := by
  have hdis := R.split_not_conn_ab hab hσ hφ
  unfold splitU
  split_ifs with h
  · exact fun h' => hdis ((h.symm _ _).trans _ _ _ h')
  · exact h

end Pieces

variable (a b) in
open Classical in
/-- The product `Q` at the piece of the split vertex outside the marked component, read from
`splitU`, as an element of the local group of the split vertex (`1` if not defined, which does
not happen under the hypotheses of `splitQ_spec`). -/
noncomputable def splitQ : C.loc (R.lab a).1 :=
  if h : ∃ Q : C.loc (R.lab a).1, cycleWord (R.M.split a b).σ (C.letterWord ∘ R.lab)
      (R.splitU a b) = C.letterWord ⟨(R.lab a).1, Q⟩ then h.choose else 1

section Spec

open Classical

variable (hab : a ≠ b) (hσ : R.M.σ.SameCycle a b) (hφ : R.M.φ.SameCycle a b)
  (hint : ¬ R.M.σ.SameCycle R.base a)

include hab hσ hφ hint

theorem splitU_type_pow (n : ℕ) :
    (R.lab (((R.M.split a b).σ ^ n) (R.splitU a b))).1 = (R.lab a).1 := by
  have hu := R.split_interior_of_not_conn hσ hint (R.splitU_not_conn hab hσ hφ)
  induction n with
  | zero =>
    rcases R.splitU_splitO with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [pow_zero, Perm.one_apply, h]
    exact R.type_eq_of_sameCycle hint hσ
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, R.split_type_σ hσ hint, ih]
    intro h
    exact hu.1 (h.trans (sameCycle_of_pow_eq n rfl).symm)

/-- The product at the `u`-piece is the letter `Q = splitQ` of the local group of the split
vertex. -/
theorem splitQ_spec : cycleWord (R.M.split a b).σ (C.letterWord ∘ R.lab) (R.splitU a b) =
    C.letterWord ⟨(R.lab a).1, R.splitQ a b⟩ := by
  have h := exists_cycleWord_eq_letter (R.M.split a b).σ R.lab (R.lab a).1 (R.splitU a b)
    (R.splitU_type_pow hab hσ hφ hint)
  unfold splitQ
  rw [dif_pos h]
  exact h.choose_spec

/-- The product at the `o`-piece, read from `splitO`, is `Q⁻¹`. -/
theorem split_word_o : cycleWord (R.M.split a b).σ (C.letterWord ∘ R.lab) (R.splitO a b) =
    (C.letterWord ⟨(R.lab a).1, R.splitQ a b⟩)⁻¹ := by
  have hold := CombMap.split_cycleWord (C.letterWord ∘ R.lab) hab hσ
  rw [R.local_eq a hint] at hold
  rw [← R.splitQ_spec hab hσ hφ hint]
  rcases R.splitU_splitO with ⟨hu, ho⟩ | ⟨hu, ho⟩ <;> rw [hu, ho]
  · exact (eq_inv_of_mul_eq_one_right hold.symm)
  · exact (eq_inv_of_mul_eq_one_left hold.symm)

/-- If `Q = 1`, both new pieces have product `1`. -/
theorem split_words_one (hQ : R.splitQ a b = 1) :
    cycleWord (R.M.split a b).σ (C.letterWord ∘ R.lab) a = 1 ∧
    cycleWord (R.M.split a b).σ (C.letterWord ∘ R.lab) b = 1 := by
  have hu := R.splitQ_spec hab hσ hφ hint
  have ho := R.split_word_o hab hσ hφ hint
  rw [hQ] at hu ho
  have h1 : C.letterWord ⟨(R.lab a).1, 1⟩ = 1 := map_one _
  rw [h1] at hu ho
  rw [inv_one] at ho
  rcases R.splitU_splitO with ⟨eu, eo⟩ | ⟨eu, eo⟩ <;> rw [eu] at hu <;> rw [eo] at ho
  · exact ⟨hu, ho⟩
  · exact ⟨ho, hu⟩

/-! ### Case `Q = 1`: keep the marked component -/

/-- **Case `Q = 1`.**  The component of the mark, with the original mark and labels, is a raw
picture for the same element. -/
noncomputable def splitRetain (hQ : R.splitQ a b = 1) : C.RawPicture x where
  M := (R.M.split a b).component R.base
  lab := R.lab ∘ Subtype.val
  base := ⟨R.base, Relation.EqvGen.refl _⟩
  connected := (R.M.split a b).component_connected _
  spherical := (CombMap.split_sameFace_component R.connected R.spherical hab hσ hφ R.base).1
  type_σ := by
    intro d hd
    have hd' : ¬ (R.M.split a b).σ.SameCycle R.base d.val := fun h =>
      hd ((CombMap.restrict_sameCycle_iff _ _ _).2 h)
    exact R.split_type_σ hσ hint hd'
  local_eq := by
    intro d hd
    have hd' : ¬ (R.M.split a b).σ.SameCycle R.base d.val := fun h =>
      hd ((CombMap.restrict_sameCycle_iff _ _ _).2 h)
    have e := CombMap.restrict_cycleWord (M := R.M.split a b) _ _ _ (C.letterWord ∘ R.lab) d
    refine e.trans ?_
    obtain ⟨ha, hb⟩ := R.split_words_one hab hσ hφ hint hQ
    by_cases hda : (R.M.split a b).σ.SameCycle a d.val
    · exact cycleWord_eq_one_of_sameCycle _ hda ha
    by_cases hdb : (R.M.split a b).σ.SameCycle b d.val
    · exact cycleWord_eq_one_of_sameCycle _ hdb hb
    exact R.split_local_eq hσ hint hd' hda hdb
  edge_interior := by
    intro d hd hd'
    have h1 : ¬ R.M.σ.SameCycle R.base d.val := by
      rw [← RawPicture.split_sameCycle_base_iff hint hσ]
      exact fun h => hd ((CombMap.restrict_sameCycle_iff _ _ _).2 h)
    have h2 : ¬ R.M.σ.SameCycle R.base (R.M.α d.val) := by
      rw [← RawPicture.split_sameCycle_base_iff hint hσ]
      exact fun h => hd' ((CombMap.restrict_sameCycle_iff _ _ _).2 h)
    exact R.edge_interior d.val h1 h2
  edge_boundary := by
    intro d hd
    have h1 : R.M.σ.SameCycle R.base d.val := by
      rw [← RawPicture.split_sameCycle_base_iff hint hσ]
      exact (CombMap.restrict_sameCycle_iff _ _ _).1 hd
    obtain ⟨h2, h3⟩ := R.edge_boundary d.val h1
    refine ⟨fun h => h2 ?_, h3⟩
    rw [← RawPicture.split_sameCycle_base_iff hint hσ]
    exact (CombMap.restrict_sameCycle_iff _ _ _).1 h
  boundary_word := by
    refine (CombMap.restrict_cycleWord (M := R.M.split a b) _ _ _ (C.letterWord ∘ R.lab)
      ⟨R.base, _⟩).trans ?_
    exact (cycleWord_congr _ (RawPicture.split_pow_of_not (fun h => hint h.symm)
      (fun h => hint (h.symm.trans hσ.symm)))).trans R.boundary_word

theorem splitRetain_numEdges (hQ : R.splitQ a b = 1) :
    (R.splitRetain hab hσ hφ hint hQ).M.numEdges =
      ((R.M.split a b).component R.base).numEdges := rfl

/-- In the case `Q = 1` the retained picture has strictly fewer edges. -/
theorem splitRetain_numEdges_lt (hQ : R.splitQ a b = 1) :
    (R.splitRetain hab hσ hφ hint hQ).M.numEdges < R.M.numEdges := by
  rw [splitRetain_numEdges, ← CombMap.split_numEdges R.M a b,
    CombMap.numEdges_component_add (R.M.split a b) R.base]
  have := numOrbits_pos ((R.M.split a b).componentCompl R.base).α
    ⟨R.splitU a b, R.splitU_not_conn hab hσ hφ⟩
  unfold CombMap.numEdges
  omega

/-! ### Case `Q ≠ 1`: discard the marked component and cap the defect -/

/-- The component not containing the mark, as a defective picture of type `t = (R.lab a).1` and
product `Q = splitQ` at the `u`-piece of the split vertex. -/
noncomputable def splitDefect : C.DefectPicture (R.lab a).1 (R.splitQ a b) where
  M := (R.M.split a b).componentCompl R.base
  lab := R.lab ∘ Subtype.val
  b := ⟨R.splitU a b, R.splitU_not_conn hab hσ hφ⟩
  connected :=
    (CombMap.split_sameFace_component R.connected R.spherical hab hσ hφ R.base).2.1
  spherical :=
    (CombMap.split_sameFace_component R.connected R.spherical hab hσ hφ R.base).2.2
  type_σ := by
    intro d
    exact R.split_type_σ hσ hint (R.split_interior_of_not_conn hσ hint d.2).1
  type_b := by
    have := R.splitU_type_pow hab hσ hφ hint 0
    rwa [pow_zero, Perm.one_apply] at this
  local_eq := by
    intro d hd
    have e := CombMap.restrict_cycleWord (M := R.M.split a b) _ _ _ (C.letterWord ∘ R.lab) d
    refine e.trans ?_
    have hdu : ¬ (R.M.split a b).σ.SameCycle (R.splitU a b) d.val := fun h =>
      hd ((CombMap.restrict_sameCycle_iff _ _ _).2 h)
    have hdo : ¬ (R.M.split a b).σ.SameCycle (R.splitO a b) d.val := fun h =>
      d.2 ((R.splitO_conn).trans _ _ _ ((R.M.split a b).eqvGen_of_sameCycle h))
    have hint' := (R.split_interior_of_not_conn hσ hint d.2).1
    rcases R.splitU_splitO with ⟨eu, eo⟩ | ⟨eu, eo⟩ <;> rw [eu] at hdu <;> rw [eo] at hdo
    · exact R.split_local_eq hσ hint hint' hdu hdo
    · exact R.split_local_eq hσ hint hint' hdo hdu
  defect_word :=
    (CombMap.restrict_cycleWord (M := R.M.split a b) _ _ _ (C.letterWord ∘ R.lab) _).trans
      (R.splitQ_spec hab hσ hφ hint)
  edge := by
    intro d
    have hαd : ¬ Relation.EqvGen (R.M.split a b).Step R.base (R.M.α d.val) :=
      ((R.M.split a b).componentCompl R.base).α d |>.2
    exact R.edge_interior d.val (R.split_interior_of_not_conn hσ hint d.2).2
      (R.split_interior_of_not_conn hσ hint hαd).2

/-- The capped defect has `E(M_u) + 1` edges. -/
theorem splitDefect_cap_numEdges :
    (R.splitDefect hab hσ hφ hint).cap.M.numEdges =
      ((R.M.split a b).componentCompl R.base).numEdges + 1 :=
  (R.splitDefect hab hσ hφ hint).cap_numEdges

/-- If the marked component has at least two edges, the capped defect has at most
`E(R) - 1` edges. -/
theorem splitDefect_cap_numEdges_add_one_le
    (hMo : 2 ≤ ((R.M.split a b).component R.base).numEdges) :
    (R.splitDefect hab hσ hφ hint).cap.M.numEdges + 1 ≤ R.M.numEdges := by
  rw [splitDefect_cap_numEdges, ← CombMap.split_numEdges R.M a b,
    CombMap.numEdges_component_add (R.M.split a b) R.base]
  omega

/-- **Same-face split extraction.**  Split an interior vertex of a raw picture `R` for `x` at
distinct darts `a`, `b` of the same vertex and the same face, and assume the component of the
mark has at least two edges.  Then either

1. (`Q = 1`) there is a raw picture for the same `x` with strictly fewer edges, or
2. (`Q ≠ 1`) there is a raw picture for the single nonidentity letter `Q` of the local group
   `H_t` of the split vertex (`t = (R.lab a).1`) with at most `E(R) - 1` edges.

Here `Q = splitQ` is the product at the piece of the split vertex outside the marked component. -/
theorem sameFace_extract (hMo : 2 ≤ ((R.M.split a b).component R.base).numEdges) :
    (R.splitQ a b = 1 ∧ ∃ R' : C.RawPicture x, R'.M.numEdges < R.M.numEdges) ∨
    (R.splitQ a b ≠ 1 ∧ ∃ R' : C.RawPicture (C.letterWord ⟨(R.lab a).1, R.splitQ a b⟩),
      R'.M.numEdges + 1 ≤ R.M.numEdges) := by
  by_cases hQ : R.splitQ a b = 1
  · exact Or.inl ⟨hQ, R.splitRetain hab hσ hφ hint hQ, R.splitRetain_numEdges_lt hab hσ hφ hint hQ⟩
  · exact Or.inr ⟨hQ, (R.splitDefect hab hσ hφ hint).cap,
      R.splitDefect_cap_numEdges_add_one_le hab hσ hφ hint hMo⟩

end Spec

end RawPicture

end ConeComplex

end TheoremA
