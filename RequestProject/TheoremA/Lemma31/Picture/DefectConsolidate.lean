module

public import RequestProject.TheoremA.Lemma31.Picture.DefectLocal

/-!
# Internal consolidation in a least defect (Section 5)

`ConeComplex.IsLeastDefect.type_α_σ_ne`: in a least defect of a non-positively curved cone complex
of groups, consecutive darts `d`, `e = σ d` at any vertex have partners `u = α d`, `v = α e` of
different local types.

Suppose the types of `u` and `v` coincide.  The labels of the new map are (`consLab`)

* `d ↦ l_d · l_e` (product in the local group of the central vertex), `e ↦ 1`;
* `u ↦ l_v · l_u` (product in the common local group of `u`, `v`), `v ↦ 1`;
* all other labels unchanged,

and `e, v` are erased.  The two incidence orientations are checked in `relEdge_merge` (central
index vertex: `ab` and `φ(b)⁻¹φ(a)⁻¹ = φ(ab)⁻¹`; central triple vertex: `φ(a)⁻¹φ(b)⁻¹ = φ(ba)⁻¹` and
`ba`).  New labels may be `1`.

* **Distinct endpoints** (`u`, `v` at different vertices): the rotation is
  `erase_{e,v}((u v) · σ)` (`CombMap.consolidate_map`: connected, `χ = 2`, one edge fewer).  The
  merged vertex has product `q P q⁻¹ Q`, where `P`, `Q` are the old products at `u`, `v` and
  `q = l_v`; the central product and all other products are unchanged.
* **Digon** (`u`, `v` at the same vertex): Section 1 gives `σ v = u`; the rotation is
  `erase_{e,v}(σ)` (`CombMap.consolidateDigon_map`), and the product at `u` equals the old product
  at `v`.

In each case exactly one vertex has nonidentity product (tracked for every position of the old
exceptional vertex), which gives defect data with one edge fewer, contradicting minimality.
-/

@[expose] public section

namespace TheoremA

universe u w

open Picture Equiv Function

namespace ConeComplex

variable {V T : Type w} {C : ConeComplex.{u, w} V T}

/-! ### Products of letters -/

open Classical in
/-- The product of two letters, in the local group of the first one (the second letter is ignored
if it lies in a different local group; this does not happen below). -/
noncomputable def Letter.mul (p q : C.Letter) : C.Letter :=
  ⟨p.1, p.2 * (if h : q.1 = p.1 then h ▸ q.2 else 1)⟩

open Classical in
/-- The product of two letters, in the local group of the second one. -/
noncomputable def Letter.mulR (p q : C.Letter) : C.Letter :=
  ⟨q.1, (if h : p.1 = q.1 then h ▸ p.2 else 1) * q.2⟩

theorem Letter.mulR_mk (k : V ⊕ T) (x y : C.loc k) :
    Letter.mulR (⟨k, x⟩ : C.Letter) ⟨k, y⟩ = ⟨k, x * y⟩ := by
  simp [Letter.mulR]

theorem Letter.mulR_fst (p q : C.Letter) : (Letter.mulR p q).1 = q.1 := rfl

theorem letterWord_mulR {p q : C.Letter} (h : q.1 = p.1) :
    C.letterWord (Letter.mulR p q) = C.letterWord p * C.letterWord q := by
  obtain ⟨k, x⟩ := p
  obtain ⟨k', y⟩ := q
  simp only at h
  subst h
  rw [Letter.mulR_mk]
  exact map_mul (Monoid.CoprodI.of (M := C.loc) (i := k')) x y

theorem Letter.mul_mk (k : V ⊕ T) (x y : C.loc k) :
    Letter.mul (⟨k, x⟩ : C.Letter) ⟨k, y⟩ = ⟨k, x * y⟩ := by
  simp [Letter.mul]

theorem Letter.mul_fst (p q : C.Letter) : (Letter.mul p q).1 = p.1 := rfl

theorem letterWord_mul {p q : C.Letter} (h : q.1 = p.1) :
    C.letterWord (Letter.mul p q) = C.letterWord p * C.letterWord q := by
  obtain ⟨k, x⟩ := p
  obtain ⟨k', y⟩ := q
  simp only at h
  subst h
  rw [Letter.mul_mk]
  exact map_mul (Monoid.CoprodI.of (M := C.loc) (i := k')) x y

theorem letterWord_mk_one (k : V ⊕ T) : C.letterWord (⟨k, 1⟩ : C.Letter) = 1 :=
  map_one (Monoid.CoprodI.of (M := C.loc) (i := k))

/-- **Folding two relator edges of the same incidence.**  If `{p₁, q₁}` and `{p₂, q₂}` are
relator edges, `p₁, p₂` of the same type and `q₁, q₂` of the same type, then
`{p₁ p₂, q₂ q₁}` is a relator edge (both orientations). -/
theorem relEdge_merge {p₁ q₁ p₂ q₂ : C.Letter}
    (h₁ : C.RelEdge p₁ q₁ ∨ C.RelEdge q₁ p₁) (h₂ : C.RelEdge p₂ q₂ ∨ C.RelEdge q₂ p₂)
    (hp : p₂.1 = p₁.1) (hq : q₂.1 = q₁.1) :
    C.RelEdge (Letter.mul p₁ p₂) (Letter.mulR q₂ q₁) ∨
      C.RelEdge (Letter.mulR q₂ q₁) (Letter.mul p₁ p₂) := by
  rcases h₁ with ⟨i, t, hit, x, rfl, rfl⟩ | ⟨i, t, hit, x, rfl, rfl⟩
  · rcases h₂ with ⟨i', t', hit', y, rfl, rfl⟩ | ⟨i', t', hit', y, rfl, rfl⟩
    · simp only [Sum.inl.injEq, Sum.inr.injEq] at hp hq
      subst hp
      subst hq
      left
      refine ⟨i', t', hit, x * y, ?_, ?_⟩
      · rw [Letter.mul_mk]
      · rw [Letter.mulR_mk, map_mul, mul_inv_rev]
    · simp at hp
  · rcases h₂ with ⟨i', t', hit', y, rfl, rfl⟩ | ⟨i', t', hit', y, rfl, rfl⟩
    · simp at hp
    · simp only [Sum.inl.injEq, Sum.inr.injEq] at hp hq
      subst hp
      subst hq
      right
      refine ⟨i', t', hit, y * x, ?_, ?_⟩
      · rw [Letter.mulR_mk]
      · rw [Letter.mul_mk, map_mul, mul_inv_rev]

/-! ### The consolidated labels -/

/-- The labels after consolidating at the consecutive darts `d, e = σ d`. -/
noncomputable def consLab (M : CombMap) (lab : M.D → C.Letter) (d : M.D) (z : M.D) : C.Letter :=
  if z = d then Letter.mul (lab d) (lab (M.σ d))
  else if z = M.σ d then ⟨(lab (M.σ d)).1, 1⟩
  else if z = M.α d then Letter.mulR (lab (M.α (M.σ d))) (lab (M.α d))
  else if z = M.α (M.σ d) then ⟨(lab (M.α (M.σ d))).1, 1⟩
  else lab z

theorem consLab_fst (M : CombMap) (lab : M.D → C.Letter) (d z : M.D) :
    (consLab M lab d z).1 = (lab z).1 := by
  unfold consLab
  split_ifs with h1 h2 h3 h4
  · rw [Letter.mul_fst, h1]
  · rw [h2]
  · rw [Letter.mulR_fst, h3]
  · rw [h4]
  · rfl

namespace IsLeastDefect

variable {M : CombMap} {lab : M.D → C.Letter} (h : C.IsLeastDefect M lab) (hC : C.NPC) (d : M.D)
  (htyp : (lab (M.α (M.σ d))).1 = (lab (M.α d)).1)

section Facts

include h hC

omit hC in
theorem cons_hdu : ¬ M.σ.SameCycle d (M.α d) := h.1.not_sameCycle_α d

omit hC in
theorem cons_hdv : ¬ M.σ.SameCycle d (M.α (M.σ d)) := fun h' =>
  h.1.not_sameCycle_α (M.σ d) ((show M.σ.SameCycle d (M.σ d) from ⟨1, by simp⟩).symm.trans h')

theorem cons_ne : d ≠ M.α d ∧ d ≠ M.α (M.σ d) ∧ M.σ d ≠ M.α d ∧ M.σ d ≠ M.α (M.σ d) ∧
    M.α d ≠ M.α (M.σ d) ∧ M.σ d ≠ d := by
  have hde := h.σ_ne hC d
  have hdu := cons_hdu h d
  have hdv := cons_hdv h d
  have hσ : M.σ.SameCycle d (M.σ d) := ⟨1, by simp⟩
  refine ⟨fun e => hdu (e ▸ Perm.SameCycle.refl _ _), fun e => hdv (e ▸ Perm.SameCycle.refl _ _),
    fun e => hdu (e ▸ hσ), fun e => hdv (e ▸ hσ), fun e => hde (M.α.injective e).symm, hde⟩

omit h hC in
theorem consLab_d : consLab M lab d d = Letter.mul (lab d) (lab (M.σ d)) := by
  simp [consLab]

theorem consLab_e : consLab M lab d (M.σ d) = ⟨(lab (M.σ d)).1, 1⟩ := by
  obtain ⟨-, -, -, -, -, hde⟩ := cons_ne h hC d
  simp [consLab, hde]

theorem consLab_u : consLab M lab d (M.α d) = Letter.mulR (lab (M.α (M.σ d))) (lab (M.α d)) := by
  obtain ⟨h1, -, h3, -, -, -⟩ := cons_ne h hC d
  simp [consLab, h1.symm, h3.symm]

theorem consLab_v : consLab M lab d (M.α (M.σ d)) = ⟨(lab (M.α (M.σ d))).1, 1⟩ := by
  obtain ⟨-, h2, -, h4, h5, -⟩ := cons_ne h hC d
  simp [consLab, h2.symm, h4.symm, h5.symm]

omit h hC in
theorem consLab_of_ne {z : M.D} (h1 : z ≠ d) (h2 : z ≠ M.σ d) (h3 : z ≠ M.α d)
    (h4 : z ≠ M.α (M.σ d)) : consLab M lab d z = lab z := by
  simp [consLab, h1, h2, h3, h4]

theorem consWord_e : C.letterWord (consLab M lab d (M.σ d)) = 1 := by
  rw [consLab_e h hC d]; exact letterWord_mk_one _

theorem consWord_v : C.letterWord (consLab M lab d (M.α (M.σ d))) = 1 := by
  rw [consLab_v h hC d]; exact letterWord_mk_one _

omit hC in
theorem consWord_d : C.letterWord (consLab M lab d d) =
    C.letterWord (lab d) * C.letterWord (lab (M.σ d)) := by
  rw [consLab_d d, letterWord_mul (h.1.type_σ d)]

include htyp in
theorem consWord_u : C.letterWord (consLab M lab d (M.α d)) =
    C.letterWord (lab (M.α (M.σ d))) * C.letterWord (lab (M.α d)) := by
  rw [consLab_u h hC d, letterWord_mulR htyp.symm]

/-- The new labels satisfy the relator-edge condition on the retained darts. -/
theorem consLab_edge (hd' : (lab (M.α (M.σ d))).1 = (lab (M.α d)).1) (z : M.D)
    (hz1 : z ≠ M.σ d) (hz2 : z ≠ M.α (M.σ d)) :
    C.RelEdge (consLab M lab d z) (consLab M lab d (M.α z)) ∨
      C.RelEdge (consLab M lab d (M.α z)) (consLab M lab d z) := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := cons_ne h hC d
  have key := relEdge_merge (h.1.edge d) (h.1.edge (M.σ d)) (h.1.type_σ d) hd'
  by_cases hzd : z = d
  · subst hzd
    rw [consLab_d, consLab_u h hC]
    exact key
  by_cases hzu : z = M.α d
  · subst hzu
    rw [M.α_α, consLab_d, consLab_u h hC]
    exact key.symm
  have a1 : M.α z ≠ d := fun e => hzu (by rw [← e, M.α_α])
  have a2 : M.α z ≠ M.σ d := fun e => hz2 (by rw [← e, M.α_α])
  have a3 : M.α z ≠ M.α d := fun e => hzd (M.α.injective e)
  have a4 : M.α z ≠ M.α (M.σ d) := fun e => hz1 (M.α.injective e)
  rw [consLab_of_ne d hzd hz1 hzu hz2, consLab_of_ne d a1 a2 a3 a4]
  exact h.1.edge z

/-- The central product is unchanged (read from any retained dart of the central vertex). -/
theorem consWord_central {y : M.D} (hy : M.σ.SameCycle d y) (hye : y ≠ M.σ d) :
    cycleWord M.σ (C.letterWord ∘ consLab M lab d) y = cycleWord M.σ (C.letterWord ∘ lab) y := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := cons_ne h hC d
  refine cycleWord_merge_consecutive n6 hy hye (fun z hz hzd hze => ?_) ?_
  · have hzu : z ≠ M.α d := fun e => cons_hdu h d (e ▸ hz)
    have hzv : z ≠ M.α (M.σ d) := fun e => cons_hdv h d (e ▸ hz)
    simp only [Function.comp_apply, consLab_of_ne d hzd hze hzu hzv]
  · simp only [Function.comp_apply]
    rw [consWord_d h d, consWord_e h hC d, mul_one]

end Facts

/-! ### Distinct endpoints -/

section Distinct

variable (hdist : ¬ M.σ.SameCycle (M.α d) (M.α (M.σ d)))

include h hC htyp hdist

theorem consolidate_distinct_false : False := by
  classical
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := cons_ne h hC d
  have hdu := cons_hdu h d
  have hdv := cons_hdv h d
  set f := C.letterWord ∘ lab with hf
  set g := C.letterWord ∘ consLab M lab d with hg
  set πA := swap (M.α d) (M.α (M.σ d)) * M.σ with hπA
  have hπ : ∀ {y z}, πA.SameCycle y z ↔ M.σ.SameCycle y z ∨
      ((M.σ.SameCycle (M.α d) y ∨ M.σ.SameCycle (M.α (M.σ d)) y) ∧
        (M.σ.SameCycle (M.α d) z ∨ M.σ.SameCycle (M.α (M.σ d)) z)) :=
    sameCycle_swap_mul_iff hdist
  have hge : g (M.σ d) = 1 := consWord_e h hC d
  have hgv : g (M.α (M.σ d)) = 1 := consWord_v h hC d
  have hgu : g (M.α d) = f (M.α (M.σ d)) * f (M.α d) := consWord_u h hC d htyp
  have hwordA : ∀ y, y ≠ M.σ d → y ≠ M.α (M.σ d) →
      cycleWord (erase2 πA (M.σ d) (M.α (M.σ d))) g y = cycleWord πA g y :=
    fun y hy1 hy2 => cycleWord_erase2 g hy1 hy2 hge hgv
  have hpow : ∀ y, ¬ M.σ.SameCycle (M.α d) y → ¬ M.σ.SameCycle (M.α (M.σ d)) y →
      cycleWord πA g y = cycleWord M.σ g y :=
    fun y h1 h2 => cycleWord_congr _ (swap_mul_pow_apply_of_not_sameCycle h1 h2)
  have hWC : ∀ y, M.σ.SameCycle d y → y ≠ M.σ d → cycleWord πA g y = cycleWord M.σ f y := by
    intro y hy hye
    rw [hpow y (fun h' => hdu (hy.trans h'.symm)) (fun h' => hdv (hy.trans h'.symm))]
    exact consWord_central h hC d hy hye
  have hWO : ∀ y, ¬ M.σ.SameCycle d y → ¬ M.σ.SameCycle (M.α d) y →
      ¬ M.σ.SameCycle (M.α (M.σ d)) y → cycleWord πA g y = cycleWord M.σ f y := by
    intro y h1 h2 h3
    rw [hpow y h2 h3]
    refine cycleWord_congr_fun fun z hz => ?_
    have z1 : z ≠ d := fun e => h1 (e ▸ hz.symm)
    have z2 : z ≠ M.σ d := fun e => h1 ((show M.σ.SameCycle d (M.σ d) from ⟨1, by simp⟩).trans
      (e ▸ hz.symm))
    have z3 : z ≠ M.α d := fun e => h2 (e ▸ hz.symm)
    have z4 : z ≠ M.α (M.σ d) := fun e => h3 (e ▸ hz.symm)
    simp only [hg, hf, Function.comp_apply, consLab_of_ne d z1 z2 z3 z4]
  have hWU : cycleWord πA g (M.α d) = f (M.α (M.σ d)) * cycleWord M.σ f (M.α d) *
      (f (M.α (M.σ d)))⁻¹ * cycleWord M.σ f (M.α (M.σ d)) := by
    rw [hπA, cycleWord_swap_mul g hdist]
    have e1 : cycleWord M.σ g (M.α d) = g (M.α d) * (f (M.α d))⁻¹ * cycleWord M.σ f (M.α d) := by
      refine cycleWord_update_first M.σ fun z hz hzu => ?_
      have z1 : z ≠ d := fun e => hdu (e ▸ hz).symm
      have z2 : z ≠ M.σ d := fun e => hdu ((show M.σ.SameCycle d (M.σ d) from ⟨1, by simp⟩).trans
        (e ▸ hz).symm)
      have z4 : z ≠ M.α (M.σ d) := fun e => hdist (e ▸ hz)
      simp only [hg, hf, Function.comp_apply, consLab_of_ne d z1 z2 hzu z4]
    have e2 : cycleWord M.σ g (M.α (M.σ d)) = g (M.α (M.σ d)) * (f (M.α (M.σ d)))⁻¹ *
        cycleWord M.σ f (M.α (M.σ d)) := by
      refine cycleWord_update_first M.σ fun z hz hzv => ?_
      have z1 : z ≠ d := fun e => hdv (e ▸ hz).symm
      have z2 : z ≠ M.σ d := fun e => hdv ((show M.σ.SameCycle d (M.σ d) from ⟨1, by simp⟩).trans
        (e ▸ hz).symm)
      have z3 : z ≠ M.α d := fun e => hdist (e ▸ hz).symm
      simp only [hg, hf, Function.comp_apply, consLab_of_ne d z1 z2 z3 hzv]
    rw [e1, e2, hgu, hgv]
    group
  have hSU : ∀ y, (M.σ.SameCycle (M.α d) y ∨ M.σ.SameCycle (M.α (M.σ d)) y) →
      πA.SameCycle (M.α d) y := fun y hy => hπ.2 (Or.inr ⟨Or.inl (Perm.SameCycle.refl _ _), hy⟩)
  have hSσ : ∀ y z, M.σ.SameCycle y z → πA.SameCycle y z := fun y z hyz => hπ.2 (Or.inl hyz)
  -- map facts
  obtain ⟨hconn, hχ, hE⟩ := CombMap.consolidate_map (κ := fun z => (lab z).1.isLeft)
    h.1.kind_σ h.1.kind_α h.1.connected h.1.spherical n6 (by simpa only [htyp]) hdist
  obtain ⟨b0, hb0, hexc⟩ := h.1.exc
  -- `P = 1`, `Q = 1` away from the exceptional vertex
  have hP1 : ¬ M.σ.SameCycle (M.α d) b0 → cycleWord M.σ f (M.α d) = 1 := fun h' => by
    by_contra hne; exact h' (hexc _ hne).symm
  have hQ1 : ¬ M.σ.SameCycle (M.α (M.σ d)) b0 → cycleWord M.σ f (M.α (M.σ d)) = 1 := fun h' => by
    by_contra hne; exact h' (hexc _ hne).symm
  have hwb0 : ∀ y, M.σ.SameCycle b0 y → cycleWord M.σ f y ≠ 1 := fun y hy hw =>
    hb0 (cycleWord_eq_one_of_sameCycle _ hy.symm hw)
  have hUone : ¬ M.σ.SameCycle (M.α d) b0 → ¬ M.σ.SameCycle (M.α (M.σ d)) b0 →
      ∀ y, (M.σ.SameCycle (M.α d) y ∨ M.σ.SameCycle (M.α (M.σ d)) y) → cycleWord πA g y = 1 := by
    intro h1 h2 y hy
    refine cycleWord_eq_one_of_sameCycle _ (hSU y hy) ?_
    rw [hWU, hP1 h1, hQ1 h2]
    group
  have hdata : ∀ x, x ≠ M.σ d → x ≠ M.α (M.σ d) → cycleWord πA g x ≠ 1 →
      (∀ y, y ≠ M.σ d → y ≠ M.α (M.σ d) → cycleWord πA g y ≠ 1 → πA.SameCycle x y) →
      C.DefectData (M.eraseEdge πA (M.σ d)) (consLab M lab d ∘ Subtype.val) := by
    intro x hx1 hx2 hwx hrest
    refine DefectData.of_eraseEdge πA (M.σ d) (consLab M lab d) hconn hχ ?_
      (fun z hz1 hz2 => consLab_edge h hC d htyp z hz1 hz2) x hx1 hx2 (by rwa [hwordA x hx1 hx2])
      (fun y hy1 hy2 hy => hrest y hy1 hy2 (by rwa [hwordA y hy1 hy2] at hy))
    intro z w _ _ _ _ hzw
    rw [consLab_fst, consLab_fst]
    rcases hπ.1 hzw with h' | ⟨hz, hw⟩
    · exact h.1.type_eq_of_sameCycle h'
    · have tz : (lab z).1 = (lab (M.α d)).1 := by
        rcases hz with hz | hz
        · exact h.1.type_eq_of_sameCycle hz
        · rw [h.1.type_eq_of_sameCycle hz, htyp]
      have tw : (lab w).1 = (lab (M.α d)).1 := by
        rcases hw with hw | hw
        · exact h.1.type_eq_of_sameCycle hw
        · rw [h.1.type_eq_of_sameCycle hw, htyp]
      rw [tz, tw]
  have hfew : (M.eraseEdge πA (M.σ d)).numEdges < M.numEdges := by rw [hπA]; omega
  by_cases hb0c : M.σ.SameCycle d b0
  · -- exceptional vertex at the centre
    refine h.not_lt (hdata d n6.symm n2 ?_ fun y hy1 hy2 hwy => ?_) hfew
    · rw [hWC d (Perm.SameCycle.refl _ _) n6.symm]
      exact hwb0 d hb0c.symm
    · by_cases hdy : M.σ.SameCycle d y
      · exact hSσ d y hdy
      by_cases huy : M.σ.SameCycle (M.α d) y ∨ M.σ.SameCycle (M.α (M.σ d)) y
      · exact absurd (hUone (fun h' => hdu (hb0c.trans h'.symm))
          (fun h' => hdv (hb0c.trans h'.symm)) y huy) hwy
      · push_neg at huy
        rw [hWO y hdy huy.1 huy.2] at hwy
        exact absurd (hb0c.trans (hexc y hwy)) hdy
  by_cases hb0u : M.σ.SameCycle (M.α d) b0 ∨ M.σ.SameCycle (M.α (M.σ d)) b0
  · -- exceptional vertex at one of the merged endpoints
    refine h.not_lt (hdata (M.α d) n3.symm n5 ?_ fun y hy1 hy2 hwy => ?_) hfew
    · rw [hWU]
      rcases hb0u with hu | hv
      · rw [hQ1 (fun h' => hdist (hu.trans h'.symm)), mul_one]
        intro h'
        apply hwb0 (M.α d) hu.symm
        have : cycleWord M.σ f (M.α d) =
            (f (M.α (M.σ d)))⁻¹ * (f (M.α (M.σ d)) * cycleWord M.σ f (M.α d) *
              (f (M.α (M.σ d)))⁻¹) * f (M.α (M.σ d)) := by group
        rw [this, h']
        group
      · rw [hP1 (fun h' => hdist (h'.trans hv.symm)), mul_one, mul_inv_cancel, one_mul]
        exact hwb0 _ hv.symm
    · by_cases hdy : M.σ.SameCycle d y
      · rw [hWC y hdy hy1] at hwy
        exact absurd (hdy.trans (hexc y hwy).symm) hb0c
      by_cases huy : M.σ.SameCycle (M.α d) y ∨ M.σ.SameCycle (M.α (M.σ d)) y
      · exact hSU y huy
      · push_neg at huy
        rw [hWO y hdy huy.1 huy.2] at hwy
        rcases hb0u with hu | hv
        · exact absurd (hu.trans (hexc y hwy)) huy.1
        · exact absurd (hv.trans (hexc y hwy)) huy.2
  · -- exceptional vertex elsewhere
    push_neg at hb0u
    have hb1 : b0 ≠ M.σ d := fun e => hb0c (e ▸ ⟨1, by simp⟩)
    have hb2 : b0 ≠ M.α (M.σ d) := fun e => hb0u.2 (e ▸ Perm.SameCycle.refl _ _)
    have hb0c' : ¬ M.σ.SameCycle d b0 := hb0c
    have hb0u1 : ¬ M.σ.SameCycle (M.α d) b0 := hb0u.1
    have hb0u2 : ¬ M.σ.SameCycle (M.α (M.σ d)) b0 := hb0u.2
    refine h.not_lt (hdata b0 hb1 hb2 ?_ fun y hy1 hy2 hwy => ?_) hfew
    · rw [hWO b0 hb0c' hb0u1 hb0u2]
      exact hb0
    · by_cases hdy : M.σ.SameCycle d y
      · rw [hWC y hdy hy1] at hwy
        exact absurd (hdy.trans (hexc y hwy).symm) hb0c'
      by_cases huy : M.σ.SameCycle (M.α d) y ∨ M.σ.SameCycle (M.α (M.σ d)) y
      · exact absurd (hUone hb0u1 hb0u2 y huy) hwy
      · push_neg at huy
        rw [hWO y hdy huy.1 huy.2] at hwy
        exact hSσ b0 y (hexc y hwy)

end Distinct

/-! ### Digon -/

section Digon

variable (hdig : M.σ (M.α (M.σ d)) = M.α d)

include h hC htyp hdig

theorem consolidate_digon_false : False := by
  classical
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := cons_ne h hC d
  have hdu := cons_hdu h d
  set f := C.letterWord ∘ lab with hf
  set g := C.letterWord ∘ consLab M lab d with hg
  have hge : g (M.σ d) = 1 := consWord_e h hC d
  have hgv : g (M.α (M.σ d)) = 1 := consWord_v h hC d
  have hgu : g (M.α d) = f (M.α (M.σ d)) * f (M.α d) := consWord_u h hC d htyp
  have hvu : M.σ.SameCycle (M.α (M.σ d)) (M.α d) := ⟨1, by rw [zpow_one]; exact hdig⟩
  have hdσ : M.σ.SameCycle d (M.σ d) := ⟨1, by simp⟩
  have hwordB : ∀ y, y ≠ M.σ d → y ≠ M.α (M.σ d) →
      cycleWord (erase2 M.σ (M.σ d) (M.α (M.σ d))) g y = cycleWord M.σ g y :=
    fun y hy1 hy2 => cycleWord_erase2 g hy1 hy2 hge hgv
  have hWC : ∀ y, M.σ.SameCycle d y → y ≠ M.σ d → cycleWord M.σ g y = cycleWord M.σ f y :=
    fun y hy hye => consWord_central h hC d hy hye
  have hWO : ∀ y, ¬ M.σ.SameCycle d y → ¬ M.σ.SameCycle (M.α d) y →
      cycleWord M.σ g y = cycleWord M.σ f y := by
    intro y h1 h2
    refine cycleWord_congr_fun fun z hz => ?_
    have z1 : z ≠ d := fun e => h1 (e ▸ hz.symm)
    have z2 : z ≠ M.σ d := fun e => h1 (hdσ.trans (e ▸ hz.symm))
    have z3 : z ≠ M.α d := fun e => h2 (e ▸ hz.symm)
    have z4 : z ≠ M.α (M.σ d) := fun e => h2 (hvu.symm.trans (e ▸ hz.symm))
    simp only [hg, hf, Function.comp_apply, consLab_of_ne d z1 z2 z3 z4]
  have hWU : cycleWord M.σ g (M.α d) = cycleWord M.σ f (M.α (M.σ d)) := by
    have e1 : cycleWord M.σ g (M.α (M.σ d)) = cycleWord M.σ f (M.α (M.σ d)) := by
      refine cycleWord_merge_consecutive (by rw [hdig]; exact n5) (Perm.SameCycle.refl _ _)
        (by rw [hdig]; exact n5.symm) (fun z hz hzv hzu => ?_) ?_
      · rw [hdig] at hzu
        have z1 : z ≠ d := fun e => cons_hdv h d (e ▸ hz).symm
        have z2 : z ≠ M.σ d := fun e => cons_hdv h d (hdσ.trans (e ▸ hz).symm)
        simp only [hg, hf, Function.comp_apply, consLab_of_ne d z1 z2 hzu hzv]
      · rw [hdig, hgv, hgu, one_mul]
    have e2 := cycleWord_apply M.σ g (M.α (M.σ d))
    rw [hdig, hgv] at e2
    rw [e2, e1]
    group
  obtain ⟨hconn, hχ, hE⟩ := CombMap.consolidateDigon_map (κ := fun z => (lab z).1.isLeft)
    h.1.kind_σ h.1.kind_α h.1.connected h.1.spherical n6 (by simpa only [htyp]) hdig
  obtain ⟨b0, hb0, hexc⟩ := h.1.exc
  have hwb0 : ∀ y, M.σ.SameCycle b0 y → cycleWord M.σ f y ≠ 1 := fun y hy hw =>
    hb0 (cycleWord_eq_one_of_sameCycle _ hy.symm hw)
  have hUone : ¬ M.σ.SameCycle (M.α d) b0 → ∀ y, M.σ.SameCycle (M.α d) y →
      cycleWord M.σ g y = 1 := by
    intro h1 y hy
    refine cycleWord_eq_one_of_sameCycle _ hy ?_
    rw [hWU]
    by_contra hne
    exact h1 (hvu.symm.trans (hexc _ hne).symm)
  have hdata : ∀ x, x ≠ M.σ d → x ≠ M.α (M.σ d) → cycleWord M.σ g x ≠ 1 →
      (∀ y, y ≠ M.σ d → y ≠ M.α (M.σ d) → cycleWord M.σ g y ≠ 1 → M.σ.SameCycle x y) →
      C.DefectData (M.eraseEdge M.σ (M.σ d)) (consLab M lab d ∘ Subtype.val) := by
    intro x hx1 hx2 hwx hrest
    refine DefectData.of_eraseEdge M.σ (M.σ d) (consLab M lab d) hconn hχ ?_
      (fun z hz1 hz2 => consLab_edge h hC d htyp z hz1 hz2) x hx1 hx2 (by rwa [hwordB x hx1 hx2])
      (fun y hy1 hy2 hy => hrest y hy1 hy2 (by rwa [hwordB y hy1 hy2] at hy))
    intro z w _ _ _ _ hzw
    rw [consLab_fst, consLab_fst]
    exact h.1.type_eq_of_sameCycle hzw
  have hfew : (M.eraseEdge M.σ (M.σ d)).numEdges < M.numEdges := by omega
  by_cases hb0c : M.σ.SameCycle d b0
  · refine h.not_lt (hdata d n6.symm n2 ?_ fun y hy1 hy2 hwy => ?_) hfew
    · rw [hWC d (Perm.SameCycle.refl _ _) n6.symm]
      exact hwb0 d hb0c.symm
    · by_cases hdy : M.σ.SameCycle d y
      · exact hdy
      by_cases huy : M.σ.SameCycle (M.α d) y
      · exact absurd (hUone (fun h' => hdu (hb0c.trans h'.symm)) y huy) hwy
      · rw [hWO y hdy huy] at hwy
        exact absurd (hb0c.trans (hexc y hwy)) hdy
  by_cases hb0u : M.σ.SameCycle (M.α d) b0
  · refine h.not_lt (hdata (M.α d) n3.symm n5 ?_ fun y hy1 hy2 hwy => ?_) hfew
    · rw [hWU]
      exact hwb0 _ (hb0u.symm.trans hvu.symm)
    · by_cases hdy : M.σ.SameCycle d y
      · rw [hWC y hdy hy1] at hwy
        exact absurd (hdy.trans (hexc y hwy).symm) hb0c
      by_cases huy : M.σ.SameCycle (M.α d) y
      · exact huy
      · rw [hWO y hdy huy] at hwy
        exact absurd (hb0u.trans (hexc y hwy)) huy
  · have hb1 : b0 ≠ M.σ d := fun e => hb0c (e ▸ hdσ)
    have hb2 : b0 ≠ M.α (M.σ d) := fun e => hb0u (e ▸ hvu.symm)
    refine h.not_lt (hdata b0 hb1 hb2 ?_ fun y hy1 hy2 hwy => ?_) hfew
    · rw [hWO b0 hb0c hb0u]
      exact hb0
    · by_cases hdy : M.σ.SameCycle d y
      · rw [hWC y hdy hy1] at hwy
        exact absurd (hdy.trans (hexc y hwy).symm) hb0c
      by_cases huy : M.σ.SameCycle (M.α d) y
      · exact absurd (hUone hb0u y huy) hwy
      · rw [hWO y hdy huy] at hwy
        exact hexc y hwy

end Digon

include h hC in
/-- **Section 5: internal consolidation forbids repeated neighbouring types.**  In a least defect,
consecutive darts `d`, `σ d` at any vertex have partners of different local types. -/
theorem type_α_σ_ne : (lab (M.α (M.σ d))).1 ≠ (lab (M.α d)).1 := by
  intro htyp'
  by_cases hdist : M.σ.SameCycle (M.α d) (M.α (M.σ d))
  · have hdig : M.σ (M.α (M.σ d)) = M.α d := by
      have hφ1 : M.φ (M.α d) = M.σ d := by
        change M.σ (M.α (M.α d)) = _
        rw [M.α_α]
      have hφ2 : M.φ (M.σ d) = M.σ (M.α (M.σ d)) := rfl
      have hface : M.φ.SameCycle (M.α d) (M.σ (M.α (M.σ d))) := ⟨2, by
        rw [zpow_ofNat, pow_two, Perm.mul_apply, hφ1, hφ2]⟩
      exact (h.sameVertex_sameFace_eq (hdist.trans ⟨1, by simp⟩) hface).symm
    exact consolidate_digon_false h hC d htyp' hdig
  · exact consolidate_distinct_false h hC d htyp' hdist

end IsLeastDefect

end ConeComplex

end TheoremA
