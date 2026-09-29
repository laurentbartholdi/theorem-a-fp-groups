module

public import RequestProject.TheoremA.Lemma31.Picture.IdentityEdge
public import RequestProject.TheoremA.Lemma31.Picture.Minimal

/-!
# A typed exceptional vertex

## No marked loops (Section 5 of the task)

`RawPicture.NoMarkedLoops R` says that every dart at the marked vertex has its `α`-partner at an
ordinary vertex.  **This is already one of the raw-picture axioms**: the field
`RawPicture.edge_boundary` states, for every dart `d` at the marked vertex, that `α d` is *not* at
the marked vertex.  Hence every raw picture has no marked loops (`RawPicture.noMarkedLoops`), and
in particular every constructor used in the raw-existence proof (the relator triangle, the
letter-pair digon, gluing at marked vertices, re-basing within the marked vertex) as well as every
move of the extraction, capping, consolidation and identity-deletion constructions produces
pictures with no marked loops — each of them had to prove `edge_boundary` to produce a
`RawPicture` at all.  Consequently the restricted minimality notion "least among local pictures
with no marked loops" coincides with the existing `LocalPicture.IsLeast`
(`LocalPicture.isLeastNoMarkedLoops_iff`), and the existing digon lemma
`LocalPicture.IsLeast.adjacent_marked_digon` applies unchanged.

## Marked degree one (Section 6)

In a least local picture:
* no dart at the marked vertex carries the identity letter (`IsLeast.marked_lab_ne_one`, via the
  identity-edge deletion);
* two consecutive darts `d, e = σ d` at the marked vertex with `e ≠ base` carry letters of
  different local factors (`IsLeast.marked_fst_ne`, via the two consolidation moves and the digon
  lemma);
* hence the marked word, read linearly from the base, is a reduced word of the free product
  (`Monoid.CoprodI.Word`), and by uniqueness of reduced words it is the single letter
  `⟨k, g⟩` (`IsLeast.marked_degree_one`): the marked vertex has exactly one dart.
-/

@[expose] public section

namespace TheoremA

universe u w

namespace ConeComplex

open Picture Equiv Function

variable {V T : Type w} {C : ConeComplex.{u, w} V T}

/-! ### No marked loops -/

/-- **No marked loops**: every dart at the marked vertex has its `α`-partner at an ordinary
vertex.  (A property of the marked vertex only.) -/
def RawPicture.NoMarkedLoops {x : Monoid.CoprodI C.loc} (R : C.RawPicture x) : Prop :=
  ∀ d, R.M.σ.SameCycle R.base d → ¬ R.M.σ.SameCycle R.base (R.M.α d)

/-- Every raw picture has no marked loops: this is part of the raw-picture axiom
`edge_boundary`.  In particular all raw-existence constructors, the extraction and capping moves,
both consolidation moves and the identity-edge deletion preserve the property. -/
theorem RawPicture.noMarkedLoops {x : Monoid.CoprodI C.loc} (R : C.RawPicture x) :
    R.NoMarkedLoops :=
  fun d hd => (R.edge_boundary d hd).1

namespace LocalPicture

/-- Least edge count among local pictures with no marked loops. -/
def IsLeastNoMarkedLoops (L : C.LocalPicture) : Prop :=
  L.R.NoMarkedLoops ∧ ∀ L' : C.LocalPicture, L'.R.NoMarkedLoops → L.R.M.numEdges ≤ L'.R.M.numEdges

/-- Since every raw picture has no marked loops, the restricted minimality predicate is the
existing one. -/
theorem isLeastNoMarkedLoops_iff (L : C.LocalPicture) : L.IsLeastNoMarkedLoops ↔ L.IsLeast :=
  ⟨fun h L' => h.2 L' L'.R.noMarkedLoops, fun h => ⟨L.R.noMarkedLoops, fun L' _ => h L'⟩⟩

variable {L : C.LocalPicture}

theorem word_ne_one (L : C.LocalPicture) : C.letterWord ⟨L.k, L.g⟩ ≠ 1 := by
  intro h
  exact L.ne_one (Monoid.CoprodI.of_injective L.k (h.trans (map_one _).symm))

/-- **No identity letters at the marked vertex of a least local picture.** -/
theorem IsLeast.marked_lab_ne_one (hL : L.IsLeast) {d : L.R.M.D}
    (hd : L.R.M.σ.SameCycle L.R.base d) : (L.R.lab d).2 ≠ 1 := by
  intro h1
  obtain ⟨R', hR'⟩ := L.R.exists_fewer_edges_of_identity L.word_ne_one hd h1
  have := hL ⟨L.k, L.g, L.ne_one, R'⟩
  simp only at this
  omega

/-- **No two consecutive letters from the same factor** (linear reading: the second dart is not
the base) at the marked vertex of a least local picture. -/
theorem IsLeast.marked_fst_ne (hL : L.IsLeast) {d e : L.R.M.D}
    (hd : L.R.M.σ.SameCycle L.R.base d) (hde : L.R.M.σ d = e) (hne : d ≠ e)
    (hbase : e ≠ L.R.base) : (L.R.lab d).1 ≠ (L.R.lab e).1 := by
  intro hk
  rcases hld : L.R.lab d with ⟨k₁, g₁⟩
  rcases hle : L.R.lab e with ⟨k₂, g₂⟩
  rw [hld, hle] at hk
  change k₁ = k₂ at hk
  subst hk
  let P : L.R.MarkedPair := ⟨d, e, k₁, g₁, g₂, hd, hde, hne, hbase, hld, hle⟩
  by_cases hX : L.R.M.σ.SameCycle P.u P.v
  · have hdig : L.R.M.σ P.v = P.u := (hL.adjacent_marked_digon hd hde hne hX).1
    have h1 := hL ⟨L.k, L.g, L.ne_one, P.consolidateDigon hdig⟩
    have h2 := (P.consolidateDigon_counts hdig).2.1
    simp only at h1
    omega
  · have h1 := hL ⟨L.k, L.g, L.ne_one, P.consolidate hX⟩
    have h2 := P.consolidate_numEdges hX
    simp only at h1
    omega

/-- **Marked degree one.**  In a least local picture the marked vertex has exactly one dart (the
base), and it carries the letter `⟨k, g⟩`.  Proof: by `marked_lab_ne_one` and `marked_fst_ne` the
marked word read linearly from the base is a reduced word of the free product; its value is the
one-letter reduced word `⟨k, g⟩`, so by uniqueness of reduced words (`Monoid.CoprodI.Word.equiv`)
the two words agree. -/
theorem IsLeast.marked_degree_one (hL : L.IsLeast) :
    L.R.M.σ L.R.base = L.R.base ∧ L.R.lab L.R.base = ⟨L.k, L.g⟩ := by
  classical
  have hmarked : ∀ i : ℕ, L.R.M.σ.SameCycle L.R.base ((L.R.M.σ ^ i) L.R.base) :=
    fun i => ⟨i, by simp⟩
  have hinj : ∀ i j : ℕ, i < minimalPeriod L.R.M.σ L.R.base →
      j < minimalPeriod L.R.M.σ L.R.base → (L.R.M.σ ^ i) L.R.base = (L.R.M.σ ^ j) L.R.base →
      i = j := by
    intro i j hi hj h
    refine Function.iterate_injOn_Iio_minimalPeriod (f := L.R.M.σ) hi hj ?_
    simpa only [Equiv.Perm.coe_pow] using h
  let l : List C.Letter :=
    (List.range (minimalPeriod L.R.M.σ L.R.base)).map fun i => L.R.lab ((L.R.M.σ ^ i) L.R.base)
  let w : Monoid.CoprodI.Word C.loc :=
    { toList := l
      ne_one := by
        intro p hp
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp
        exact hL.marked_lab_ne_one (hmarked i)
      chain_ne := by
        refine (List.isChain_map _).2 ((List.isChain_range _ _).2 fun i hi => ?_)
        refine hL.marked_fst_ne (hmarked i) ?_ ?_ ?_
        · rw [Nat.succ_eq_add_one, pow_succ', Perm.mul_apply]
        · intro h
          have := hinj i (i + 1) (by omega) (by omega) h
          omega
        · intro h
          have := hinj (i + 1) 0 (by omega) (by omega) (by simpa using h)
          omega }
  have hw : w.prod = C.letterWord ⟨L.k, L.g⟩ := by
    rw [← L.R.boundary_word]
    change (l.map fun p => Monoid.CoprodI.of p.2).prod = _
    simp only [l, List.map_map]
    rfl
  let w₁ : Monoid.CoprodI.Word C.loc :=
    { toList := [⟨L.k, L.g⟩]
      ne_one := by simpa using L.ne_one
      chain_ne := List.isChain_singleton _ }
  have hw₁ : w₁.prod = C.letterWord ⟨L.k, L.g⟩ := by
    change ([(⟨L.k, L.g⟩ : C.Letter)].map fun p => Monoid.CoprodI.of p.2).prod = _
    simp [letterWord]
  have heq : w = w₁ := Monoid.CoprodI.Word.equiv.symm.injective (hw.trans hw₁.symm)
  have hl : l = [⟨L.k, L.g⟩] := congrArg Monoid.CoprodI.Word.toList heq
  have hn : minimalPeriod L.R.M.σ L.R.base = 1 := by
    simpa [l] using congrArg List.length hl
  refine ⟨minimalPeriod_eq_one_iff_isFixedPt.1 hn, ?_⟩
  have := hl
  simp only [l, hn, List.range_one, List.map_cons, List.map_nil, pow_zero,
    Perm.one_apply, List.cons.injEq, and_true] at this
  exact this

end LocalPicture

/-! ### Removing the marked leaf: a typed defect (Section 7) -/

namespace RawPicture

variable {x : Monoid.CoprodI C.loc} (R : C.RawPicture x) (hfix : R.M.σ R.base = R.base)
  {s : V ⊕ T} {a : C.loc s} (hlab : R.lab R.base = ⟨s, a⟩) (ha : a ≠ 1)

section Uncap

include hfix

theorem marked_eq_base_of_fixed {z : R.M.D} (hz : R.M.σ.SameCycle R.base z) : z = R.base :=
  (hz.eq_of_left hfix).symm

omit hfix in
theorem not_marked_leafPartner : ¬ R.M.σ.SameCycle R.base (R.M.α R.base) :=
  (R.edge_boundary R.base (Perm.SameCycle.refl _ _)).1

omit hfix in
theorem base_ne_leafPartner : R.base ≠ R.M.α R.base := fun h =>
  R.not_marked_leafPartner (h ▸ Perm.SameCycle.refl _ _)

omit hfix in
include hlab in
theorem lab_leafPartner : R.lab (R.M.α R.base) = ⟨s, a⁻¹⟩ := by
  rw [(R.edge_boundary R.base (Perm.SameCycle.refl _ _)).2, hlab]
  rfl

omit hfix in
include hlab ha in
/-- The ordinary endpoint of the marked leaf has degree at least two (`W` is nonempty). -/
theorem σ_leafPartner_ne : R.M.σ (R.M.α R.base) ≠ R.M.α R.base := by
  intro h
  have h1 := R.local_eq _ R.not_marked_leafPartner
  rw [cycleWord_of_fixed _ h, Function.comp_apply, R.lab_leafPartner hlab] at h1
  apply ha
  have h2 : Monoid.CoprodI.of (a⁻¹) = (1 : Monoid.CoprodI C.loc) := h1
  rw [map_inv, inv_eq_one] at h2
  exact Monoid.CoprodI.of_injective s (h2.trans (map_one _).symm)

theorem σ_leafPartner_ne_base : R.M.σ (R.M.α R.base) ≠ R.base := by
  intro h
  apply R.base_ne_leafPartner
  exact R.M.σ.injective (hfix.trans h.symm)

theorem erase2_leaf_eq : erase2 R.M.σ R.base (R.M.α R.base) = erasePt R.M.σ (R.M.α R.base) := by
  unfold erase2
  rw [erasePt_of_fixed hfix]

include hlab ha

theorem uncap_numVertices :
    (R.M.eraseEdge R.M.σ R.base).numVertices + 1 = R.M.numVertices := by
  have hA := CombMap.eraseEdge_numVertices R.M.σ R.base
  have hB := numOrbits_erase2 R.M.σ R.base (R.M.α R.base)
  rw [if_pos hfix, erasePt_of_fixed hfix, if_neg (R.σ_leafPartner_ne hlab ha)] at hB
  unfold CombMap.numVertices at hA ⊢
  omega

theorem uncap_numFaces : (R.M.eraseEdge R.M.σ R.base).numFaces = R.M.numFaces := by
  have hA := CombMap.eraseEdge_numFaces R.M.σ R.base
  have hmu : R.base ≠ R.M.α R.base := R.base_ne_leafPartner
  have hσu := R.σ_leafPartner_ne hlab ha
  have hσum : R.M.σ (R.M.α R.base) ≠ R.base := R.σ_leafPartner_ne_base hfix
  have hB := numOrbits_erase2 (swap R.base (R.M.α R.base) * R.M.σ * R.M.α) R.base (R.M.α R.base)
  have hχ : swap R.base (R.M.α R.base) * R.M.σ * R.M.α = swap R.base (R.M.α R.base) * R.M.φ := by
    rw [mul_assoc]; rfl
  have hχm : (swap R.base (R.M.α R.base) * R.M.σ * R.M.α) R.base = R.M.σ (R.M.α R.base) := by
    change swap R.base (R.M.α R.base) (R.M.σ (R.M.α R.base)) = _
    exact swap_apply_of_ne_of_ne hσum hσu
  have hχu : (swap R.base (R.M.α R.base) * R.M.σ * R.M.α) (R.M.α R.base) = R.M.α R.base := by
    change swap R.base (R.M.α R.base) (R.M.σ (R.M.α (R.M.α R.base))) = _
    rw [R.M.α_α, hfix, swap_apply_left]
  have h2 : erasePt (swap R.base (R.M.α R.base) * R.M.σ * R.M.α) R.base (R.M.α R.base) =
      R.M.α R.base := by
    rw [erasePt_apply_of_ne hmu.symm (by rw [hχu]; exact hmu.symm), hχu]
  rw [hχm, if_neg hσum, h2, if_pos rfl, hχ] at hB
  have hφ : R.M.φ.SameCycle R.base (R.M.α R.base) := by
    refine (show R.M.φ.SameCycle (R.M.α R.base) R.base from ⟨1, ?_⟩).symm
    change R.M.σ (R.M.α (R.M.α R.base)) = R.base
    rw [R.M.α_α, hfix]
  have hs := numOrbits_swap_mul_split hmu hφ
  rw [hχ] at hA
  unfold CombMap.numFaces at hA ⊢
  omega

theorem uncap_connected : (R.M.eraseEdge R.M.σ R.base).Connected := by
  classical
  have hmu : R.base ≠ R.M.α R.base := R.base_ne_leafPartner
  have hσu := R.σ_leafPartner_ne hlab ha
  have hσum : R.M.σ (R.M.α R.base) ≠ R.base := R.σ_leafPartner_ne_base hfix
  let g : R.M.D → R.M.D := fun z =>
    if z = R.base then R.M.σ (R.M.α R.base) else if z = R.M.α R.base then R.M.σ (R.M.α R.base)
    else z
  have hgm : g R.base = R.M.σ (R.M.α R.base) := if_pos rfl
  have hgu : g (R.M.α R.base) = R.M.σ (R.M.α R.base) := by
    simp only [g, if_neg hmu.symm, if_true]
  have hgid : ∀ y, y ≠ R.base → y ≠ R.M.α R.base → g y = y := fun y h1 h2 => by
    simp only [g, if_neg h1, if_neg h2]
  refine CombMap.eraseEdge_connected_of R.M.σ R.base R.connected g hgid (fun y => ?_)
    (fun y => ?_)
  · by_cases hym : y = R.base
    · subst hym; rw [hfix]; exact Relation.EqvGen.refl _
    by_cases hyu : y = R.M.α R.base
    · subst hyu; rw [hgu, hgid _ hσum hσu]; exact Relation.EqvGen.refl _
    rw [hgid y hym hyu]
    have h1 : R.M.σ y ≠ R.base := fun h => hym (R.M.σ.injective (h.trans hfix.symm))
    by_cases h2 : R.M.σ y = R.M.α R.base
    · rw [h2, hgu]
      exact Relation.EqvGen.rel _ _ (Or.inl (erase2_apply_of_eq_right hmu hym h2 hσum).symm)
    · rw [hgid _ h1 h2]
      exact Relation.EqvGen.rel _ _ (Or.inl (erase2_apply_of_notMem hym hyu h1 h2).symm)
  · by_cases hym : y = R.base
    · rw [hym, hgm, hgu]; exact Relation.EqvGen.refl _
    by_cases hyu : y = R.M.α R.base
    · rw [hyu, hgu, R.M.α_α, hgm]; exact Relation.EqvGen.refl _
    have h1 : R.M.α y ≠ R.base := fun h => hyu (by rw [← h, R.M.α_α])
    have h2 : R.M.α y ≠ R.M.α R.base := fun h => hym (R.M.α.injective h)
    rw [hgid y hym hyu, hgid _ h1 h2]
    exact CombMap.withσ_eqvGen_α y

/-- **Removing the marked leaf.**  If the marked vertex of a raw picture is a leaf carrying the
letter `⟨s, a⟩` with `a ≠ 1`, deleting it together with its edge gives a defect picture of type
`s` and defect `a`, with chosen dart `σ u` (`u = α base`). -/
def uncap : C.DefectPicture s a where
  M := R.M.eraseEdge R.M.σ R.base
  lab := R.lab ∘ Subtype.val
  b := ⟨R.M.σ (R.M.α R.base), R.σ_leafPartner_ne_base hfix, R.σ_leafPartner_ne hlab ha⟩
  connected := R.uncap_connected hfix hlab ha
  spherical := by
    have hV := R.uncap_numVertices hfix hlab ha
    have hF := R.uncap_numFaces hfix hlab ha
    have hE := CombMap.eraseEdge_numEdges (M := R.M) R.M.σ R.base
    have h := R.spherical
    unfold CombMap.euler at h ⊢
    omega
  type_σ := by
    intro z
    have hz : ¬ R.M.σ.SameCycle R.base z.val := fun h => z.2.1 (R.marked_eq_base_of_fixed hfix h)
    have hw : R.M.σ.SameCycle z.val ((R.M.eraseEdge R.M.σ R.base).σ z).val :=
      (sameCycle_erase2_iff z.2.1 z.2.2 ((R.M.eraseEdge R.M.σ R.base).σ z).2.1
        ((R.M.eraseEdge R.M.σ R.base).σ z).2.2).1 ⟨1, by simp; rfl⟩
    exact R.type_eq_of_sameCycle hz hw
  type_b := by
    change (R.lab (R.M.σ (R.M.α R.base))).1 = s
    rw [R.type_eq_of_sameCycle R.not_marked_leafPartner ⟨1, by simp⟩, R.lab_leafPartner hlab]
  local_eq := by
    intro z hz
    rw [CombMap.eraseEdge_sameCycle_iff] at hz
    have hz' : ¬ R.M.σ.SameCycle (R.M.α R.base) z.val := fun h =>
      hz ((show R.M.σ.SameCycle (R.M.σ (R.M.α R.base)) (R.M.α R.base) from ⟨-1, by simp⟩).trans h)
    have hzm : ¬ R.M.σ.SameCycle R.base z.val := fun h => z.2.1 (R.marked_eq_base_of_fixed hfix h)
    change cycleWord (R.M.eraseEdge R.M.σ R.base).σ ((C.letterWord ∘ R.lab) ∘ Subtype.val) z = 1
    rw [CombMap.eraseEdge_cycleWord, R.erase2_leaf_eq hfix,
      cycleWord_congr _ (erasePt_pow_apply_of_not_sameCycle hz')]
    exact R.local_eq _ hzm
  defect_word := by
    change cycleWord (R.M.eraseEdge R.M.σ R.base).σ ((C.letterWord ∘ R.lab) ∘ Subtype.val)
      ⟨R.M.σ (R.M.α R.base), _⟩ = _
    rw [CombMap.eraseEdge_cycleWord, R.erase2_leaf_eq hfix]
    have h1 := cycleWord_erasePt_apply (C.letterWord ∘ R.lab) (R.σ_leafPartner_ne hlab ha)
    rw [R.local_eq _ (fun h => R.not_marked_leafPartner (h.trans ⟨-1, by simp⟩)),
      Function.comp_apply, R.lab_leafPartner hlab] at h1
    have h2 : C.letterWord ⟨s, a⁻¹⟩ = (C.letterWord ⟨s, a⟩)⁻¹ := map_inv _ _
    rw [h2] at h1
    exact (mul_inv_eq_one.1 h1.symm)
  edge := by
    intro z
    have hz : ¬ R.M.σ.SameCycle R.base z.val := fun h => z.2.1 (R.marked_eq_base_of_fixed hfix h)
    have hαz : ¬ R.M.σ.SameCycle R.base (R.M.α z.val) := fun h =>
      z.2.2 ((R.M.α_α z.val).symm.trans (congrArg R.M.α (R.marked_eq_base_of_fixed hfix h)))
    exact R.edge_interior z.val hz hαz

theorem uncap_numEdges : (R.uncap hfix hlab ha).M.numEdges + 1 = R.M.numEdges :=
  CombMap.eraseEdge_numEdges (M := R.M) R.M.σ R.base

theorem uncap_counts :
    (R.uncap hfix hlab ha).M.numVertices + 1 = R.M.numVertices ∧
    (R.uncap hfix hlab ha).M.numEdges + 1 = R.M.numEdges ∧
    (R.uncap hfix hlab ha).M.numFaces = R.M.numFaces :=
  ⟨R.uncap_numVertices hfix hlab ha, R.uncap_numEdges hfix hlab ha, R.uncap_numFaces hfix hlab ha⟩

end Uncap

end RawPicture

namespace LocalPicture

variable {L : C.LocalPicture}

/-- **A least local picture yields a nonidentity defect picture**, of the same type `k` and
defect `g`, with one edge fewer; this defect picture is least by edge count among all defect
pictures with nonidentity defect (of any type). -/
theorem IsLeast.exists_defectPicture (hL : L.IsLeast) :
    ∃ Δ : C.DefectPicture L.k L.g, Δ.M.numEdges + 1 = L.R.M.numEdges ∧
      ∀ (s : V ⊕ T) (P : C.loc s) (Δ' : C.DefectPicture s P), P ≠ 1 →
        Δ.M.numEdges ≤ Δ'.M.numEdges := by
  obtain ⟨hfix, hlab⟩ := hL.marked_degree_one
  refine ⟨L.R.uncap hfix hlab L.ne_one, L.R.uncap_numEdges hfix hlab L.ne_one, ?_⟩
  intro s P Δ' hP
  have h1 := hL ⟨s, P, hP, Δ'.cap⟩
  have h2 := Δ'.cap_numEdges
  have h3 := L.R.uncap_numEdges hfix hlab L.ne_one
  simp only at h1
  omega

end LocalPicture

/-- **A typed exceptional vertex.**  If a nonidentity element `a` of an index group dies in the
colimit (`ι v a = 1`), then some local group (index or triple, possibly different from `v`)
has a nonidentity element `P` admitting a defect picture.  No degree, face-length or girth
bound is claimed. -/
theorem exists_defectPicture_of_ι_eq_one {v : V} {a : C.A v} (ha : a ≠ 1)
    (h : C.ι (Sum.inl v) a = 1) :
    ∃ (s : V ⊕ T) (P : C.loc s), P ≠ 1 ∧ Nonempty (C.DefectPicture s P) := by
  obtain ⟨L, hL⟩ := LocalPicture.exists_isLeast_of_ι_eq_one ha h
  obtain ⟨Δ, -⟩ := hL.exists_defectPicture
  exact ⟨L.k, L.g, L.ne_one, ⟨Δ⟩⟩

end ConeComplex

end TheoremA
