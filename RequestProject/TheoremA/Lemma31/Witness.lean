module

public import RequestProject.TheoremA.Lemma31.Iso
public import RequestProject.TheoremA.Lemma31.EulerCounting

/-!
# The reduced-picture witness lemma and Lemma 3.1

This file organises the combinatorial proof of the injectivity statement behind Lemma 3.1
(Lemma 5.1 of the expanded manuscript) into

1. a **witness lemma** (`TheoremA.WitnessLemma`): if a nonidentity element of an index group
   maps to `1` in the colimit of a non-positively curved cone complex of groups, there is a
   finite connected labelled bipartite map (`TheoremA.ConeComplex.PictureWitness`) on the sphere
   whose triple vertices have degree `≥ 3`, whose index vertices except possibly one have degree
   `≥ 2`, and whose face boundaries have `≥ 12` darts;
2. the **Euler counting** (`TheoremA.ConeComplex.PictureWitness.false`, from
   `EulerCounting.lean`): no such map exists, since the bounds force `χ ≤ 1`;
3. the conclusion: all index groups embed in the colimit (`coneIndexDevelopable_of_witnessLemma`),
   and hence Lemma 3.1 (`lemma31_of_coneIndexDevelopable`, via the isomorphism
   `K_Σ(G) ≃* colim` of `Iso.lean`).

Steps 2 and 3 are proved.  Step 1 is not needed any more: Lemma 3.1 is now proved directly in
`Lemma31/Geometric.lean` (`TheoremA.lemma31`), and `TheoremA.witnessLemma` is proved there
vacuously (its hypotheses are contradictory).
This file also records the local algebraic facts at a triple vertex that the reduction theory
needs for the degree bound (b) (`ConeComplex.NPC.eq_one_of_φ_eq_one`,
`ConeComplex.NPC.eq_one_of_φ_mul_φ_eq_one`, `ConeComplex.NPC.eq_inv_of_φ_mul_φ_eq_one`); the
graph-theoretic input for the face bound (d) is
`SimpleGraph.egirth_le_length_of_nonBacktracking`.
-/

@[expose] public section

namespace TheoremA

universe u w

namespace ConeComplex

variable {V T : Type w} (C : ConeComplex.{u, w} V T)

/-! ### Local facts at a triple vertex -/

/-- A one-edge relation at a triple vertex is trivial (injectivity of the structure maps). -/
theorem NPC.eq_one_of_φ_eq_one (hC : C.NPC) {v : V} {t : T} (h : C.inc v t) {a : C.A v}
    (ha : C.φ v t h a = 1) : a = 1 :=
  hC.φ_injective v t h (ha.trans (map_one _).symm)

/-- A two-edge relation at a triple vertex between *distinct* index types is trivial (trivial
pairwise intersections). -/
theorem NPC.eq_one_of_φ_mul_φ_eq_one (hC : C.NPC) {v v' : V} {t : T} (h : C.inc v t)
    (h' : C.inc v' t) (hne : v ≠ v') {a : C.A v} {a' : C.A v'}
    (ha : C.φ v t h a * C.φ v' t h' a' = 1) : a = 1 ∧ a' = 1 := by
  have e : C.φ v t h a = C.φ v' t h' a'⁻¹ := by
    rw [map_inv]; exact eq_inv_of_mul_eq_one_left ha
  have ha1 := hC.inter_trivial v v' t h h' hne a a'⁻¹ e
  subst ha1
  refine ⟨rfl, ?_⟩
  rw [map_one, one_mul] at ha
  exact hC.eq_one_of_φ_eq_one C h' ha

/-- A two-edge relation at a triple vertex between edges of the *same* index type forces the two
labels to be mutually inverse: such a pair of edges can be cancelled (a reduction move). -/
theorem NPC.eq_inv_of_φ_mul_φ_eq_one (hC : C.NPC) {v : V} {t : T} (h : C.inc v t)
    {a a' : C.A v} (ha : C.φ v t h a * C.φ v t h a' = 1) : a' = a⁻¹ := by
  rw [← map_mul] at ha
  exact eq_inv_of_mul_eq_one_right (hC.eq_one_of_φ_eq_one C h ha)

/-! ### Picture witnesses -/

/-- A **picture witness** for the cone complex of groups `C`: a finite connected bipartite
combinatorial map on the sphere whose triple vertices are labelled by triangles `t ∈ T` and whose
index vertices are labelled by indices `v ∈ V`, every edge joining an index vertex `v` to a
triple vertex `t` with `v` incident to `t`, such that

* (b) every triple vertex has degree `≥ 3`;
* (c) every index vertex except possibly one has degree `≥ 2`;
* (d) every face boundary has at least `12` darts;
* (e) `V_T + V_I - E + F = 2`. -/
structure PictureWitness where
  /-- The underlying bipartite map. -/
  M : BipartiteMap
  /-- The triangle labelling the triple vertex of an edge. -/
  tripleLabel : M.E → T
  /-- The index labelling the index vertex of an edge. -/
  indexLabel : M.E → V
  /-- (a) Every edge joins an index to an incident triangle. -/
  inc_label : ∀ e, C.inc (indexLabel e) (tripleLabel e)
  /-- (a) The label of a triple vertex is well defined. -/
  tripleLabel_σ : ∀ e, tripleLabel (M.σ (e, true)).1 = tripleLabel e
  /-- (a) The label of an index vertex is well defined. -/
  indexLabel_σ : ∀ e, indexLabel (M.σ (e, false)).1 = indexLabel e
  /-- The map is connected. -/
  connected : ∀ d d' : M.E × Bool, ∃ g ∈ Subgroup.closure {M.σ, M.α}, g d = d'
  /-- (b) Triple vertices have degree at least `3`. -/
  degree_triple : ∀ e, 3 ≤ M.degree (e, true)
  /-- (c) At most one index vertex (the exceptional one) has degree less than `2`. -/
  degree_index : ∀ e e' : M.E, M.degree (e, false) < 2 → M.degree (e', false) < 2 →
    M.σ.SameCycle (e, false) (e', false)
  /-- (d) Every face boundary has at least `12` darts. -/
  faceLength_ge : ∀ d, 12 ≤ M.faceLength d
  /-- (e) The map is spherical. -/
  spherical : M.euler = 2

/-- **No picture witness exists**: the degree and face bounds force `χ ≤ 1`. -/
theorem PictureWitness.false {C : ConeComplex.{u, w} V T} (W : C.PictureWitness) : False :=
  W.M.euler_ne_two W.degree_triple W.degree_index W.faceLength_ge W.spherical

end ConeComplex

/-- **The witness lemma** (statement): if a nonidentity element of an index group of a
non-positively curved cone complex of groups maps to `1` in the colimit, then there is a picture
witness. -/
def WitnessLemma : Prop :=
  ∀ (V T : Type w) (C : ConeComplex.{u, w} V T), C.NPC → ∀ (v : V) (a : C.A v), a ≠ 1 →
    C.ι (Sum.inl v) a = 1 → Nonempty C.PictureWitness

/-- Developability at the index vertices: in a non-positively curved cone complex of groups, every
index group embeds in the colimit.  (This is the part of `ConeDevelopable` used for Lemma 3.1.) -/
def ConeIndexDevelopable : Prop :=
  ∀ (V T : Type w) (C : ConeComplex.{u, w} V T), C.NPC → ∀ v : V,
    Function.Injective (C.ι (Sum.inl v))

theorem coneIndexDevelopable_of_coneDevelopable (h : ConeDevelopable.{u, w}) :
    ConeIndexDevelopable.{u, w} :=
  fun V T C hC v => h V T C hC (Sum.inl v)

/-- **The witness lemma implies developability at the index vertices** (proved: the Euler count
rules out every picture witness). -/
theorem coneIndexDevelopable_of_witnessLemma (h : WitnessLemma.{u, w}) :
    ConeIndexDevelopable.{u, w} := by
  intro V T C hC v
  rw [injective_iff_map_eq_one]
  intro a ha
  by_contra hne
  exact (h V T C hC v a hne ha).some.false

/-- **Lemma 3.1 from developability at the index vertices** (proved).  The comparison uses the
isomorphism `K_Σ(G) ≃* colim` (`diagramGroup_ι_injective_iff`), not merely a map in one
direction. -/
theorem lemma31_of_coneIndexDevelopable (h : ConeIndexDevelopable.{u, 0}) : Lemma31.{u} := by
  intro r T hw hg G _ v
  exact (diagramGroup_ι_injective_iff r T hw G v).mpr
    (h _ _ (tripleComplex r T G) (tripleComplex_npc r T hw hg G) v)

/-- **Lemma 3.1 from the witness lemma** (proved). -/
theorem lemma31_of_witnessLemma (h : WitnessLemma.{u, 0}) : Lemma31.{u} :=
  lemma31_of_coneIndexDevelopable (coneIndexDevelopable_of_witnessLemma h)

/- The declaration `witnessLemma` (previously an unproved `sorry` here) has moved to
`Lemma31/Geometric.lean`, where it is proved: its hypotheses are contradictory by the geometric
argument of `Lemma31/Picture/` (`TheoremA.coneIndexDevelopable`). -/

end TheoremA
