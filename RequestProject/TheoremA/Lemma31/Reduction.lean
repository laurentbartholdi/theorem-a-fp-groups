module

public import RequestProject.TheoremA.Lemma31.ConeComplex
public import RequestProject.TheoremA.Reduction

/-!
# Lemma 3.1 from developability of cone complexes of groups

Following the proof of Lemma 3.1 in the manuscript, `K_Σ(G)` is compared with the colimit of the
cone complex of groups with local groups `G` at the indices and `G × G` at the triples, the maps
into the local group of `ℓ = (i, j) ⟶ k` being `g ↦ (g, 1)`, `g ↦ (1, g)`, `g ↦ (g, g)` (eq. (3.2)).

* `TheoremA.tripleComplex` is this cone complex of groups;
* `TheoremA.tripleComplex_npc`: it is non-positively curved as soon as `girth(L) ≥ 12` (the three
  subgroups `G × 1`, `1 × G`, `diag G` of `G × G` pairwise intersect trivially, even for
  non-abelian `G`);
* `TheoremA.lemma31_of_coneDevelopable`: Lemma 3.1 follows from `ConeDevelopable`.
-/

@[expose] public section

namespace TheoremA

open TripleSystem

universe u

/-- The structure map `G → G × G` attached to an index `v` of a triple `t` (eq. (3.2)). -/
def tripleMap (G : Type u) [Group G] (t : Triple) (v : ℕ) : G →* G × G :=
  if v = t.1 then MonoidHom.inl G G
  else if v = t.2.1 then MonoidHom.inr G G
  else MonoidHom.prod (MonoidHom.id G) (MonoidHom.id G)

/-- The cone complex of groups of the proof of Lemma 3.1. -/
def tripleComplex (r : ℕ) (T : List Triple) (G : Type u) [Group G] :
    ConeComplex.{u, 0} (Fin r) (Fin T.length) where
  inc v l := (v : ℕ) ∈ T[l].entries
  A _ := G
  B _ := G × G
  φ v l _ := tripleMap G T[l] v

theorem tripleComplex_graph (r : ℕ) (T : List Triple) (G : Type u) [Group G] :
    (tripleComplex r T G).graph = incidenceGraph r T := by
  ext x y
  cases x <;> cases y <;> rfl

theorem tripleMap_inter_trivial (G : Type u) [Group G] (t : Triple)
    (hd : t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2) (v v' : ℕ)
    (hv : v ∈ t.entries) (hv' : v' ∈ t.entries) (hne : v ≠ v') (a a' : G)
    (h : tripleMap G t v a = tripleMap G t v' a') : a = 1 := by
  simp only [Triple.entries, List.mem_cons, List.not_mem_nil, or_false] at hv hv'
  obtain ⟨h12, h13, h23⟩ := hd
  have h21 := Ne.symm h12
  have h31 := Ne.symm h13
  have h32 := Ne.symm h23
  rcases hv with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl <;>
    simp_all [tripleMap, Prod.ext_iff]
  grind

theorem tripleComplex_npc (r : ℕ) (T : List Triple) (hw : WellFormed r T)
    (hg : 12 ≤ (incidenceGraph r T).egirth) (G : Type u) [Group G] :
    (tripleComplex r T G).NPC where
  φ_injective v l _ := by
    intro a b hab
    change tripleMap G T[l] v a = tripleMap G T[l] v b at hab
    unfold tripleMap at hab
    split_ifs at hab <;> simp_all [Prod.ext_iff]
  inter_trivial v v' l h h' hne a a' e := by
    have hd := hw T[l] (List.getElem_mem _)
    exact tripleMap_inter_trivial G T[l] ⟨hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2⟩ v v' h h'
      (fun hvv => hne (Fin.ext hvv)) a a' e
  girth := by rw [tripleComplex_graph]; exact hg

/-- The comparison map `K_Σ(G) → colim`, sending `g_v` to the image of `g` in the local group at
`v`. -/
def toColim (r : ℕ) (T : List Triple) (hw : WellFormed r T) (G : Type u) [Group G] :
    diagramGroup r T G →* (tripleComplex r T G).colim := by
  refine QuotientGroup.lift _
    (Monoid.CoprodI.lift fun v => (tripleComplex r T G).ι (Sum.inl v)) ?_
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨t, ht, hi, hj, hk, hx⟩
  obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.mp ht
  have hd := hw T[l] ht
  have key : ∀ (v : Fin r) (hv : (v : ℕ) ∈ T[l].entries) (g : G),
      (tripleComplex r T G).ι (Sum.inl v) g = (tripleComplex r T G).ι (Sum.inr ⟨l, hl⟩) (tripleMap G T[l] v g) :=
    fun v hv g => (tripleComplex r T G).ι_inl_eq v ⟨l, hl⟩ hv g
  have mi : ((⟨T[l].1, hi⟩ : Fin r) : ℕ) ∈ T[l].entries := by simp [Triple.entries]
  have mj : ((⟨T[l].2.1, hj⟩ : Fin r) : ℕ) ∈ T[l].entries := by simp [Triple.entries]
  have mk : ((⟨T[l].2.2, hk⟩ : Fin r) : ℕ) ∈ T[l].entries := by simp [Triple.entries]
  have ti : ∀ g : G, tripleMap G T[l] T[l].1 g = (g, 1) := by
    intro g; simp [tripleMap]
  have tj : ∀ g : G, tripleMap G T[l] T[l].2.1 g = (1, g) := by
    intro g; simp [tripleMap, hd.2.2.2.1.symm]
  have tk : ∀ g : G, tripleMap G T[l] T[l].2.2 g = (g, g) := by
    intro g; simp [tripleMap, hd.2.2.2.2.1.symm, hd.2.2.2.2.2.symm]
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  rcases hx with ⟨g, h, rfl⟩ | ⟨g, rfl⟩
  · simp only [ofIdx, map_commutatorElement, Monoid.CoprodI.lift_of]
    erw [key _ mi, key _ mj]
    rw [ti, tj, ← map_commutatorElement, commutatorElement_eq_one_iff_commute.mpr, map_one]
    exact Commute.prod (Commute.one_right g) (Commute.one_left h)
  · simp only [ofIdx, map_mul, map_inv, Monoid.CoprodI.lift_of]
    erw [key _ mi, key _ mj, key _ mk]
    change ((tripleComplex r T G).ι (Sum.inr ⟨l, hl⟩) (tripleMap G T[l] T[l].2.2 g))⁻¹ *
      (tripleComplex r T G).ι (Sum.inr ⟨l, hl⟩) (tripleMap G T[l] T[l].1 g) *
      (tripleComplex r T G).ι (Sum.inr ⟨l, hl⟩) (tripleMap G T[l] T[l].2.1 g) = 1
    rw [ti, tj, tk]
    have e0 : ((g, g) : G × G)⁻¹ * (g, 1) * (1, g) = 1 := by ext <;> simp
    have e := congrArg ((tripleComplex r T G).ι (Sum.inr ⟨l, hl⟩)) e0
    simpa only [map_mul, map_inv, map_one] using e

theorem toColim_ι (r : ℕ) (T : List Triple) (hw : WellFormed r T) (G : Type u) [Group G]
    (v : Fin r) (g : G) :
    toColim r T hw G (diagramGroup.ι r T G v g) = (tripleComplex r T G).ι (Sum.inl v) g := by
  simp [toColim, diagramGroup.ι, ofIdx]
  rfl

/-- **Lemma 3.1 from developability.**  If non-positively curved cone complexes of groups are
developable, then Lemma 3.1 holds. -/
theorem lemma31_of_coneDevelopable (hdev : ConeDevelopable.{u, 0}) : Lemma31.{u} := by
  intro r T hw hg G _ v
  have hinj := hdev _ _ (tripleComplex r T G) (tripleComplex_npc r T hw hg G) (Sum.inl v)
  intro a b hab
  apply hinj
  change (tripleComplex r T G).ι (Sum.inl v) a = (tripleComplex r T G).ι (Sum.inl v) b
  rw [← toColim_ι r T hw, ← toColim_ι r T hw, hab]

end TheoremA
