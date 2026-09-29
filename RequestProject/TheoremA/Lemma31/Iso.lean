module

public import RequestProject.TheoremA.Lemma31.Reduction

/-!
# `K_Σ(G)` is isomorphic to the colimit of the cone complex of groups

`TheoremA.toColim` (in `Reduction.lean`) is the map `K_Σ(G) → colim` sending `g_v` to the image of
`g` in the local group at `v`.  Here we construct the inverse map `colim → K_Σ(G)`: at the index
`v` it is `ι_v`, and at a triple `ℓ = (i, j) ⟶ k` it is `(g, h) ↦ g_i h_j`, which is a homomorphism
because `G_i` and `G_j` commute in `K_Σ(G)`; it is compatible with the structure maps
`(g,1), (1,g), (g,g)` because `g_k = g_i g_j` in `K_Σ(G)`.

* `TheoremA.fromColim` — the map `colim → K_Σ(G)`;
* `TheoremA.diagramGroupEquivColim` — `K_Σ(G) ≃* colim`, whose forward map is `toColim`.
-/

@[expose] public section

namespace TheoremA

open TripleSystem

universe u

variable (r : ℕ) (T : List Triple) (hw : WellFormed r T) (G : Type u) [Group G]

theorem diagramGroup.ι_eq_one_of_mem {x : Monoid.CoprodI fun _ : Fin r => G}
    (hx : x ∈ relators r T G) :
    (QuotientGroup.mk' (Subgroup.normalClosure (relators r T G)) x : diagramGroup r T G) = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.subset_normalClosure hx

/-- In `K_Σ(G)`, the copies `G_i` and `G_j` of a triple `(i, j) ⟶ k` commute. -/
theorem diagramGroup.commute_ι (t : Triple) (ht : t ∈ T) (hi : t.1 < r) (hj : t.2.1 < r)
    (hk : t.2.2 < r) (g h : G) :
    Commute (diagramGroup.ι r T G ⟨t.1, hi⟩ g) (diagramGroup.ι r T G ⟨t.2.1, hj⟩ h) := by
  have := diagramGroup.ι_eq_one_of_mem r T G ⟨t, ht, hi, hj, hk, Or.inl ⟨g, h, rfl⟩⟩
  rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at this
  exact this

/-- In `K_Σ(G)`, `g_k = g_i g_j` for a triple `(i, j) ⟶ k`. -/
theorem diagramGroup.ι_third (t : Triple) (ht : t ∈ T) (hi : t.1 < r) (hj : t.2.1 < r)
    (hk : t.2.2 < r) (g : G) :
    diagramGroup.ι r T G ⟨t.2.2, hk⟩ g =
      diagramGroup.ι r T G ⟨t.1, hi⟩ g * diagramGroup.ι r T G ⟨t.2.1, hj⟩ g := by
  have := diagramGroup.ι_eq_one_of_mem r T G ⟨t, ht, hi, hj, hk, Or.inr ⟨g, rfl⟩⟩
  simp only [map_mul, map_inv] at this
  rw [mul_assoc, inv_mul_eq_one] at this
  exact this

/-- The homomorphism `G × G → K_Σ(G)`, `(g, h) ↦ g_i h_j`, at the triple `ℓ = (i, j) ⟶ k`. -/
def tripleToK (l : Fin T.length) : G × G →* diagramGroup r T G :=
  MonoidHom.noncommCoprod
    (diagramGroup.ι r T G ⟨T[l].1, (hw T[l] (List.getElem_mem _)).1⟩)
    (diagramGroup.ι r T G ⟨T[l].2.1, (hw T[l] (List.getElem_mem _)).2.1⟩)
    (diagramGroup.commute_ι r T G T[l] (List.getElem_mem _) _ _
      (hw T[l] (List.getElem_mem _)).2.2.1)

/-- The local homomorphisms into `K_Σ(G)`. -/
def colimFamily : ∀ x, (tripleComplex r T G).loc x →* diagramGroup r T G
  | .inl v => diagramGroup.ι r T G v
  | .inr l => tripleToK r T hw G l

theorem tripleToK_tripleMap (l : Fin T.length) (v : ℕ) (hvr : v < r) (hv : v ∈ T[l].entries)
    (a : G) : diagramGroup.ι r T G ⟨v, hvr⟩ a = tripleToK r T hw G l (tripleMap G T[l] v a) := by
  have hmem := List.getElem_mem (l := T) l.isLt
  obtain ⟨h1, h2, h3, h12, h13, h23⟩ := hw T[l] (List.getElem_mem _)
  have third := diagramGroup.ι_third r T G T[l] hmem h1 h2 h3 a
  simp only [Triple.entries, List.mem_cons, List.not_mem_nil, or_false] at hv
  simp only [tripleToK, MonoidHom.noncommCoprod_apply]
  simp only [Fin.getElem_fin] at *
  rcases hv with h | h | h
  · rw [show (⟨v, hvr⟩ : Fin r) = ⟨_, h1⟩ from Fin.ext h, h]
    simp [tripleMap]
  · rw [show (⟨v, hvr⟩ : Fin r) = ⟨_, h2⟩ from Fin.ext h, h]
    simp [tripleMap, Ne.symm h12]
  · rw [show (⟨v, hvr⟩ : Fin r) = ⟨_, h3⟩ from Fin.ext h, h]
    simp [tripleMap, Ne.symm h13, Ne.symm h23]
    exact third

/-- The comparison map `colim → K_Σ(G)`. -/
def fromColim : (tripleComplex r T G).colim →* diagramGroup r T G := by
  refine QuotientGroup.lift _ (Monoid.CoprodI.lift (colimFamily r T hw G)) ?_
  refine Subgroup.normalClosure_le_normal ?_
  rintro x ⟨⟨v, hvr⟩, l, hv, a, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, Monoid.CoprodI.lift_of,
    Monoid.CoprodI.lift_of, mul_inv_eq_one]
  exact tripleToK_tripleMap r T hw G l v hvr hv a

theorem fromColim_ι_inl (v : Fin r) (g : G) :
    fromColim r T hw G ((tripleComplex r T G).ι (Sum.inl v) g) = diagramGroup.ι r T G v g := by
  simp only [fromColim, ConeComplex.ι, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.lift_mk, Monoid.CoprodI.lift_of]
  rfl

theorem fromColim_ι_inr (l : Fin T.length) (p : G × G) :
    fromColim r T hw G ((tripleComplex r T G).ι (Sum.inr l) p) = tripleToK r T hw G l p := by
  simp only [fromColim, ConeComplex.ι, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.lift_mk, Monoid.CoprodI.lift_of]
  rfl

theorem fromColim_comp_toColim :
    (fromColim r T hw G).comp (toColim r T hw G) = MonoidHom.id _ := by
  refine QuotientGroup.monoidHom_ext _ (Monoid.CoprodI.ext_hom _ _ fun v => ?_)
  ext g
  have := fromColim_ι_inl r T hw G v g
  rw [← toColim_ι r T hw G v g] at this
  exact this

theorem toColim_comp_fromColim :
    (toColim r T hw G).comp (fromColim r T hw G) = MonoidHom.id _ := by
  refine QuotientGroup.monoidHom_ext _ (Monoid.CoprodI.ext_hom _ _ fun x => ?_)
  ext p
  change toColim r T hw G (fromColim r T hw G ((tripleComplex r T G).ι x p)) =
    (tripleComplex r T G).ι x p
  rcases x with v | l
  · rw [fromColim_ι_inl, toColim_ι]
  · rw [fromColim_ι_inr]
    have hd := hw T[l] (List.getElem_mem _)
    obtain ⟨g, h⟩ := p
    simp only [tripleToK, MonoidHom.noncommCoprod_apply, map_mul, toColim_ι]
    have mi : ((⟨T[l].1, hd.1⟩ : Fin r) : ℕ) ∈ T[l].entries := by simp [Triple.entries]
    have mj : ((⟨T[l].2.1, hd.2.1⟩ : Fin r) : ℕ) ∈ T[l].entries := by simp [Triple.entries]
    rw [(tripleComplex r T G).ι_inl_eq _ l mi, (tripleComplex r T G).ι_inl_eq _ l mj,
      ← map_mul]
    congr 1
    change tripleMap G T[l] T[l].1 g * tripleMap G T[l] T[l].2.1 h = (g, h)
    have hne : T[(l : ℕ)].2.1 ≠ T[(l : ℕ)].1 := hd.2.2.2.1.symm
    simp [tripleMap, hne]

/-- **`K_Σ(G)` is isomorphic to the colimit of the cone complex of groups**, compatibly with the
canonical maps from the index groups (`diagramGroupEquivColim_ι`). -/
def diagramGroupEquivColim : diagramGroup r T G ≃* (tripleComplex r T G).colim :=
  MonoidHom.toMulEquiv (toColim r T hw G) (fromColim r T hw G)
    (fromColim_comp_toColim r T hw G) (toColim_comp_fromColim r T hw G)

theorem diagramGroupEquivColim_ι (v : Fin r) (g : G) :
    diagramGroupEquivColim r T hw G (diagramGroup.ι r T G v g) =
      (tripleComplex r T G).ι (Sum.inl v) g :=
  toColim_ι r T hw G v g

include hw in
/-- Hence `ι_v : G → K_Σ(G)` is injective **if and only if** the canonical map from the local
group at `v` into the colimit of the cone complex of groups is injective. -/
theorem diagramGroup_ι_injective_iff (v : Fin r) :
    Function.Injective (diagramGroup.ι r T G v) ↔
      Function.Injective ((tripleComplex r T G).ι (Sum.inl v)) := by
  have e : ⇑((tripleComplex r T G).ι (Sum.inl v)) =
      ⇑(diagramGroupEquivColim r T hw G) ∘ ⇑(diagramGroup.ι r T G v) := by
    funext g; exact (diagramGroupEquivColim_ι r T hw G v g).symm
  rw [e]
  exact ((MulEquiv.injective _).of_comp_iff _).symm

end TheoremA
