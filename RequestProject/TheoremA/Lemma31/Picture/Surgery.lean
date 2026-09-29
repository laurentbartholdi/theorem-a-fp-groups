module

public import RequestProject.TheoremA.Lemma31.Picture.EraseEdge

/-!
# Labelled surgery: raw-picture conditions without connectivity

`ConeComplex.PrePicture C x` carries all the labelling conditions of a raw picture for `x`
(type, local, interior-edge, boundary-edge and marked-word conditions) but neither connectivity
nor `χ = 2`.

* `PrePicture.toRaw` : a connected pre-picture with `χ = 2` is a raw picture;
* `PrePicture.component` : the connected component of the marked vertex, with the restricted
  labels, is again a pre-picture for the same element;
* `PrePicture.ofEraseEdge` : the labelled version of `CombMap.eraseEdge` — the five labelling
  conditions for the erased map, stated on the full dart set for the retained darts, in terms of
  the permutation `erase2 π a (α a)` and the cycles of `π`.
-/

@[expose] public section

namespace TheoremA

universe u w

namespace ConeComplex

open Picture Equiv Function

variable {V T : Type w} (C : ConeComplex.{u, w} V T)

/-- A labelled map satisfying all conditions of a raw picture for `x` except connectivity and
`χ = 2`. -/
structure PrePicture (x : Monoid.CoprodI C.loc) where
  /-- The underlying combinatorial map. -/
  M : CombMap
  /-- The letters on the darts. -/
  lab : M.D → C.Letter
  /-- The base dart. -/
  base : M.D
  type_σ : ∀ d, ¬ M.σ.SameCycle base d → (lab (M.σ d)).1 = (lab d).1
  local_eq : ∀ d, ¬ M.σ.SameCycle base d → cycleWord M.σ (C.letterWord ∘ lab) d = 1
  edge_interior : ∀ d, ¬ M.σ.SameCycle base d → ¬ M.σ.SameCycle base (M.α d) →
    C.RelEdge (lab d) (lab (M.α d)) ∨ C.RelEdge (lab (M.α d)) (lab d)
  edge_boundary : ∀ d, M.σ.SameCycle base d →
    ¬ M.σ.SameCycle base (M.α d) ∧ lab (M.α d) = (lab d).inv
  boundary_word : cycleWord M.σ (C.letterWord ∘ lab) base = x

variable {C}

namespace PrePicture

variable {x : Monoid.CoprodI C.loc} (P : C.PrePicture x)

/-- A connected pre-picture with `χ = 2` is a raw picture. -/
def toRaw (hc : P.M.Connected) (hs : P.M.euler = 2) : C.RawPicture x where
  M := P.M
  lab := P.lab
  base := P.base
  connected := hc
  spherical := hs
  type_σ := P.type_σ
  local_eq := P.local_eq
  edge_interior := P.edge_interior
  edge_boundary := P.edge_boundary
  boundary_word := P.boundary_word

open Classical in
theorem component_sameCycle_iff {d e : (P.M.component P.base).D} :
    (P.M.component P.base).σ.SameCycle d e ↔ P.M.σ.SameCycle d.val e.val := by
  exact CombMap.restrict_sameCycle_iff _ _ _

/-- The component of the marked vertex. -/
noncomputable def component : C.PrePicture x where
  M := P.M.component P.base
  lab := P.lab ∘ Subtype.val
  base := ⟨P.base, Relation.EqvGen.refl _⟩
  type_σ d hd := P.type_σ d.val fun h => hd ((P.component_sameCycle_iff).2 h)
  local_eq d hd := by
    classical
    refine (CombMap.restrict_cycleWord (M := P.M) _ _ _ (C.letterWord ∘ P.lab) d).trans ?_
    exact P.local_eq d.val fun h => hd ((P.component_sameCycle_iff).2 h)
  edge_interior d hd hd' := P.edge_interior d.val (fun h => hd ((P.component_sameCycle_iff).2 h))
    (fun h => hd' ((P.component_sameCycle_iff).2 h))
  edge_boundary d hd := by
    obtain ⟨h1, h2⟩ := P.edge_boundary d.val ((P.component_sameCycle_iff).1 hd)
    exact ⟨fun h => h1 ((P.component_sameCycle_iff).1 h), h2⟩
  boundary_word := by
    classical
    exact (CombMap.restrict_cycleWord (M := P.M) _ _ _ (C.letterWord ∘ P.lab) _).trans
      P.boundary_word

theorem component_M : P.component.M = P.M.component P.base := rfl

end PrePicture

/-- **Labelled edge deletion.**  The map `M.eraseEdge π a` with the restricted labels `lab` and
base `base` is a pre-picture for `x`, provided the five labelling conditions hold at the retained
darts (stated on the full dart set; "marked" means "in the same `π`-cycle as `base`", which for
retained darts is the same as in the same cycle of the erased rotation). -/
def PrePicture.ofEraseEdge {x : Monoid.CoprodI C.loc} (M : CombMap) (π : Perm M.D) (a : M.D)
    (lab : M.D → C.Letter) (base : M.D) (hb : base ≠ a ∧ base ≠ M.α a)
    (htype : ∀ z, z ≠ a → z ≠ M.α a → ¬ π.SameCycle base z →
      (lab (erase2 π a (M.α a) z)).1 = (lab z).1)
    (hlocal : ∀ z, z ≠ a → z ≠ M.α a → ¬ π.SameCycle base z →
      cycleWord (erase2 π a (M.α a)) (C.letterWord ∘ lab) z = 1)
    (hint : ∀ z, z ≠ a → z ≠ M.α a → ¬ π.SameCycle base z → ¬ π.SameCycle base (M.α z) →
      C.RelEdge (lab z) (lab (M.α z)) ∨ C.RelEdge (lab (M.α z)) (lab z))
    (hbd : ∀ z, z ≠ a → z ≠ M.α a → π.SameCycle base z →
      ¬ π.SameCycle base (M.α z) ∧ lab (M.α z) = (lab z).inv)
    (hword : cycleWord (erase2 π a (M.α a)) (C.letterWord ∘ lab) base = x) :
    C.PrePicture x where
  M := M.eraseEdge π a
  lab := lab ∘ Subtype.val
  base := ⟨base, hb⟩
  type_σ d hd := htype d.val d.2.1 d.2.2 fun h => hd ((CombMap.eraseEdge_sameCycle_iff π a).2 h)
  local_eq d hd := (CombMap.eraseEdge_cycleWord π a (C.letterWord ∘ lab) d).trans
    (hlocal d.val d.2.1 d.2.2 fun h => hd ((CombMap.eraseEdge_sameCycle_iff π a).2 h))
  edge_interior d hd hd' := hint d.val d.2.1 d.2.2
    (fun h => hd ((CombMap.eraseEdge_sameCycle_iff π a).2 h))
    (fun h => hd' ((CombMap.eraseEdge_sameCycle_iff π a).2 h))
  edge_boundary d hd := by
    obtain ⟨h1, h2⟩ := hbd d.val d.2.1 d.2.2 ((CombMap.eraseEdge_sameCycle_iff π a).1 hd)
    exact ⟨fun h => h1 ((CombMap.eraseEdge_sameCycle_iff π a).1 h), h2⟩
  boundary_word := (CombMap.eraseEdge_cycleWord π a (C.letterWord ∘ lab) ⟨base, hb⟩).trans hword

end ConeComplex

end TheoremA
