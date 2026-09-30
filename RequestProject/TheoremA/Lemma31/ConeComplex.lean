module

public import Mathlib

/-!
# Simple complexes of groups over the cone on a bipartite graph

This file sets up the general statement behind Lemma 3.1 of the manuscript.

Let `L` be a bipartite graph with vertex classes `V` ("indices") and `T` ("triangles"), given by an
incidence relation `inc : V → T → Prop`.  A *cone complex of groups* over `L` assigns a group `A v`
to every `v ∈ V`, a group `B t` to every `t ∈ T`, and a homomorphism `φ v t : A v →* B t` to every
incident pair.  Geometrically this is the simple complex of groups over the poset
`{o} ∪ V ∪ T` (with `t < v < o` whenever `inc v t`) whose local group at the cone point `o` is
trivial; its order complex is the cone on `L`.

The *colimit* `C.colim` is the free product of all local groups modulo the identifications
`a = φ v t a`.  It is the fundamental group of the complex of groups.

`ConeComplex.NPC` is the non-positive-curvature condition of the manuscript for the metric in
which every triangle `(o, v, t)` has angles `π/6, π/2, π/3`:

* the maps `φ v t` are injective;
* at every `t ∈ T`, the images of two different incident groups intersect trivially (this is
  exactly the statement that the point–coset incidence graph at `t` has no cycle of length four,
  i.e. girth at least six);
* the graph `L` itself has girth at least twelve.

(The link at `v` is a complete bipartite graph, so it imposes no condition.)

`ConeDevelopable` is the statement that every such non-positively curved cone complex of groups is
developable, i.e. all local groups embed in the colimit (Bridson–Haefliger, II.12.28, in this
special case).
-/

@[expose] public section

namespace TheoremA

universe u w

/-- A simple complex of groups over the cone on the bipartite graph with incidence `inc`. -/
structure ConeComplex (V T : Type w) where
  /-- The incidence relation of the bipartite graph `L`. -/
  inc : V → T → Prop
  /-- Local groups at the index vertices. -/
  A : V → Type u
  /-- Local groups at the triangle vertices. -/
  B : T → Type u
  [grpA : ∀ v, Group (A v)]
  [grpB : ∀ t, Group (B t)]
  /-- The structure maps. -/
  φ : ∀ v t, inc v t → A v →* B t

attribute [instance] ConeComplex.grpA ConeComplex.grpB

namespace ConeComplex

variable {V T : Type w} (C : ConeComplex.{u, w} V T)

/-- The family of all local groups, indexed by `V ⊕ T`. -/
def loc : V ⊕ T → Type u
  | .inl v => C.A v
  | .inr t => C.B t

instance instGroupLoc : ∀ x, Group (C.loc x)
  | .inl v => C.grpA v
  | .inr t => C.grpB t

/-- The identification relators `a · (φ v t a)⁻¹` in the free product of the local groups. -/
def rels : Set (Monoid.CoprodI C.loc) :=
  {x | ∃ (v : V) (t : T) (h : C.inc v t) (a : C.A v),
    x = Monoid.CoprodI.of (i := Sum.inl v) a *
      (Monoid.CoprodI.of (i := Sum.inr t) (C.φ v t h a))⁻¹}

/-- The colimit (fundamental group) of the cone complex of groups. -/
abbrev colim : Type _ := Monoid.CoprodI C.loc ⧸ Subgroup.normalClosure C.rels

/-- The canonical homomorphisms from the local groups to the colimit. -/
def ι (x : V ⊕ T) : C.loc x →* C.colim :=
  (QuotientGroup.mk' _).comp (Monoid.CoprodI.of (i := x))

theorem ι_inl_eq (v : V) (t : T) (h : C.inc v t) (a : C.A v) :
    C.ι (Sum.inl v) a = C.ι (Sum.inr t) (C.φ v t h a) := by
  have hmem : Monoid.CoprodI.of (i := Sum.inl v) a *
      (Monoid.CoprodI.of (i := Sum.inr t) (C.φ v t h a))⁻¹ ∈ Subgroup.normalClosure C.rels :=
    Subgroup.subset_normalClosure ⟨v, t, h, a, rfl⟩
  have := (QuotientGroup.eq_one_iff _).mpr hmem
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at this
  exact this

/-- The bipartite graph `L` as a simple graph on `V ⊕ T`. -/
def graph : SimpleGraph (V ⊕ T) where
  Adj x y := match x, y with
    | .inl v, .inr t => C.inc v t
    | .inr t, .inl v => C.inc v t
    | _, _ => False
  symm := ⟨by
    rintro (a | a) (b | b) h <;> simp_all⟩
  loopless := ⟨fun v => by cases v <;> simp⟩

/-- Non-positive curvature for the `(π/6, π/2, π/3)` metric: injective structure maps, pairwise
trivial intersections of the incident groups at every triangle vertex (link girth `≥ 6`), and
`girth(L) ≥ 12`. -/
structure NPC : Prop where
  φ_injective : ∀ v t (h : C.inc v t), Function.Injective (C.φ v t h)
  inter_trivial : ∀ (v v' : V) (t : T) (h : C.inc v t) (h' : C.inc v' t), v ≠ v' →
    ∀ (a : C.A v) (a' : C.A v'), C.φ v t h a = C.φ v' t h' a' → a = 1
  girth : 12 ≤ C.graph.egirth

end ConeComplex

/-- **Developability of non-positively curved cone complexes of groups** (Bridson–Haefliger,
II.12.28, specialised to the cone on a bipartite graph with the `(π/6, π/2, π/3)` metric): all
local groups embed in the colimit. -/
def ConeDevelopable : Prop :=
  ∀ (V T : Type w) (C : ConeComplex.{u, w} V T), C.NPC → ∀ x, Function.Injective (C.ι x)

end TheoremA
