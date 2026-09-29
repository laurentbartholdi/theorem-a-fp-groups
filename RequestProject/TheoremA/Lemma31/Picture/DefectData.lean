module

public import RequestProject.TheoremA.Lemma31.Picture.Exceptional
public import RequestProject.TheoremA.Lemma31.Picture.EraseEdgeDiffFace

/-!
# Defect data, least nonidentity defects, and map-level moves

## Defect data

`ConeComplex.DefectData M lab` is the condition, on a labelled combinatorial map, of being the
underlying labelled map of a nonidentity defect picture of *some* type: connected, spherical,
every vertex carrying letters of a single local group, every edge a relator edge, and exactly one
vertex (the vertex of some dart `b`) with nonidentity product, all other vertex products being `1`.

* `DefectPicture.toDefectData` : a defect picture with `P ≠ 1` gives defect data on its map;
* `DefectData.exists_defectPicture` : conversely, defect data give a defect picture on the same
  map, of the type of the exceptional vertex, with nonidentity defect;
* `ConeComplex.IsLeastDefect M lab` : defect data with the least number of edges among all defect
  data (for all types and all nonidentity defects); `exists_isLeastDefect` shows that a least one
  exists as soon as some defect data exist.

## Map-level moves through an auxiliary raw picture

The consolidation moves of `Consolidate.lean` are stated for raw pictures, but their map-level
conclusions (connectivity, `χ = 2`, one edge fewer) only depend on the underlying map.  Given a
connected spherical map with a two-colouring `κ` of its vertices for which every edge is
bichromatic, `CombMap.auxRaw` labels it as a raw picture over a trivial cone complex (all local
groups trivial), with marked vertex at any chosen dart.  This transfers the map-level results
(`CombMap.consolidate_map`, `CombMap.consolidateDigon_map`) to arbitrary such maps.  The labels
of the auxiliary raw picture carry no information and are only used to invoke those lemmas.
-/

@[expose] public section

namespace TheoremA

universe u w

open Picture Equiv Function

/-! ### An auxiliary trivial cone complex -/

/-- The cone complex with one index, one triple, trivial local groups. -/
def trivCC : ConeComplex.{0, 0} Unit Unit where
  inc _ _ := True
  A _ := Unit
  B _ := Unit
  φ _ _ _ := 1

namespace trivCC

theorem letterWord_eq_one (p : trivCC.Letter) : trivCC.letterWord p = 1 := by
  obtain ⟨k, g⟩ := p
  cases k with
  | inl a =>
    change Monoid.CoprodI.of (i := Sum.inl a) g = 1
    exact (congrArg _ (show g = 1 from rfl)).trans (map_one _)
  | inr a =>
    change Monoid.CoprodI.of (i := Sum.inr a) g = 1
    exact (congrArg _ (show g = 1 from rfl)).trans (map_one _)

/-- The letter recording a colour. -/
def kindLetter : Bool → trivCC.Letter
  | true => ⟨Sum.inl (), (1 : Unit)⟩
  | false => ⟨Sum.inr (), (1 : Unit)⟩

theorem relEdge_kind (b : Bool) :
    trivCC.RelEdge (kindLetter b) (kindLetter (!b)) ∨
      trivCC.RelEdge (kindLetter (!b)) (kindLetter b) := by
  cases b
  · exact Or.inr ⟨(), (), trivial, (1 : Unit), rfl, rfl⟩
  · exact Or.inl ⟨(), (), trivial, (1 : Unit), rfl, rfl⟩

theorem kindLetter_inv (b : Bool) : (kindLetter b).inv = kindLetter b := by
  cases b <;> rfl

end trivCC

theorem cycleWord_const_one {D M : Type*} [Monoid M] (π : Perm D) (x : D) :
    cycleWord π (fun _ => (1 : M)) x = 1 := by
  simp [cycleWord]

namespace Picture.CombMap

variable (M : CombMap) (κ : M.D → Bool) (hκσ : ∀ x, κ (M.σ x) = κ x)
  (hκα : ∀ x, κ (M.α x) = !κ x)

include hκσ in
theorem kind_pow (x : M.D) (n : ℕ) : κ ((M.σ ^ n) x) = κ x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, hκσ, ih]

include hκσ in
theorem kind_eq_of_sameCycle {x y : M.D} (h : M.σ.SameCycle x y) : κ y = κ x := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  exact M.kind_pow κ hκσ x n

include hκσ hκα in
theorem not_sameCycle_α_of_kind (x : M.D) : ¬ M.σ.SameCycle x (M.α x) := fun h => by
  have := M.kind_eq_of_sameCycle κ hκσ h
  rw [hκα] at this
  cases hx : κ x <;> simp [hx] at this

open Classical in
/-- The auxiliary labels: darts at the vertex of `c` get the colour of their partner, all other
darts their own colour. -/
noncomputable def auxLab (c : M.D) (z : M.D) : trivCC.Letter :=
  if M.σ.SameCycle c z then trivCC.kindLetter (κ (M.α z)) else trivCC.kindLetter (κ z)

/-- **The auxiliary raw picture** over the trivial cone complex, with marked vertex at `c`. -/
noncomputable def auxRaw (hc : M.Connected) (hs : M.euler = 2) (c : M.D) : trivCC.RawPicture 1 where
  M := M
  lab := M.auxLab κ c
  base := c
  connected := hc
  spherical := hs
  type_σ := by
    intro z hz
    have hz' : ¬ M.σ.SameCycle c (M.σ z) := fun h => hz (h.trans ⟨-1, by simp⟩)
    simp only [auxLab, if_neg hz, if_neg hz', hκσ]
  local_eq := by
    intro z _
    have : (trivCC.letterWord ∘ M.auxLab κ c) = fun _ => 1 :=
      funext fun y => trivCC.letterWord_eq_one _
    rw [this, cycleWord_const_one]
  edge_interior := by
    intro z hz hz'
    simp only [auxLab, if_neg hz, if_neg hz', hκα]
    exact trivCC.relEdge_kind _
  edge_boundary := by
    intro z hz
    have hαz : ¬ M.σ.SameCycle c (M.α z) := fun h =>
      M.not_sameCycle_α_of_kind κ hκσ hκα z (hz.symm.trans h)
    refine ⟨hαz, ?_⟩
    simp only [auxLab, if_pos hz, if_neg hαz]
    rw [trivCC.kindLetter_inv]
  boundary_word := by
    have : (trivCC.letterWord ∘ M.auxLab κ c) = fun _ => 1 :=
      funext fun y => trivCC.letterWord_eq_one _
    rw [this, cycleWord_const_one]

variable {M κ}

variable (hc : M.Connected) (hs : M.euler = 2) {d : M.D} (hde : M.σ d ≠ d)
  (hk : κ (M.α (M.σ d)) = κ (M.α d))

open Classical in
/-- The consolidation pair `d, σ d` of the auxiliary raw picture. -/
noncomputable def auxPair : (M.auxRaw κ hκσ hκα hc hs d).MarkedPair where
  d := d
  e := M.σ d
  k := (trivCC.kindLetter (κ (M.α d))).1
  g₁ := (trivCC.kindLetter (κ (M.α d))).2
  g₂ := (trivCC.kindLetter (κ (M.α d))).2
  marked := Perm.SameCycle.refl _ _
  next := rfl
  ne := fun h => hde h.symm
  ne_base := hde
  lab_d := by
    change M.auxLab κ d d = _
    simp only [auxLab, if_pos (Perm.SameCycle.refl _ _)]
  lab_e := by
    change M.auxLab κ d (M.σ d) = _
    have h1 : M.σ.SameCycle d (M.σ d) := ⟨1, by simp⟩
    unfold auxLab
    rw [if_pos h1, hk]

include hκσ hκα hc hs hde hk

/-- **Consolidation at a vertex, distinct endpoints (map level).**  Let `d ≠ e = σ d` be
consecutive darts whose partners `u = α d`, `v = α e` lie at different vertices of the same
colour.  Merging the vertices of `u` and `v` and erasing the edge `{e, v}` gives a connected
spherical map with one edge fewer. -/
theorem consolidate_map (hdist : ¬ M.σ.SameCycle (M.α d) (M.α (M.σ d))) :
    (M.eraseEdge (swap (M.α d) (M.α (M.σ d)) * M.σ) (M.σ d)).Connected ∧
    (M.eraseEdge (swap (M.α d) (M.α (M.σ d)) * M.σ) (M.σ d)).euler = 2 ∧
    (M.eraseEdge (swap (M.α d) (M.α (M.σ d)) * M.σ) (M.σ d)).numEdges + 1 = M.numEdges :=
  ⟨(auxPair hκσ hκα hc hs hde hk).consolidate_connected hdist,
    (auxPair hκσ hκα hc hs hde hk).consolidate_euler hdist,
    (auxPair hκσ hκα hc hs hde hk).consolidate_numEdges'⟩

/-- **Consolidation at a vertex, digon case (map level).**  If moreover `σ v = u`, erasing the edge
`{e, v}` gives a connected spherical map with one edge fewer. -/
theorem consolidateDigon_map (hdig : M.σ (M.α (M.σ d)) = M.α d) :
    (M.eraseEdge M.σ (M.σ d)).Connected ∧ (M.eraseEdge M.σ (M.σ d)).euler = 2 ∧
    (M.eraseEdge M.σ (M.σ d)).numEdges + 1 = M.numEdges :=
  ⟨(auxPair hκσ hκα hc hs hde hk).consolidateDigon_connected hdig,
    (auxPair hκσ hκα hc hs hde hk).consolidateDigon_euler hdig,
    (auxPair hκσ hκα hc hs hde hk).consolidateDigon_numEdges'⟩

end Picture.CombMap

namespace ConeComplex

variable {V T : Type w} (C : ConeComplex.{u, w} V T)

/-- **Defect data** on a labelled map: connected, spherical, every vertex typed by one local group,
every edge a relator edge, and exactly one vertex (the vertex of some dart `b`) with nonidentity
product; all other vertex products are `1`. -/
structure DefectData (M : CombMap) (lab : M.D → C.Letter) : Prop where
  connected : M.Connected
  spherical : M.euler = 2
  type_σ : ∀ d, (lab (M.σ d)).1 = (lab d).1
  edge : ∀ d, C.RelEdge (lab d) (lab (M.α d)) ∨ C.RelEdge (lab (M.α d)) (lab d)
  exc : ∃ b, cycleWord M.σ (C.letterWord ∘ lab) b ≠ 1 ∧
    ∀ d, cycleWord M.σ (C.letterWord ∘ lab) d ≠ 1 → M.σ.SameCycle b d

/-- A **least defect**: defect data with the least number of edges among all defect data on all
labelled maps. -/
def IsLeastDefect (M : CombMap) (lab : M.D → C.Letter) : Prop :=
  C.DefectData M lab ∧ ∀ (M' : CombMap) (lab' : M'.D → C.Letter), C.DefectData M' lab' →
    M.numEdges ≤ M'.numEdges

variable {C}

theorem relEdge_isLeft {p q : C.Letter} (h : C.RelEdge p q) :
    p.1.isLeft = true ∧ q.1.isLeft = false := by
  obtain ⟨v, t, _, a, rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-- A defect picture with nonidentity defect gives defect data on its map. -/
theorem DefectPicture.toDefectData {s : V ⊕ T} {P : C.loc s} (Δ : C.DefectPicture s P)
    (hP : P ≠ 1) : C.DefectData Δ.M Δ.lab where
  connected := Δ.connected
  spherical := Δ.spherical
  type_σ := Δ.type_σ
  edge := Δ.edge
  exc := ⟨Δ.b, by rw [Δ.defect_word]; exact DefectPicture.cap_word_ne_one hP, fun d hd => by
    by_contra h
    exact hd (Δ.local_eq d h)⟩

namespace DefectData

variable {M : CombMap} {lab : M.D → C.Letter} (h : C.DefectData M lab)

include h

theorem type_pow (d : M.D) (n : ℕ) : (lab ((M.σ ^ n) d)).1 = (lab d).1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, h.type_σ, ih]

theorem type_eq_of_sameCycle {d e : M.D} (hde : M.σ.SameCycle d e) : (lab e).1 = (lab d).1 := by
  obtain ⟨n, rfl⟩ := hde.exists_nat_pow_eq
  exact h.type_pow d n

theorem kind_σ (x : M.D) : (lab (M.σ x)).1.isLeft = (lab x).1.isLeft := by rw [h.type_σ]

theorem kind_α (x : M.D) : (lab (M.α x)).1.isLeft = !(lab x).1.isLeft := by
  rcases h.edge x with he | he
  · obtain ⟨h1, h2⟩ := relEdge_isLeft he
    rw [h1, h2]; rfl
  · obtain ⟨h1, h2⟩ := relEdge_isLeft he
    rw [h1, h2]; rfl

/-- The two ends of an edge are at different vertices. -/
theorem not_sameCycle_α (x : M.D) : ¬ M.σ.SameCycle x (M.α x) :=
  M.not_sameCycle_α_of_kind (fun z => (lab z).1.isLeft) h.kind_σ h.kind_α x

theorem type_α_ne (x : M.D) : (lab (M.α x)).1 ≠ (lab x).1 := fun e => by
  have := h.kind_α x
  rw [e] at this
  cases hx : (lab x).1.isLeft <;> simp [hx] at this

/-- **Defect data give a defect picture** on the same map, of the type of the exceptional vertex,
with nonidentity defect. -/
theorem exists_defectPicture :
    ∃ (s : V ⊕ T) (P : C.loc s) (Δ : C.DefectPicture s P), P ≠ 1 ∧ Δ.M = M := by
  obtain ⟨b, hb, hexc⟩ := h.exc
  obtain ⟨Q, hQ⟩ := exists_cycleWord_eq_letter M.σ lab (lab b).1 b (h.type_pow b)
  refine ⟨(lab b).1, Q, {
    M := M
    lab := lab
    b := b
    connected := h.connected
    spherical := h.spherical
    type_σ := h.type_σ
    type_b := rfl
    local_eq := fun d hd => by
      by_contra hne
      exact hd (hexc d hne)
    defect_word := hQ
    edge := h.edge }, fun hQ1 => hb ?_, rfl⟩
  rw [hQ, hQ1]
  exact map_one _

end DefectData

/-- Least defects exist as soon as defect data exist. -/
theorem exists_isLeastDefect {M : CombMap} {lab : M.D → C.Letter} (h : C.DefectData M lab) :
    ∃ (M' : CombMap) (lab' : M'.D → C.Letter), C.IsLeastDefect M' lab' := by
  classical
  have hex : ∃ n, ∃ (M' : CombMap) (lab' : M'.D → C.Letter), C.DefectData M' lab' ∧
      M'.numEdges = n := ⟨_, M, lab, h, rfl⟩
  obtain ⟨M', lab', h', hn⟩ := Nat.find_spec hex
  refine ⟨M', lab', h', fun M'' lab'' h'' => ?_⟩
  rw [hn]
  exact Nat.find_min' hex ⟨M'', lab'', h'', rfl⟩

/-- A nonidentity defect picture yields a least defect. -/
theorem exists_isLeastDefect_of_defectPicture {s : V ⊕ T} {P : C.loc s}
    (Δ : C.DefectPicture s P) (hP : P ≠ 1) :
    ∃ (M' : CombMap) (lab' : M'.D → C.Letter), C.IsLeastDefect M' lab' :=
  exists_isLeastDefect (Δ.toDefectData hP)

namespace IsLeastDefect

variable {M : CombMap} {lab : M.D → C.Letter} (h : C.IsLeastDefect M lab)

include h

/-- Minimality: no defect data with fewer edges. -/
theorem not_lt {M' : CombMap} {lab' : M'.D → C.Letter} (h' : C.DefectData M' lab') :
    ¬ M'.numEdges < M.numEdges := fun hlt => absurd (h.2 M' lab' h') (not_le.2 hlt)

end IsLeastDefect

end ConeComplex

end TheoremA
