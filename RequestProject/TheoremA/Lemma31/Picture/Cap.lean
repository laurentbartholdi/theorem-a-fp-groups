module

public import RequestProject.TheoremA.Lemma31.Picture.RawSplit

/-!
# Capping one defective local vertex by a marked leaf

## Map level

`CombMap.leafEdge` is the map with two darts `0, 1`, one edge `{0, 1}` and two one-dart vertices.
`CombMap.addMarkedLeaf M b` glues it to `M` at the vertex of `b` (`CombMap.glue M leafEdge b 0`).
Writing `z = inr 0`, `m = inr 1` and `p = σ⁻¹ b`:

* `α' z = m`, `α' m = z`, `α'` agrees with `α` on old darts;
* `σ' p = z`, `σ' z = b`, `σ' m = m`, `σ'` agrees with `σ` on the other old darts
  (`addMarkedLeaf_σ_pred`, `addMarkedLeaf_σ_z`, `addMarkedLeaf_σ_m`, `addMarkedLeaf_σ_of_ne`);
* one more vertex, one more edge, the same number of faces, the same `χ`
  (`addMarkedLeaf_numVertices`, `addMarkedLeaf_numEdges`, `addMarkedLeaf_numFaces`,
  `addMarkedLeaf_euler`), and connectedness is preserved (`addMarkedLeaf_connected`);
* **face subdivision**: with `r = α p`, the old face arrow `r ↦ b` becomes `r ↦ z ↦ m ↦ b`, all
  other face arrows are unchanged (`addMarkedLeaf_φ_r`, `addMarkedLeaf_φ_z`, `addMarkedLeaf_φ_m`,
  `addMarkedLeaf_φ_of_ne`).

## Labelled level

`ConeComplex.DefectPicture s P` records the input of the construction: a connected spherical
labelled map with a chosen dart `b`, in which every vertex carries letters of one local group,
every edge is a relator edge, every vertex except the `b`-vertex has product `1`, and the
`b`-vertex has type `s` and product `P : C.loc s` (read from `b`).  `DefectPicture.cap` labels
`z` by `P⁻¹` and `m` by `P` and makes `m` the base dart; this is a `RawPicture` for the single
letter `P` with exactly one more edge (`DefectPicture.cap_numEdges`).  No `NPC`, girth or
injectivity into the colimit is used.
-/

@[expose] public section

namespace TheoremA

namespace Picture

open Equiv Function

namespace CombMap

/-- A single edge with two one-dart vertices. -/
def leafEdge : CombMap where
  D := Fin 2
  σ := 1
  α := swap 0 1
  α_α := by decide
  α_ne := by decide

theorem leafEdge_numVertices : leafEdge.numVertices = 2 :=
  numOrbits_eq_of_invariant (N := 1) leafEdge.σ ![0, 1] (by decide) (by decide) (by decide)

theorem leafEdge_numEdges : leafEdge.numEdges = 1 :=
  numOrbits_eq_of_invariant (N := 2) leafEdge.α ![0, 0] (by decide) (by decide) (by decide)

theorem leafEdge_numFaces : leafEdge.numFaces = 1 :=
  numOrbits_eq_of_invariant (N := 2) leafEdge.φ ![0, 0] (by decide) (by decide) (by decide)

theorem leafEdge_connected : leafEdge.Connected :=
  leafEdge.connected_of_walks (0 : Fin 2) [[], [false]] (by decide)

variable (M : CombMap) (b : M.D)

/-- **Adding a marked leaf** at the vertex of `b`: a new edge `{z, m}` with `z = inr 0` inserted
immediately before `b` in the rotation, and `m = inr 1` a new one-dart vertex. -/
def addMarkedLeaf : CombMap := glue M leafEdge b (0 : Fin 2)

/-- The new dart at the old vertex. -/
def leafZ : (M.addMarkedLeaf b).D := Sum.inr (0 : Fin 2)

/-- The new leaf dart. -/
def leafM : (M.addMarkedLeaf b).D := Sum.inr (1 : Fin 2)

theorem addMarkedLeaf_α_inl (x : M.D) :
    (M.addMarkedLeaf b).α (Sum.inl x) = Sum.inl (M.α x) := rfl

theorem addMarkedLeaf_α_z : (M.addMarkedLeaf b).α (M.leafZ b) = M.leafM b := rfl

theorem addMarkedLeaf_α_m : (M.addMarkedLeaf b).α (M.leafM b) = M.leafZ b := rfl

theorem addMarkedLeaf_σ_apply (x : (M.addMarkedLeaf b).D) :
    (M.addMarkedLeaf b).σ x =
      swap (Sum.inl b) (Sum.inr (0 : Fin 2)) (Perm.sumCongr M.σ (1 : Perm (Fin 2)) x) := rfl

theorem addMarkedLeaf_σ_pred :
    (M.addMarkedLeaf b).σ (Sum.inl (M.σ⁻¹ b)) = M.leafZ b := by
  rw [addMarkedLeaf_σ_apply]; simp [leafZ]

theorem addMarkedLeaf_σ_z : (M.addMarkedLeaf b).σ (M.leafZ b) = Sum.inl b := by
  rw [addMarkedLeaf_σ_apply]; simp [leafZ]

theorem addMarkedLeaf_σ_m : (M.addMarkedLeaf b).σ (M.leafM b) = M.leafM b := by
  rw [addMarkedLeaf_σ_apply]
  simp only [leafM, Perm.sumCongr_apply, Sum.map_inr, Perm.coe_one, id]
  exact swap_apply_of_ne_of_ne Sum.inr_ne_inl
    (fun h => absurd (Sum.inr_injective h) (show (1 : Fin 2) ≠ 0 by decide))

theorem addMarkedLeaf_σ_of_ne {x : M.D} (hx : M.σ x ≠ b) :
    (M.addMarkedLeaf b).σ (Sum.inl x) = Sum.inl (M.σ x) := by
  rw [addMarkedLeaf_σ_apply]
  simp only [Perm.sumCongr_apply, Sum.map_inl]
  exact swap_apply_of_ne_of_ne (fun h => hx (Sum.inl_injective h)) (by simp)

theorem addMarkedLeaf_φ_apply (x : (M.addMarkedLeaf b).D) :
    (M.addMarkedLeaf b).φ x = (M.addMarkedLeaf b).σ ((M.addMarkedLeaf b).α x) := rfl

/-- Face subdivision: the old arrow `r ↦ b` (with `r = α (σ⁻¹ b)`) now goes to `z`. -/
theorem addMarkedLeaf_φ_r :
    (M.addMarkedLeaf b).φ (Sum.inl (M.α (M.σ⁻¹ b))) = M.leafZ b := by
  rw [addMarkedLeaf_φ_apply, addMarkedLeaf_α_inl, M.α_α, addMarkedLeaf_σ_pred]

theorem addMarkedLeaf_φ_z : (M.addMarkedLeaf b).φ (M.leafZ b) = M.leafM b := by
  rw [addMarkedLeaf_φ_apply, addMarkedLeaf_α_z, addMarkedLeaf_σ_m]

theorem addMarkedLeaf_φ_m : (M.addMarkedLeaf b).φ (M.leafM b) = Sum.inl b := by
  rw [addMarkedLeaf_φ_apply, addMarkedLeaf_α_m, addMarkedLeaf_σ_z]

/-- All other old face arrows are unchanged. -/
theorem addMarkedLeaf_φ_of_ne {x : M.D} (hx : M.φ x ≠ b) :
    (M.addMarkedLeaf b).φ (Sum.inl x) = Sum.inl (M.φ x) := by
  rw [addMarkedLeaf_φ_apply, addMarkedLeaf_α_inl, addMarkedLeaf_σ_of_ne _ _ hx]; rfl

/-- The old face arrow into `b` is the one from `r = α (σ⁻¹ b)`. -/
theorem φ_eq_iff_eq (x : M.D) : M.φ x = b ↔ x = M.α (M.σ⁻¹ b) := by
  constructor
  · rintro rfl
    change x = M.α (M.σ⁻¹ (M.σ (M.α x)))
    simp [M.α_α]
  · rintro rfl
    change M.σ (M.α (M.α (M.σ⁻¹ b))) = b
    simp [M.α_α]

theorem addMarkedLeaf_numVertices :
    (M.addMarkedLeaf b).numVertices = M.numVertices + 1 := by
  have := glue_numVertices M leafEdge b (0 : Fin 2)
  rw [leafEdge_numVertices] at this
  change (M.addMarkedLeaf b).numVertices + 1 = _ at this
  omega

theorem addMarkedLeaf_numEdges : (M.addMarkedLeaf b).numEdges = M.numEdges + 1 := by
  have := glue_numEdges M leafEdge b (0 : Fin 2)
  rwa [leafEdge_numEdges] at this

theorem addMarkedLeaf_numFaces : (M.addMarkedLeaf b).numFaces = M.numFaces := by
  have := glue_numFaces M leafEdge b (0 : Fin 2)
  rw [leafEdge_numFaces] at this
  change (M.addMarkedLeaf b).numFaces + 1 = _ at this
  omega

/-- Adding a marked leaf keeps the Euler characteristic. -/
theorem addMarkedLeaf_euler : (M.addMarkedLeaf b).euler = M.euler := by
  have hV := addMarkedLeaf_numVertices M b
  have hE := addMarkedLeaf_numEdges M b
  have hF := addMarkedLeaf_numFaces M b
  unfold euler
  omega

theorem addMarkedLeaf_connected (hM : M.Connected) : (M.addMarkedLeaf b).Connected :=
  glue_connected _ _ _ _ hM leafEdge_connected

/-- The new leaf is a vertex with a single dart. -/
theorem addMarkedLeaf_sameCycle_m_iff (x : (M.addMarkedLeaf b).D) :
    (M.addMarkedLeaf b).σ.SameCycle (M.leafM b) x ↔ x = M.leafM b := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Perm.mul_apply, ih ⟨n, rfl⟩, addMarkedLeaf_σ_m]
  · rintro rfl; exact Perm.SameCycle.refl _ _

end CombMap

end Picture

universe u w

namespace ConeComplex

open Picture Equiv Function

variable {V T : Type w} (C : ConeComplex.{u, w} V T)

/-- The input of the capping construction: a connected spherical labelled map with a chosen dart
`b`, where every vertex carries letters of a single local group, every edge is a relator edge,
every vertex other than the `b`-vertex has product `1`, and the `b`-vertex has type `s` and
product `P` read from `b`.  (`P` need not be `1`.) -/
structure DefectPicture (s : V ⊕ T) (P : C.loc s) where
  /-- The underlying map. -/
  M : CombMap
  /-- The letters. -/
  lab : M.D → C.Letter
  /-- The chosen dart of the defective vertex. -/
  b : M.D
  connected : M.Connected
  spherical : M.euler = 2
  /-- Every vertex carries letters of a single local group. -/
  type_σ : ∀ d, (lab (M.σ d)).1 = (lab d).1
  /-- The defective vertex has type `s`. -/
  type_b : (lab b).1 = s
  /-- Every other vertex has product `1`. -/
  local_eq : ∀ d, ¬ M.σ.SameCycle b d → cycleWord M.σ (C.letterWord ∘ lab) d = 1
  /-- The product at the defective vertex, read from `b`, is `P`. -/
  defect_word : cycleWord M.σ (C.letterWord ∘ lab) b = C.letterWord ⟨s, P⟩
  /-- Every edge is an ordinary relator edge. -/
  edge : ∀ d, C.RelEdge (lab d) (lab (M.α d)) ∨ C.RelEdge (lab (M.α d)) (lab d)

namespace DefectPicture

variable {C} {s : V ⊕ T} {P : C.loc s} (Δ : C.DefectPicture s P)

/-- The labels of the capped map: `z` gets `P⁻¹`, `m` gets `P`. -/
def capLab : (Δ.M.addMarkedLeaf Δ.b).D → C.Letter :=
  Sum.elim Δ.lab ![⟨s, P⁻¹⟩, ⟨s, P⟩]

theorem type_pow (d : Δ.M.D) (n : ℕ) : (Δ.lab ((Δ.M.σ ^ n) d)).1 = (Δ.lab d).1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, Δ.type_σ, ih]

theorem type_eq_of_sameCycle {d e : Δ.M.D} (h : Δ.M.σ.SameCycle d e) :
    (Δ.lab e).1 = (Δ.lab d).1 := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  exact Δ.type_pow d n

theorem cap_local_b : cycleWord (Δ.M.addMarkedLeaf Δ.b).σ (C.letterWord ∘ Δ.capLab)
    (Sum.inl Δ.b) = 1 := by
  change cycleWord (swap (Sum.inl Δ.b) (Sum.inr (0 : Fin 2)) *
    Perm.sumCongr Δ.M.σ (1 : Perm (Fin 2))) (C.letterWord ∘ Δ.capLab) (Sum.inl Δ.b) = 1
  rw [cycleWord_swap_mul _ not_sameCycle_sumCongr_inl_inr, cycleWord_sumCongr_inl,
    cycleWord_sumCongr_inr, cycleWord_of_fixed (π := (1 : Perm (Fin 2))) _ (x := 0) rfl]
  change cycleWord Δ.M.σ (C.letterWord ∘ Δ.lab) Δ.b * C.letterWord ⟨s, P⁻¹⟩ = 1
  rw [Δ.defect_word]
  change Monoid.CoprodI.of P * Monoid.CoprodI.of P⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

/-- **Capping a defective vertex by a marked leaf.**  The result is a raw picture for the single
local letter `P`. -/
def cap : C.RawPicture (C.letterWord ⟨s, P⟩) where
  M := Δ.M.addMarkedLeaf Δ.b
  lab := Δ.capLab
  base := Δ.M.leafM Δ.b
  connected := CombMap.addMarkedLeaf_connected _ _ Δ.connected
  spherical := by rw [CombMap.addMarkedLeaf_euler, Δ.spherical]
  type_σ := by
    rintro (d | d) -
    · by_cases hd : Δ.M.σ d = Δ.b
      · have : d = Δ.M.σ⁻¹ Δ.b := by rw [← hd]; simp
        subst this
        rw [CombMap.addMarkedLeaf_σ_pred]
        change s = (Δ.lab (Δ.M.σ⁻¹ Δ.b)).1
        have := Δ.type_σ (Δ.M.σ⁻¹ Δ.b)
        rw [hd, Δ.type_b] at this
        exact this
      · rw [CombMap.addMarkedLeaf_σ_of_ne _ _ hd]
        exact Δ.type_σ d
    · fin_cases d
      · change (Δ.capLab ((Δ.M.addMarkedLeaf Δ.b).σ (Δ.M.leafZ Δ.b))).1 = s
        rw [CombMap.addMarkedLeaf_σ_z]
        exact Δ.type_b
      · change (Δ.capLab ((Δ.M.addMarkedLeaf Δ.b).σ (Δ.M.leafM Δ.b))).1 = _
        rw [CombMap.addMarkedLeaf_σ_m]
        rfl
  local_eq := by
    intro d hd
    rw [CombMap.addMarkedLeaf_sameCycle_m_iff] at hd
    by_cases hdb : (Δ.M.addMarkedLeaf Δ.b).σ.SameCycle (Sum.inl Δ.b) d
    · exact cycleWord_eq_one_of_sameCycle _ hdb Δ.cap_local_b
    rcases d with d | d
    · have hdb' : ¬ Δ.M.σ.SameCycle Δ.b d := by
        intro h
        apply hdb
        exact (CombMap.glue_sameCycle_iff _ _ _ _).2 (Or.inl (sameCycle_sumCongr_inl.2 h))
      have hpow : ∀ n : ℕ, ((Δ.M.addMarkedLeaf Δ.b).σ ^ n) (Sum.inl d) =
          (Perm.sumCongr Δ.M.σ (1 : Perm (Fin 2)) ^ n) (Sum.inl d) :=
        swap_mul_pow_apply_of_not_sameCycle (by rwa [sameCycle_sumCongr_inl])
          not_sameCycle_sumCongr_inr_inl
      rw [cycleWord_congr _ hpow, cycleWord_sumCongr_inl]
      exact Δ.local_eq d hdb'
    · fin_cases d
      · exact absurd ((CombMap.glue_sameCycle_iff _ _ _ _).2
          (Or.inr ⟨Or.inl (Perm.SameCycle.refl _ _),
            Or.inr (Perm.SameCycle.refl _ _)⟩)) hdb
      · exact absurd rfl hd
  edge_interior := by
    rintro (d | d) hd hd'
    · exact Δ.edge d
    · fin_cases d
      · exact absurd ((CombMap.addMarkedLeaf_sameCycle_m_iff _ _ _).2 rfl) hd'
      · exact absurd ((CombMap.addMarkedLeaf_sameCycle_m_iff _ _ _).2 rfl) hd
  edge_boundary := by
    intro d hd
    rw [CombMap.addMarkedLeaf_sameCycle_m_iff] at hd
    subst hd
    rw [CombMap.addMarkedLeaf_α_m, CombMap.addMarkedLeaf_sameCycle_m_iff]
    exact ⟨fun h => absurd (Sum.inr_injective h) (show (0 : Fin 2) ≠ 1 by decide), rfl⟩
  boundary_word := by
    rw [cycleWord_of_fixed _ (CombMap.addMarkedLeaf_σ_m _ _)]
    rfl

/-- The cap adds exactly one edge. -/
theorem cap_numEdges : Δ.cap.M.numEdges = Δ.M.numEdges + 1 :=
  CombMap.addMarkedLeaf_numEdges _ _

/-- The cap adds exactly one vertex and keeps the number of faces. -/
theorem cap_numVertices_numFaces :
    Δ.cap.M.numVertices = Δ.M.numVertices + 1 ∧ Δ.cap.M.numFaces = Δ.M.numFaces :=
  ⟨CombMap.addMarkedLeaf_numVertices _ _, CombMap.addMarkedLeaf_numFaces _ _⟩

/-- The marked word of the cap is exactly the free-product letter of `P`; it is nonidentity iff
`P ≠ 1` (injectivity of the factor into the free product). -/
theorem cap_word_ne_one (hP : P ≠ 1) : C.letterWord ⟨s, P⟩ ≠ 1 := by
  intro h
  exact hP (Monoid.CoprodI.of_injective s (h.trans (map_one _).symm))

end DefectPicture

end ConeComplex

end TheoremA
