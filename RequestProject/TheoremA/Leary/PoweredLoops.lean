module

public import RequestProject.TheoremA.Leary.PerfectClosure

/-!
# Powered-loop homomorphisms from short relations

`EdgeData` is finite combinatorial data: vertices `Fin nv`, directed edges `Fin m` with source,
target and reversal, a list of directed triangles, a list of tree edges, a root and a path from the
root to every vertex.  `EdgeData.WF` records the (decidable) compatibility conditions.

* `shortRels D` — the short relators `a ā`, `abc`, `a⁻¹b⁻¹c⁻¹`; `PGrp D` is the presented group.
* `piRels D` — the spanning-tree edge-path relators `a ā`, `a` (tree edges), `abc`; `PiGrp D`.
* In `PGrp D`: `xP_rev` (`ā = a⁻¹`), `tri_commute` (`ab = ba`), `tri_zpow` (`aⁿbⁿcⁿ = 1` for every
  integer `n`).
* `rho D hD n : PiGrp D →* PGrp D` — defined on generators by `z_a(n) = g_u(n) aⁿ g_v(n)⁻¹` using
  only the relations of `PGrp D`; nothing is assumed about non-tree edges.
* `rho_walk` — the telescoping identity `ρₙ([a₁⋯a_k]) = g_u(n) a₁ⁿ⋯a_kⁿ g_v(n)⁻¹` for any walk;
  `rho_loop` — the based form `ρₙ([γ]) = a₁ⁿ⋯a_kⁿ` (PL).
-/

@[expose] public section

namespace TheoremA.Leary

/-- Finite edge/triangle data of a 2-complex with a spanning tree and root paths. -/
structure EdgeData where
  nv : ℕ
  m : ℕ
  src : Fin m → Fin nv
  tgt : Fin m → Fin nv
  rev : Fin m → Fin m
  tri : List (Fin m × Fin m × Fin m)
  tree : List (Fin m)
  root : Fin nv
  path : Fin nv → List (Fin m)

namespace EdgeData

variable (D : EdgeData)

/-- Well-formedness of edge data. -/
structure WF : Prop where
  rev_src : ∀ a, D.src (D.rev a) = D.tgt a
  rev_tgt : ∀ a, D.tgt (D.rev a) = D.src a
  tri_ab : ∀ t ∈ D.tri, D.tgt t.1 = D.src t.2.1
  tri_bc : ∀ t ∈ D.tri, D.tgt t.2.1 = D.src t.2.2
  tri_ca : ∀ t ∈ D.tri, D.tgt t.2.2 = D.src t.1
  tree_path : ∀ a ∈ D.tree, D.path (D.tgt a) = D.path (D.src a) ++ [a] ∨
    D.path (D.src a) = D.path (D.tgt a) ++ [D.rev a]
  path_root : D.path D.root = []

/-- The free-group generator of an edge. -/
abbrev fe (a : Fin D.m) : FreeGroup (Fin D.m) := FreeGroup.of a

/-- Short relators of `P`. -/
def shortRels : Set (FreeGroup (Fin D.m)) :=
  {r | ∃ a, r = D.fe a * D.fe (D.rev a)} ∪
  {r | ∃ t ∈ D.tri, r = D.fe t.1 * D.fe t.2.1 * D.fe t.2.2} ∪
  {r | ∃ t ∈ D.tri, r = (D.fe t.1)⁻¹ * (D.fe t.2.1)⁻¹ * (D.fe t.2.2)⁻¹}

/-- Relators of the spanning-tree edge-path presentation `Π_L`. -/
def piRels : Set (FreeGroup (Fin D.m)) :=
  {r | ∃ a, r = D.fe a * D.fe (D.rev a)} ∪
  {r | ∃ a ∈ D.tree, r = D.fe a} ∪
  {r | ∃ t ∈ D.tri, r = D.fe t.1 * D.fe t.2.1 * D.fe t.2.2}

/-- The group `P` of short relations. -/
abbrev PGrp := PresentedGroup D.shortRels

/-- The edge-path group `Π_L`. -/
abbrev PiGrp := PresentedGroup D.piRels

theorem shortRels_finite : D.shortRels.Finite := by
  refine ((Set.Finite.union ?_ ?_).union ?_)
  · exact (Set.finite_range fun a => D.fe a * D.fe (D.rev a)).subset (by
      rintro _ ⟨a, rfl⟩; exact ⟨a, rfl⟩)
  · exact ((D.tri.finite_toSet).image fun t => D.fe t.1 * D.fe t.2.1 * D.fe t.2.2).subset (by
      rintro _ ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩)
  · exact ((D.tri.finite_toSet).image
      fun t => (D.fe t.1)⁻¹ * (D.fe t.2.1)⁻¹ * (D.fe t.2.2)⁻¹).subset (by
      rintro _ ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩)

/-- `P` is finitely presented, hence `FP₂`. -/
theorem isFP_two_PGrp : IsFP 2 D.PGrp :=
  isFP_two_presentedGroup_of_finite _ D.shortRels_finite

/-- The generator of an edge in `P`. -/
abbrev xP (a : Fin D.m) : D.PGrp := PresentedGroup.of a

theorem PGrp_rel {r : FreeGroup (Fin D.m)} (hr : r ∈ D.shortRels) :
    FreeGroup.lift D.xP r = 1 := by
  have hl : FreeGroup.lift D.xP = PresentedGroup.mk D.shortRels := by
    ext i; rfl
  have : FreeGroup.lift D.xP r = (QuotientGroup.mk r : D.PGrp) := by
    rw [hl]; rfl
  rw [this, QuotientGroup.eq_one_iff]
  exact Subgroup.subset_normalClosure hr

theorem xP_mul_rev (a : Fin D.m) : D.xP a * D.xP (D.rev a) = 1 := by
  have := D.PGrp_rel (r := D.fe a * D.fe (D.rev a)) (Or.inl (Or.inl ⟨a, rfl⟩))
  simpa using this

theorem xP_rev (a : Fin D.m) : D.xP (D.rev a) = (D.xP a)⁻¹ :=
  eq_inv_of_mul_eq_one_right (D.xP_mul_rev a)

theorem tri_mul {t} (ht : t ∈ D.tri) : D.xP t.1 * D.xP t.2.1 * D.xP t.2.2 = 1 := by
  have := D.PGrp_rel (r := D.fe t.1 * D.fe t.2.1 * D.fe t.2.2) (Or.inl (Or.inr ⟨t, ht, rfl⟩))
  simpa using this

theorem tri_mul_inv {t} (ht : t ∈ D.tri) :
    (D.xP t.1)⁻¹ * (D.xP t.2.1)⁻¹ * (D.xP t.2.2)⁻¹ = 1 := by
  have := D.PGrp_rel (r := (D.fe t.1)⁻¹ * (D.fe t.2.1)⁻¹ * (D.fe t.2.2)⁻¹) (Or.inr ⟨t, ht, rfl⟩)
  simpa using this

/-- Triangle edge generators commute in `P`. -/
theorem tri_commute {t} (ht : t ∈ D.tri) : Commute (D.xP t.1) (D.xP t.2.1) := by
  have h1 := D.tri_mul ht
  have h2 := D.tri_mul_inv ht
  set a := D.xP t.1; set b := D.xP t.2.1; set c := D.xP t.2.2
  have e1 : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have e2 : c⁻¹ = (a⁻¹ * b⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right h2
  have e3 : c = a⁻¹ * b⁻¹ := inv_inj.mp e2
  have e4 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by rw [← e3, e1, mul_inv_rev]
  exact Commute.inv_inv_iff.mp e4

/-- `aⁿbⁿcⁿ = 1` in `P` for every integer `n`. -/
theorem tri_zpow {t} (ht : t ∈ D.tri) (n : ℤ) :
    D.xP t.1 ^ n * D.xP t.2.1 ^ n * D.xP t.2.2 ^ n = 1 := by
  have hc : D.xP t.2.2 = (D.xP t.1 * D.xP t.2.1)⁻¹ := eq_inv_of_mul_eq_one_right (D.tri_mul ht)
  rw [hc, ← (D.tri_commute ht).mul_zpow, inv_zpow, mul_inv_cancel]

/-- `āⁿ = a⁻ⁿ`. -/
theorem xP_rev_zpow (a : Fin D.m) (n : ℤ) : D.xP (D.rev a) ^ n = (D.xP a ^ n)⁻¹ := by
  rw [xP_rev, inv_zpow]

/-- The powered value of a list of edges. -/
def powVal (n : ℤ) (w : List (Fin D.m)) : D.PGrp := (w.map fun e => D.xP e ^ n).prod

@[simp] theorem powVal_nil (n : ℤ) : D.powVal n [] = 1 := rfl

@[simp] theorem powVal_cons (n : ℤ) (a : Fin D.m) (w : List (Fin D.m)) :
    D.powVal n (a :: w) = D.xP a ^ n * D.powVal n w := by simp [powVal]

@[simp] theorem powVal_append (n : ℤ) (v w : List (Fin D.m)) :
    D.powVal n (v ++ w) = D.powVal n v * D.powVal n w := by simp [powVal]

/-- The reversed path. -/
def revPath (w : List (Fin D.m)) : List (Fin D.m) := (w.map D.rev).reverse

theorem powVal_revPath (n : ℤ) (w : List (Fin D.m)) :
    D.powVal n (D.revPath w) = (D.powVal n w)⁻¹ := by
  induction w with
  | nil => simp [revPath]
  | cons a w ih =>
    simp only [revPath, List.map_cons, List.reverse_cons, powVal_append, powVal_cons,
      powVal_nil, mul_one] at ih ⊢
    rw [ih, xP_rev_zpow, mul_inv_rev]

/-- `g_v(n)`: the powered tree path to `v`. -/
def gP (n : ℤ) (v : Fin D.nv) : D.PGrp := D.powVal n (D.path v)

/-- `z_a(n) = g_u(n) aⁿ g_v(n)⁻¹` for `a : u → v`. -/
def zP (n : ℤ) (a : Fin D.m) : D.PGrp := D.gP n (D.src a) * D.xP a ^ n * (D.gP n (D.tgt a))⁻¹

variable {D}

theorem zP_rel (hD : D.WF) (n : ℤ) {r : FreeGroup (Fin D.m)} (hr : r ∈ D.piRels) :
    FreeGroup.lift (D.zP n) r = 1 := by
  rcases hr with (⟨a, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨t, ht, rfl⟩
  · simp only [map_mul, FreeGroup.lift_apply_of, zP, hD.rev_src, hD.rev_tgt, D.xP_rev_zpow]
    group
  · simp only [FreeGroup.lift_apply_of, zP, gP]
    rcases hD.tree_path a ha with h | h
    · rw [h, powVal_append, powVal_cons, powVal_nil, mul_one]; group
    · rw [h, powVal_append, powVal_cons, powVal_nil, mul_one, xP_rev_zpow]; group
  · simp only [map_mul, FreeGroup.lift_apply_of, zP]
    rw [hD.tri_ab t ht, hD.tri_bc t ht, hD.tri_ca t ht]
    have h := D.tri_zpow ht n
    calc D.gP n (D.src t.1) * D.xP t.1 ^ n * (D.gP n (D.src t.2.1))⁻¹ *
          (D.gP n (D.src t.2.1) * D.xP t.2.1 ^ n * (D.gP n (D.src t.2.2))⁻¹) *
          (D.gP n (D.src t.2.2) * D.xP t.2.2 ^ n * (D.gP n (D.src t.1))⁻¹)
        = D.gP n (D.src t.1) * (D.xP t.1 ^ n * D.xP t.2.1 ^ n * D.xP t.2.2 ^ n) *
          (D.gP n (D.src t.1))⁻¹ := by group
      _ = 1 := by rw [h]; group

/-- **The powered-loop homomorphism** `ρₙ : Π_L → P`. -/
def rho (hD : D.WF) (n : ℤ) : D.PiGrp →* D.PGrp :=
  PresentedGroup.toGroup (fun _ hr => zP_rel hD n hr)

theorem rho_of (hD : D.WF) (n : ℤ) (a : Fin D.m) :
    rho hD n (PresentedGroup.of a) = D.zP n a :=
  PresentedGroup.toGroup.of _

/-- The class of an edge word in `Π_L`. -/
def piVal (w : List (Fin D.m)) : D.PiGrp := (w.map fun e => (PresentedGroup.of e : D.PiGrp)).prod

/-- A walk from `u` to `v`. -/
def IsWalk (D : EdgeData) : Fin D.nv → List (Fin D.m) → Fin D.nv → Prop
  | u, [], v => u = v
  | u, a :: w, v => D.src a = u ∧ IsWalk D (D.tgt a) w v

/-- **Telescoping** along a walk. -/
theorem rho_walk (hD : D.WF) (n : ℤ) : ∀ (u : Fin D.nv) (w : List (Fin D.m)) (v : Fin D.nv),
    IsWalk D u w v → rho hD n (piVal w) = D.gP n u * D.powVal n w * (D.gP n v)⁻¹
  | u, [], v, h => by
    change u = v at h; subst h; simp [piVal]
  | u, a :: w, v, h => by
    obtain ⟨h1, h2⟩ := h
    have ih := rho_walk hD n (D.tgt a) w v h2
    have : piVal (a :: w) = (PresentedGroup.of a : D.PiGrp) * piVal w := by simp [piVal]
    rw [this, map_mul, ih, rho_of, zP, h1, powVal_cons]
    group

/-- **(PL)**: for a loop based at the root, `ρₙ([a₁⋯a_k]) = a₁ⁿ⋯a_kⁿ`. -/
theorem rho_loop (hD : D.WF) (n : ℤ) (w : List (Fin D.m)) (hw : IsWalk D D.root w D.root) :
    rho hD n (piVal w) = D.powVal n w := by
  rw [rho_walk hD n _ w _ hw, gP, hD.path_root]; simp

end EdgeData

end TheoremA.Leary
