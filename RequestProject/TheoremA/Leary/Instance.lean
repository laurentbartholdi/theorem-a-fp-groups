module

public import RequestProject.TheoremA.Leary.PerfectCert
public import RequestProject.TheoremA.Leary.FlagData

/-!
# The fixed flag complex `flagL`: perfect, nontrivial edge-path group; `FP₂` of `J(S)`

`flagL` is the collar-and-cone triangulation of the presentation complex of
`⟨s, t | s² = tst, s³ = t⁵⟩` (the binary icosahedral group): 61 vertices, 216 edges (432 directed
edges; the reverse of `a` is `a xor 1`), 156 triangles (one orientation each), a spanning tree
and root paths.  The loops `s`, `t` are subdivided into four edges.

* `flagL_wf` — well-formedness, checked by kernel evaluation.
* `flagCertData`, `flagCert_valid` — the symbolic perfection certificate (kernel-checked); the two
  relation triangles give `S - 2T = 0` and `3S - 5T = 0`, and `(1,0) = -5(1,-2) + 2(3,-5)`,
  `(0,1) = -3(1,-2) + (3,-5)`.
* `isPerfect_PiGrp_flagL` — **the edge-path group is perfect**.
* `piToA5` and `flagLoop_ne_one` — the subdivided loop `s` is a **nonidentity** element of the
  edge-path group (its image in `S₅` is the 3-cycle `(0 2 4)`).
* `isFP_two_JGrp_flagL` — **for every `S ⊆ ℤ`, `J(S)` over `flagL` is `FP₂`.**

The flag property of `flagL` (every 3-clique spans a triangle, no 4-cliques) is kernel-checked in
`Leary/Flagness.lean` (`flagL_isFlagComplex`, `flagL_check3`, `flagL_check4`); the separation proof
in `Leary/Detection.lean` uses the 3-cycle form of it through `flagL_cycle_rel`.
-/

@[expose] public section

namespace TheoremA.Leary

/-- The fixed flag complex. -/
def flagL : EdgeData where
  nv := 61
  m := 432
  src a := Fin.ofNat 61 (flagSrcT.get a.val)
  tgt a := Fin.ofNat 61 (flagTgtT.get a.val)
  rev a := Fin.ofNat 432 (if a.val % 2 = 0 then a.val + 1 else a.val - 1)
  tri := flagTri.map fun t => (Fin.ofNat 432 t.1, Fin.ofNat 432 t.2.1, Fin.ofNat 432 t.2.2)
  tree := flagTree.map (Fin.ofNat 432)
  root := 0
  path v := (flagPathT.get v.val).map (Fin.ofNat 432)

theorem flagL_m : flagL.m = 432 := rfl

instance : NeZero flagL.m := ⟨by decide⟩

theorem flagL_rev_src : ∀ a, flagL.src (flagL.rev a) = flagL.tgt a := by decide +kernel
theorem flagL_rev_tgt : ∀ a, flagL.tgt (flagL.rev a) = flagL.src a := by decide +kernel
/-- Transfer a Boolean check over the raw triangle list to all triangles of `flagL`. -/
theorem flagL_forall_tri {P : Fin flagL.m × Fin flagL.m × Fin flagL.m → Prop} [DecidablePred P]
    (h : (flagTri.all fun t =>
      decide (P (Fin.ofNat 432 t.1, Fin.ofNat 432 t.2.1, Fin.ofNat 432 t.2.2))) = true) :
    ∀ t ∈ flagL.tri, P t := by
  intro t ht
  simp only [flagL, List.mem_map] at ht
  obtain ⟨r, hr, rfl⟩ := ht
  have := List.all_eq_true.1 h r hr
  simpa using this

theorem flagL_tri_ab : ∀ t ∈ flagL.tri, flagL.tgt t.1 = flagL.src t.2.1 :=
  flagL_forall_tri (by decide +kernel)
theorem flagL_tri_bc : ∀ t ∈ flagL.tri, flagL.tgt t.2.1 = flagL.src t.2.2 :=
  flagL_forall_tri (by decide +kernel)
theorem flagL_tri_ca : ∀ t ∈ flagL.tri, flagL.tgt t.2.2 = flagL.src t.1 :=
  flagL_forall_tri (by decide +kernel)
theorem flagL_tree_path : ∀ a ∈ flagL.tree,
    flagL.path (flagL.tgt a) = flagL.path (flagL.src a) ++ [a] ∨
      flagL.path (flagL.src a) = flagL.path (flagL.tgt a) ++ [flagL.rev a] := by decide +kernel

theorem flagL_wf : flagL.WF where
  rev_src := flagL_rev_src
  rev_tgt := flagL_rev_tgt
  tri_ab := flagL_tri_ab
  tri_bc := flagL_tri_bc
  tri_ca := flagL_tri_ca
  tree_path := flagL_tree_path
  path_root := rfl

/-- The perfection certificate for `flagL`. -/
def flagCertData : flagL.PerfCert where
  val a := flagValT.get a.val
  rank a := flagRankT.get a.val
  just a := flagJustT.get a.val
  base0 := Fin.ofNat 432 (flagBase.getD 0 0)
  base1 := Fin.ofNat 432 (flagBase.getD 1 0)
  cert0 := flagCert.getD 0 []
  cert1 := flagCert.getD 1 []

theorem flagCert_valid : flagCertData.Valid := by decide +kernel

/-- **The edge-path group of `flagL` is perfect.** -/
theorem isPerfect_PiGrp_flagL : IsPerfectGroup flagL.PiGrp :=
  EdgeData.PerfCert.isPerfect flagCert_valid

/-! ### Nontriviality of the subdivided loop `s` -/

/-- The image of an edge in `S₅`, as a product of transpositions. -/
def flagPerm (a : Fin flagL.m) : Equiv.Perm (Fin 5) :=
  ((flagImgT.get a.val).map fun p => Equiv.swap (Fin.ofNat 5 p.1) (Fin.ofNat 5 p.2)).prod

theorem flagPerm_rev : ∀ a, flagPerm a * flagPerm (flagL.rev a) = 1 := by decide +kernel
theorem flagPerm_tree : ∀ a ∈ flagL.tree, flagPerm a = 1 := by decide +kernel
theorem flagPerm_tri : ∀ t ∈ flagL.tri, flagPerm t.1 * flagPerm t.2.1 * flagPerm t.2.2 = 1 :=
  flagL_forall_tri (by decide +kernel)

/-- The homomorphism from the edge-path group to `S₅`. -/
def piToA5 : flagL.PiGrp →* Equiv.Perm (Fin 5) :=
  PresentedGroup.toGroup (f := flagPerm) (fun r hr => by
    rcases hr with (⟨a, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨t, ht, rfl⟩
    · simpa using flagPerm_rev a
    · simpa using flagPerm_tree a ha
    · simpa using flagPerm_tri t ht)

/-- The subdivided loop `s`, based at the root. -/
def flagLoopL : List (Fin flagL.m) := flagLoop.map (Fin.ofNat 432)

theorem flagLoop_isWalk : EdgeData.IsWalk flagL flagL.root flagLoopL flagL.root := by
  simp only [flagLoopL, flagLoop, List.map_cons, List.map_nil, EdgeData.IsWalk]
  decide +kernel

theorem piToA5_piVal (w : List (Fin flagL.m)) :
    piToA5 (EdgeData.piVal (D := flagL) w) = (w.map flagPerm).prod := by
  induction w with
  | nil => simp [EdgeData.piVal]
  | cons a w ih =>
    simp only [EdgeData.piVal, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]; simp [piToA5, PresentedGroup.toGroup.of]

/-- **Nontriviality**: the loop `s` is a nonidentity element of the edge-path group. -/
theorem flagLoop_ne_one : EdgeData.piVal (D := flagL) flagLoopL ≠ 1 := by
  intro h
  have h1 := congrArg piToA5 h
  rw [piToA5_piVal, map_one] at h1
  revert h1
  decide +kernel

/-! ### Unconditional `FP₂` for `J(S)` -/

/-- **For every `S ⊆ ℤ`, the explicit presented group `J(S)` over `flagL` is `FP₂`.** -/
theorem isFP_two_JGrp_flagL (S : Set ℤ) : IsFP 2 (flagL.JGrp S) :=
  EdgeData.isFP_two_JGrp flagL_wf isPerfect_PiGrp_flagL S

end TheoremA.Leary
