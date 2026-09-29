module

public import RequestProject.TheoremA.Leary.PoweredLoops

/-!
# The long-relator kernel and `FP₂` of `J(S)`

For `S : Set ℤ`, `JGrp D S` is the explicit presented group with the short relators of `P` and
the long relators `loopPow (fundCycle a) n` (`n ∈ S`, `a` any edge), where
`fundCycle a = p_{src a} · a · p_{tgt a}⁻¹` is the fundamental cycle of `a`.

* `qS D S : PGrp D →* JGrp D S` — the canonical surjection (`qS_of`, `qS_surjective`).
* `NS hD S = ⟨⟨⋃ n ∈ S, range ρₙ⟩⟩ ≤ P`.
* `ker_qS : (qS D S).ker = NS hD S` — the kernel is exactly the normal closure of the powered-loop
  images.
* `jEquiv hD S : JGrp D S ≃* PGrp D ⧸ NS hD S`, with `jEquiv_of` (compatibility on generators).
* `isFP_two_JGrp` — if `Π_L` is perfect then `J(S)` is `FP₂`, for **every** `S` (no enumeration,
  injectivity or geometry used).
* `loop_eq_one_of_mem` — the forward detection: for `n ∈ S` and a loop `γ` at the root, the
  image of `a₁ⁿ⋯a_kⁿ` in `J(S)` is trivial.
-/

@[expose] public section

namespace TheoremA.Leary

open Subgroup

namespace EdgeData

variable (D : EdgeData)

/-- The word `a₁ⁿ⋯a_kⁿ` in the free group. -/
def loopPow (w : List (Fin D.m)) (n : ℤ) : FreeGroup (Fin D.m) := (w.map fun e => D.fe e ^ n).prod

/-- The fundamental cycle of an edge `a : u → v`: `p_u · a · p_v⁻¹`. -/
def fundCycle (a : Fin D.m) : List (Fin D.m) :=
  D.path (D.src a) ++ [a] ++ D.revPath (D.path (D.tgt a))

/-- The long relators `a₁ⁿ⋯a_kⁿ` for `n ∈ S` and fundamental cycles. -/
def longRels (S : Set ℤ) : Set (FreeGroup (Fin D.m)) :=
  {r | ∃ n ∈ S, ∃ a, r = D.loopPow (D.fundCycle a) n}

/-- All relators of `J(S)`. -/
def jRels (S : Set ℤ) : Set (FreeGroup (Fin D.m)) := D.shortRels ∪ D.longRels S

/-- The group `J(S)`. -/
abbrev JGrp (S : Set ℤ) := PresentedGroup (D.jRels S)

/-- The canonical surjection `q_S : P → J(S)`. -/
def qS (S : Set ℤ) : D.PGrp →* D.JGrp S :=
  PresentedGroup.toGroup (f := fun a => (PresentedGroup.of a : D.JGrp S)) (fun r hr => by
    have hl : FreeGroup.lift (fun a => (PresentedGroup.of a : D.JGrp S)) =
        PresentedGroup.mk (D.jRels S) := by ext i; rfl
    rw [hl]
    exact (QuotientGroup.eq_one_iff _).2 (subset_normalClosure (Or.inl hr)))

theorem qS_of (S : Set ℤ) (a : Fin D.m) :
    D.qS S (PresentedGroup.of a) = PresentedGroup.of a :=
  PresentedGroup.toGroup.of _

theorem qS_surjective (S : Set ℤ) : Function.Surjective (D.qS S) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
    Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  exact ⟨PresentedGroup.of a, D.qS_of S a⟩

/-- The quotient map `F → P`. -/
abbrev mkP : FreeGroup (Fin D.m) →* D.PGrp := PresentedGroup.mk D.shortRels

theorem mkP_loopPow (w : List (Fin D.m)) (n : ℤ) : D.mkP (D.loopPow w n) = D.powVal n w := by
  simp only [loopPow, powVal, map_list_prod, List.map_map]
  rfl

theorem mkP_fundCycle (n : ℤ) (a : Fin D.m) :
    D.mkP (D.loopPow (D.fundCycle a) n) = D.zP n a := by
  rw [mkP_loopPow, fundCycle, powVal_append, powVal_append, powVal_revPath, zP, gP, gP]
  simp

variable {D}

/-- `N_S = ⟨⟨⋃ n ∈ S, range ρₙ⟩⟩`. -/
def NS (hD : D.WF) (S : Set ℤ) : Subgroup D.PGrp :=
  normalClosure (⋃ n ∈ S, Set.range (rho hD n))

instance NS_normal (hD : D.WF) (S : Set ℤ) : (NS hD S).Normal := normalClosure_normal

theorem mkP_surjective : Function.Surjective D.mkP := QuotientGroup.mk'_surjective _

/-- The image in `P` of the normal closure of all relators of `J(S)` is `N_S`. -/
theorem map_normalClosure_jRels (hD : D.WF) (S : Set ℤ) :
    (normalClosure (D.jRels S)).map D.mkP = NS hD S := by
  rw [Subgroup.map_normalClosure _ _ mkP_surjective]
  apply le_antisymm
  · apply normalClosure_le_normal
    rintro _ ⟨r, hr | ⟨n, hn, a, rfl⟩, rfl⟩
    · have h1 : D.mkP r = 1 := (QuotientGroup.eq_one_iff r).2 (subset_normalClosure hr)
      rw [h1]
      exact one_mem _
    · rw [mkP_fundCycle, ← rho_of hD]
      exact subset_normalClosure (Set.mem_biUnion hn ⟨_, rfl⟩)
  · haveI : (normalClosure (D.mkP '' D.jRels S)).Normal := normalClosure_normal
    apply normalClosure_le_normal
    simp only [Set.iUnion_subset_iff]
    intro n hn
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ Subgroup.closure (Set.range PresentedGroup.of) := by
      rw [PresentedGroup.closure_range_of]; trivial
    have : y ∈ (normalClosure (D.mkP '' D.jRels S)).comap (rho hD n) := by
      refine (Subgroup.closure_le _).2 ?_ hy
      rintro _ ⟨a, rfl⟩
      show (PresentedGroup.of a : D.PiGrp) ∈
        (normalClosure (D.mkP '' D.jRels S)).comap (rho hD n)
      rw [Subgroup.mem_comap, rho_of, ← mkP_fundCycle]
      exact subset_normalClosure ⟨_, Or.inr ⟨n, hn, a, rfl⟩, rfl⟩
    exact this

/-- `q_S ∘ (F → P)` is the quotient map `F → J(S)`. -/
theorem qS_mkP (S : Set ℤ) (r : FreeGroup (Fin D.m)) :
    D.qS S (D.mkP r) = PresentedGroup.mk (D.jRels S) r := by
  induction r using FreeGroup.induction_on with
  | C1 => simp
  | of a => exact D.qS_of S a
  | inv_of a ih => rw [map_inv, map_inv, ih, map_inv]
  | mul x y hx hy => rw [map_mul, map_mul, hx, hy, map_mul]

theorem mk_jRels_eq_one (S : Set ℤ) {r : FreeGroup (Fin D.m)} (hr : r ∈ D.jRels S) :
    PresentedGroup.mk (D.jRels S) r = 1 :=
  (QuotientGroup.eq_one_iff r).2 (subset_normalClosure hr)

/-- `N_S ≤ ker q_S`: `q_S` kills every powered-loop image. -/
theorem NS_le_ker (hD : D.WF) (S : Set ℤ) : NS hD S ≤ (D.qS S).ker := by
  apply normalClosure_le_normal
  simp only [Set.iUnion_subset_iff]
  intro n hn
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ Subgroup.closure (Set.range PresentedGroup.of) := by
    rw [PresentedGroup.closure_range_of]; trivial
  have : y ∈ (D.qS S).ker.comap (rho hD n) := by
    refine (Subgroup.closure_le _).2 ?_ hy
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, rho_of, ← mkP_fundCycle, MonoidHom.mem_ker, qS_mkP]
    exact D.mk_jRels_eq_one S (Or.inr ⟨n, hn, a, rfl⟩)
  exact Subgroup.mem_comap.mp this

/-- The map `J(S) → P ⧸ N_S`: every relator of `J(S)` dies in `P ⧸ N_S`. -/
def jToQuot (hD : D.WF) (S : Set ℤ) : D.JGrp S →* D.PGrp ⧸ NS hD S :=
  PresentedGroup.toGroup (f := fun a => (QuotientGroup.mk (D.xP a) : D.PGrp ⧸ NS hD S))
    (fun r hr => by
      have hl : FreeGroup.lift (fun a => (QuotientGroup.mk (D.xP a) : D.PGrp ⧸ NS hD S)) =
          (QuotientGroup.mk' (NS hD S)).comp D.mkP := by ext i; rfl
      rw [hl, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rcases hr with hr | ⟨n, hn, a, rfl⟩
      · have h1 : D.mkP r = 1 := (QuotientGroup.eq_one_iff r).2 (subset_normalClosure hr)
        rw [h1]
        exact one_mem _
      · rw [mkP_fundCycle, ← rho_of hD]
        exact subset_normalClosure (Set.mem_biUnion hn ⟨_, rfl⟩))

theorem jToQuot_of (hD : D.WF) (S : Set ℤ) (a : Fin D.m) :
    jToQuot hD S (PresentedGroup.of a) = QuotientGroup.mk (D.xP a) :=
  PresentedGroup.toGroup.of _

/-- The map `P ⧸ N_S → J(S)` induced by `q_S`. -/
noncomputable def quotToJ (hD : D.WF) (S : Set ℤ) : D.PGrp ⧸ NS hD S →* D.JGrp S :=
  QuotientGroup.lift (NS hD S) (D.qS S) (NS_le_ker hD S)

theorem jToQuot_qS (hD : D.WF) (S : Set ℤ) (x : D.PGrp) :
    jToQuot hD S (D.qS S x) = QuotientGroup.mk x := by
  have : (jToQuot hD S).comp (D.qS S) = QuotientGroup.mk' (NS hD S) := by
    apply PresentedGroup.ext
    intro a
    simp only [MonoidHom.comp_apply, qS_of, jToQuot_of]
    rfl
  exact DFunLike.congr_fun this x

/-- **(Q)**: `J(S) ≃* P ⧸ N_S`, compatible with the edge generators (`jEquiv_of`). -/
noncomputable def jEquiv (hD : D.WF) (S : Set ℤ) : D.JGrp S ≃* D.PGrp ⧸ NS hD S :=
  MonoidHom.toMulEquiv (jToQuot hD S) (quotToJ hD S)
    (by
      apply PresentedGroup.ext
      intro a
      simp only [MonoidHom.comp_apply, jToQuot_of, MonoidHom.id_apply, quotToJ,
        QuotientGroup.lift_mk, qS_of])
    (by
      apply QuotientGroup.monoidHom_ext
      apply PresentedGroup.ext
      intro a
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, QuotientGroup.mk'_apply]
      rw [quotToJ, QuotientGroup.lift_mk, jToQuot_qS])

theorem jEquiv_of (hD : D.WF) (S : Set ℤ) (a : Fin D.m) :
    jEquiv hD S (PresentedGroup.of a) = QuotientGroup.mk (D.xP a) :=
  jToQuot_of hD S a

theorem jEquiv_qS (hD : D.WF) (S : Set ℤ) (x : D.PGrp) :
    jEquiv hD S (D.qS S x) = QuotientGroup.mk x :=
  jToQuot_qS hD S x

/-- **Kernel identification**: `ker q_S = N_S`. -/
theorem ker_qS (hD : D.WF) (S : Set ℤ) : (D.qS S).ker = NS hD S := by
  ext x
  rw [MonoidHom.mem_ker, ← (jEquiv hD S).map_eq_one_iff, jEquiv_qS, QuotientGroup.eq_one_iff]

/-- **`J(S)` is `FP₂`** whenever the edge-path group is perfect. -/
theorem isFP_two_JGrp (hD : D.WF) (hPi : IsPerfectGroup D.PiGrp) (S : Set ℤ) :
    IsFP 2 (D.JGrp S) := by
  have h1 : IsFP 2 (D.PGrp ⧸ NS hD S) :=
    isFP_two_quotient_of_perfect D.isFP_two_PGrp _
      (normalClosure_ranges_perfect' hPi S (rho hD))
  exact IsFP.of_mulEquiv (jEquiv hD S).symm h1

/-- The generator of an edge in `J(S)`. -/
abbrev xJ (S : Set ℤ) (a : Fin D.m) : D.JGrp S := PresentedGroup.of a

theorem qS_powVal (S : Set ℤ) (n : ℤ) (w : List (Fin D.m)) :
    D.qS S (D.powVal n w) = (w.map fun e => D.xJ S e ^ n).prod := by
  simp only [powVal, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp [qS_of]

/-- **Forward detection**: for `n ∈ S` and a loop at the root, `a₁ⁿ⋯a_kⁿ = 1` in `J(S)`. -/
theorem loop_eq_one_of_mem (hD : D.WF) {S : Set ℤ} {n : ℤ} (hn : n ∈ S) (w : List (Fin D.m))
    (hw : IsWalk D D.root w D.root) : (w.map fun e => D.xJ S e ^ n).prod = 1 := by
  rw [← qS_powVal, ← rho_loop hD n w hw, ← MonoidHom.mem_ker, ker_qS hD]
  exact subset_normalClosure (Set.mem_biUnion hn ⟨_, rfl⟩)

/-- The separation statement is equivalent to non-membership of `ρₙ([γ])` in `N_S`. -/
theorem loop_eq_one_iff (hD : D.WF) (S : Set ℤ) (n : ℤ) (w : List (Fin D.m))
    (hw : IsWalk D D.root w D.root) :
    (w.map fun e => D.xJ S e ^ n).prod = 1 ↔ rho hD n (piVal w) ∈ NS hD S := by
  rw [← qS_powVal, ← rho_loop hD n w hw, ← MonoidHom.mem_ker, ker_qS hD]

end EdgeData

end TheoremA.Leary
