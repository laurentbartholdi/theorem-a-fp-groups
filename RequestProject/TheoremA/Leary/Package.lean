module

public import RequestProject.TheoremA.Leary.Instance
public import RequestProject.TheoremA.Leary.Oracle
public import RequestProject.TheoremA.Groups.CodingHB

/-!
# The detection package for `J(S)` over `flagL`

* `jDet S : Fin 4 → J(S)` — the images `j_i = q_S(a_i)` of the four edges of the distinguished
  loop `γ = flagLoopL` (the subdivided loop `s`, nonidentity in the edge-path group).
* `Ys_jDet` — `j₁ⁿ j₂ⁿ j₃ⁿ j₄ⁿ` is the image of the powered loop.
* `jDet_forward` — **proved**: `n ∈ S → j₁ⁿ⋯j₄ⁿ = 1` (from the kernel identification).
* `jDet_eq_one_iff_mem_NS` — **proved**: `j₁ⁿ⋯j₄ⁿ = 1 ↔ ρₙ([γ]) ∈ N_S`.
* `FlagSeparation` — the separation statement (SEP) for `flagL` and `γ`, for all integers
  `n ≠ 0` (negative ones included).  It is stated here as a `Prop`; it is **proved** in
  `Leary/Detection.lean` (`flagSeparation`) by a combinatorial argument (a heap model of the
  right-angled Artin group of the 1-skeleton of `flagL` and an `S₅`-labelled action).
* `jDet_iff_of_separation` — from (SEP) and `0 ∈ S`: `∀ n, j₁ⁿ⋯j₄ⁿ = 1 ↔ n ∈ S`
  (the case `n = 0` is handled directly using `0 ∈ S`).
* `hb_VS_of_separation` — from (SEP): for every `R`-enumerable `S ∋ 0`, `V_S` is `HB_R` in `F_c`
  (the existing `hb_VS`, with `J = J(S)`, `IsFP 2 J(S)` unconditional and `ClassCR R J(S)` from
  the same-oracle enumerator).
-/

@[expose] public section

namespace TheoremA.Leary

open TheoremA.RelPres TheoremA.Coding EdgeData

theorem flagLoopL_length : flagLoopL.length = 4 := rfl

/-- The distinguished elements `j_i = q_S(a_i)` of `J(S)`. -/
def jDet (S : Set ℤ) (i : Fin 4) : flagL.JGrp S :=
  flagL.xJ S (flagLoopL.get (Fin.cast flagLoopL_length.symm i))

theorem Ys_jDet (S : Set ℤ) (n : ℤ) :
    Ys (jDet S) n = (flagLoopL.map fun e => flagL.xJ S e ^ n).prod := by
  have : (List.ofFn fun i : Fin 4 => jDet S i ^ n) = flagLoopL.map fun e => flagL.xJ S e ^ n := by
    rw [← List.ofFn_get flagLoopL, List.map_ofFn]
    rfl
  rw [Ys, this]

/-- **Forward detection** (proved). -/
theorem jDet_forward {S : Set ℤ} {n : ℤ} (hn : n ∈ S) : Ys (jDet S) n = 1 := by
  rw [Ys_jDet]
  exact loop_eq_one_of_mem flagL_wf hn _ flagLoop_isWalk

/-- The detection statement is exactly membership of `ρₙ([γ])` in `N_S`. -/
theorem jDet_eq_one_iff_mem_NS (S : Set ℤ) (n : ℤ) :
    Ys (jDet S) n = 1 ↔ rho flagL_wf n (piVal flagLoopL) ∈ NS flagL_wf S := by
  rw [Ys_jDet]
  exact loop_eq_one_iff flagL_wf S n _ flagLoop_isWalk

/-- **(SEP)** for `flagL` and the loop `γ = flagLoopL`: for every `S ⊆ ℤ` and every integer
`n ≠ 0` with `n ∉ S`, `ρₙ([γ]) ∉ N_S`.  Proved as `flagSeparation` in `Leary/Detection.lean`. -/
def FlagSeparation : Prop :=
  ∀ (S : Set ℤ) (n : ℤ), n ≠ 0 → n ∉ S → rho flagL_wf n (piVal flagLoopL) ∉ NS flagL_wf S

/-- The full detection `iff`, from (SEP) and `0 ∈ S`. -/
theorem jDet_iff_of_separation (hSep : FlagSeparation) {S : Set ℤ} (h0 : (0 : ℤ) ∈ S) (n : ℤ) :
    Ys (jDet S) n = 1 ↔ n ∈ S := by
  refine ⟨fun h => ?_, jDet_forward⟩
  by_contra hn
  have hn0 : n ≠ 0 := by rintro rfl; exact hn h0
  exact hSep S n hn0 hn ((jDet_eq_one_iff_mem_NS S n).1 h)

/-- **`HB_R(V_S)` from (SEP)**, via the existing `hb_VS`. -/
theorem hb_VS_of_separation (hSep : FlagSeparation) {R : Set ℕ} {S : Set ℤ}
    (hS : IntEnumerable R S) (h0 : (0 : ℤ) ∈ S) : HB R (VS 4 S) :=
  hb_VS (jDet S) (by norm_num) (classCR_JGrp hS) (isFP_two_JGrp_flagL S)
    (jDet_iff_of_separation hSep h0) h0

end TheoremA.Leary
