module

public import RequestProject.TheoremA.FP2.PerfectKernel
public import RequestProject.TheoremA.FP2.FPOneFG
public import RequestProject.TheoremA.Groups.IsFPTransport

/-!
# Quotients of `FP₂` groups by perfect normal subgroups

`isFP_two_quotient_of_perfect`: if `P` is of type `FP₂` and `N ⊴ P` is perfect
(`N ≤ ⁅N, N⁆`), then `P ⧸ N` is of type `FP₂`.

Proof: `P` is finitely generated (`IsFP.fg_of_le`), so `P ≅ F ⧸ K` for a free group `F` of finite
rank; with `M = π⁻¹(N)`, `P ⧸ N ≅ F ⧸ M`, and every element of `M` lies in `K ⊔ ⁅M, M⁆`
because `π(M) = N = ⁅N, N⁆ = π(⁅M, M⁆)`.  Then apply `isFP_two_presentedGroup_of_perfect_extension`.
-/

open scoped commutatorElement

@[expose] public section

namespace TheoremA

/-- **Quotients by perfect normal subgroups preserve `FP₂`.** -/
theorem isFP_two_quotient_of_perfect {P : Type*} [Group P] (hP : IsFP 2 P) (N : Subgroup P)
    [N.Normal] (hN : N ≤ ⁅N, N⁆) : IsFP 2 (P ⧸ N) := by
  obtain ⟨s, hs⟩ := Group.isMulFG_iff.mp (hP.fg_of_le (by norm_num))
  let m := s.card
  let x : Fin m → P := fun i => (s.equivFin.symm i : P)
  have hx : Subgroup.closure (Set.range x) = ⊤ := by
    rw [← hs]
    congr 1
    ext y
    simp only [Set.mem_range, Finset.mem_coe, x]
    constructor
    · rintro ⟨i, rfl⟩; exact (s.equivFin.symm i).2
    · intro hy; exact ⟨s.equivFin ⟨y, hy⟩, by simp⟩
  let π : FreeGroup (Fin m) →* P := FreeGroup.lift x
  have hπ : Function.Surjective π := by
    rw [← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure, hx]
  let K : Subgroup (FreeGroup (Fin m)) := π.ker
  let M : Subgroup (FreeGroup (Fin m)) := N.comap π
  have hK : Subgroup.normalClosure (K : Set (FreeGroup (Fin m))) = K :=
    Subgroup.normalClosure_eq_self K
  have hM : Subgroup.normalClosure (M : Set (FreeGroup (Fin m))) = M :=
    Subgroup.normalClosure_eq_self M
  -- `PresentedGroup K ≃* P`
  let e₀ : PresentedGroup (K : Set (FreeGroup (Fin m))) ≃* P :=
    (QuotientGroup.quotientMulEquivOfEq hK).trans (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  -- `PresentedGroup M ≃* P ⧸ N`
  let ψ : FreeGroup (Fin m) →* P ⧸ N := (QuotientGroup.mk' N).comp π
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective N).comp hπ
  have hψker : ψ.ker = M := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  let e : PresentedGroup (M : Set (FreeGroup (Fin m))) ≃* P ⧸ N :=
    (QuotientGroup.quotientMulEquivOfEq (hM.trans hψker.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hK2 : IsFP 2 (PresentedGroup (K : Set (FreeGroup (Fin m)))) := (IsFP.congr e₀).2 hP
  have hKM : (K : Set (FreeGroup (Fin m))) ⊆ M := fun y hy => by
    change π y ∈ N
    rw [(π.mem_ker).1 hy]
    exact N.one_mem
  have hcond : (M : Set (FreeGroup (Fin m))) ⊆
      (Subgroup.normalClosure (K : Set (FreeGroup (Fin m))) ⊔
        ⁅Subgroup.normalClosure (M : Set (FreeGroup (Fin m))),
          Subgroup.normalClosure (M : Set (FreeGroup (Fin m)))⁆ : Subgroup _) := by
    rw [hK, hM]
    intro y hy
    have hmap : Subgroup.map π M = N := Subgroup.map_comap_eq_self_of_surjective hπ N
    have h1 : π y ∈ Subgroup.map π ⁅M, M⁆ := by
      rw [Subgroup.map_commutator, hmap]
      exact hN hy
    obtain ⟨c, hc, hcy⟩ := h1
    have : y = (y * c⁻¹) * c := by group
    rw [this]
    refine Subgroup.mul_mem_sup ?_ hc
    change π (y * c⁻¹) = 1
    rw [map_mul, map_inv, hcy, mul_inv_cancel]
  exact (IsFP.congr e).1 (isFP_two_presentedGroup_of_perfect_extension _ _ hKM hK2 hcond)

end TheoremA
