module

public import RequestProject.TheoremA.Homological.L42.HConstr

/-!
# Lemma 4.2, part 6: the diagonal chain map `Δ : F → Q`

`Δ` is diagonally equivariant, commutes with the differentials through degree `m = k + 1` and
satisfies `(ε ⊗ ε) Δ₀ = ε`.  It is built using the contracting homotopy `Σ` of `Q`.
-/

@[expose] public section

namespace TheoremA

open TensorProduct

universe u

variable {B : Type u} [Group B] {k : ℕ}

namespace L42

variable {R : Res B k} (C : Contr R)

/-- `x₀ ⊗ x₀` in bidegree `(0, 0)`. -/
noncomputable def E00 : Qm R :=
  Pi.single (M := fun p => ∀ q, T R p q) 0 (Pi.single (M := fun q => T R 0 q) 0 (C.x0 ⊗ₜ C.x0))

theorem E00_deg : IsDeg 0 (E00 C) := by
  intro p q hpq
  by_cases hp : p = 0
  · subst hp
    have hq : q ≠ 0 := by omega
    simp [E00, hq]
  · simp [E00, hp]

@[simp] theorem E00_zero_zero : E00 C 0 0 = C.x0 ⊗ₜ C.x0 := by simp [E00]

/-- The diagonal chain map. -/
noncomputable def Δ : ∀ n, F R n →+ Qm R
  | 0 => ΔExt R (fun j => R.ε (Pi.single j 1) • E00 C)
  | n + 1 => ΔExt R (fun j => Sig C (Δ n (R.d n (Pi.single j 1))))

theorem Δ_of (n : ℕ) (g : B) (x : F R n) :
    Δ C n (MonoidAlgebra.of ℤ B g • x) = actQ R g g (Δ C n x) := by
  cases n <;> exact ΔExt_of R _ g x

theorem Δ_succ_single (n : ℕ) (j : Fin (R.c (n + 1))) :
    Δ C (n + 1) (Pi.single j 1) = Sig C (Δ C n (R.d n (Pi.single j 1))) :=
  ΔExt_single R _ j

theorem Δ_zero_single (j : Fin (R.c 0)) :
    Δ C 0 (Pi.single j 1) = R.ε (Pi.single j 1) • E00 C :=
  ΔExt_single R _ j

theorem isDeg_of_basis {n : ℕ} (φ : F R n →+ Qm R)
    (hφ : ∀ g x, φ (MonoidAlgebra.of ℤ B g • x) = actQ R g g (φ x))
    (hb : ∀ j, IsDeg n (φ (Pi.single j 1))) (x : F R n) : IsDeg n (φ x) := by
  intro p q hpq
  let ev : Qm R →+ T R p q := (Pi.evalAddMonoidHom (fun q => T R p q) q).comp
    (Pi.evalAddMonoidHom (fun p => ∀ q, T R p q) p)
  have := freeMod_hom_ext (φ := ev.comp φ) (ψ := 0) (fun i g => by
    simp only [AddMonoidHom.comp_apply, hφ, AddMonoidHom.zero_apply, ev,
      Pi.evalAddMonoidHom_apply, actQ_apply, hb i p q hpq, map_zero])
  exact congrArg (fun f => f x) this

theorem Δ_deg : ∀ n (x : F R n), IsDeg n (Δ C n x) := by
  intro n
  induction n with
  | zero =>
    refine isDeg_of_basis _ (Δ_of C 0) fun j => ?_
    rw [Δ_zero_single]
    intro p q hpq
    simp [E00_deg C p q hpq]
  | succ n ih =>
    refine isDeg_of_basis _ (Δ_of C (n + 1)) fun j => ?_
    rw [Δ_succ_single]
    exact (ih _).Sig C

theorem εε_act (b : B) (t : T R 0 0) : εε R (act R 0 0 b b t) = εε R t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp only [act, map_tmul, gsm_apply, εε_tmul, R.ε_inv]

theorem Δ_aug (x : F R 0) : εε R (Δ C 0 x 0 0) = R.ε x := by
  let ev : Qm R →+ ℤ := (εε R).toAddMonoidHom.comp
    ((Pi.evalAddMonoidHom (fun q => T R 0 q) 0).comp
      (Pi.evalAddMonoidHom (fun p => ∀ q, T R p q) 0))
  have := freeMod_hom_ext (φ := ev.comp (Δ C 0)) (ψ := R.ε) (fun i g => by
    simp only [AddMonoidHom.comp_apply, Δ_of, ev, Pi.evalAddMonoidHom_apply, actQ_apply,
      LinearMap.toAddMonoidHom_coe, εε_act, Δ_zero_single, R.ε_inv]
    simp [C.hx0, -zsmul_eq_mul])
  exact congrArg (fun f => f x) this

theorem map_ιε_ιε (t : T R 0 0) : map (ιε C) (ιε C) t = εε R t • (C.x0 ⊗ₜ C.x0) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_smul]
  | tmul x y =>
    rw [map_tmul, ιε_apply, ιε_apply, εε_tmul, tmul_smul, ← smul_tmul', smul_smul, mul_comm]

/-- `Δ` is a chain map through degree `m = k + 1`. -/
theorem Δ_chain : ∀ n, n ≤ k → ∀ x, D R (Δ C (n + 1) x) = Δ C n (R.d n x) := by
  intro n
  induction n with
  | zero =>
    intro _ x
    have := diag_hom_ext R (φ := (D R).comp (Δ C 1)) (ψ := (Δ C 0).comp (R.d 0).toAddMonoidHom)
      (fun g x => by simp only [AddMonoidHom.comp_apply, Δ_of, D_actQ])
      (fun g x => by
        simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, map_smul, Δ_of])
      (fun j => by
        simp only [AddMonoidHom.comp_apply, Δ_succ_single, LinearMap.toAddMonoidHom_coe]
        refine D_Sig_deg0 C (Δ_deg C 0 _) ?_
        rw [map_ιε_ιε, Δ_aug, R.ε_d, zero_smul])
    exact congrArg (fun f => f x) this
  | succ n ih =>
    intro hn x
    have := diag_hom_ext R (φ := (D R).comp (Δ C (n + 2)))
      (ψ := (Δ C (n + 1)).comp (R.d (n + 1)).toAddMonoidHom)
      (fun g x => by simp only [AddMonoidHom.comp_apply, Δ_of, D_actQ])
      (fun g x => by
        simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, map_smul, Δ_of])
      (fun j => by
        simp only [AddMonoidHom.comp_apply, Δ_succ_single, LinearMap.toAddMonoidHom_coe]
        refine D_Sig_of_cycle C (Δ_deg C (n + 1) _) ?_ (by omega) hn
        rw [ih (by omega), R.d_d n (by omega), map_zero])
    exact congrArg (fun f => f x) this

end L42

end TheoremA
