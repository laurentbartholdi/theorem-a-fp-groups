module

public import RequestProject.TheoremA.Homological.L42.Homotopy

/-!
# Lemma 4.2, part 3: extension principles

* additive maps on `F_p` (resp. `F_p ⊗ F_q`) that are equivariant for the group action are
  determined by their values on the basis (resp. on tensors of basis vectors);
* `hExt Y`: the `η`-semilinear map `F_p ⊗ F_q → M`, `η(b, c) = α(b) β(c)`, with prescribed values
  on basis tensors (this needs commuting images of `α` and `β`);
* `ΔExt y`: the diagonally equivariant map `F_n → Q` with prescribed values on the basis.
-/

@[expose] public section

namespace TheoremA

open TensorProduct

universe u

variable {B : Type u} [Group B] {k : ℕ}

theorem of_smul_single_eq {c : ℕ} (g : B) (n : ℤ) (i : Fin c) :
    (MonoidAlgebra.single g n : ZG B) • (Pi.single i 1 : FreeMod B c) =
      n • (MonoidAlgebra.of ℤ B g • (Pi.single i 1 : FreeMod B c)) := by
  rw [← smul_assoc]; congr 1; simp

/-- Additive maps on `Λ^c` agreeing on the translates `g e_i` of the basis are equal. -/
theorem freeMod_hom_ext {c : ℕ} {M : Type*} [AddCommGroup M] {φ ψ : FreeMod B c →+ M}
    (h : ∀ i g, φ (MonoidAlgebra.of ℤ B g • (Pi.single i 1 : FreeMod B c)) =
      ψ (MonoidAlgebra.of ℤ B g • (Pi.single i 1 : FreeMod B c))) :
    φ = ψ := by
  refine AddMonoidHom.ext fun x => ?_
  rw [eq_sum_single x, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  induction x i using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [add_smul, map_add, map_add, ha, hb]
  | single g n => rw [of_smul_single_eq, map_zsmul, map_zsmul, h]

/-- Group-equivariance implies semilinearity. -/
theorem semilinear_of_group {c : ℕ} {N : Type*} [AddCommGroup N] [Module (ZG B) N] (θ : B →* B)
    (φ : FreeMod B c →+ N)
    (h : ∀ g x, φ (MonoidAlgebra.of ℤ B g • x) = MonoidAlgebra.of ℤ B (θ g) • φ x)
    (l : ZG B) (x : FreeMod B c) : φ (l • x) = hat θ l • φ x := by
  induction l using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [add_smul, map_add, ha, hb, map_add, add_smul]
  | single g n =>
    have e1 : (MonoidAlgebra.single g n : ZG B) • x = n • (MonoidAlgebra.of ℤ B g • x) := by
      rw [← smul_assoc]; congr 1; simp
    have e2 : hat θ (MonoidAlgebra.single g n) = n • MonoidAlgebra.of ℤ B (θ g) := by
      simp [hat]
    rw [e1, map_zsmul, h, e2, smul_assoc]

theorem hat_of (θ : B →* B) (g : B) :
    hat θ (MonoidAlgebra.of ℤ B g) = MonoidAlgebra.of ℤ B (θ g) := by
  simp [hat]

theorem hat_id (l : ZG B) : hat (MonoidHom.id B) l = l := by
  induction l using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, ha, hb]
  | single g n => simp [hat]

namespace L42

variable (R : Res B k)

/-- Equivariant additive maps on `F_p ⊗ F_q` agreeing on basis tensors are equal. -/
theorem tensor_hom_ext {p q : ℕ} {M : Type*} [AddCommGroup M] (A : B → B → M →+ M)
    {φ ψ : T R p q →+ M} (hφ : ∀ b c t, φ (act R p q b c t) = A b c (φ t))
    (hψ : ∀ b c t, ψ (act R p q b c t) = A b c (ψ t))
    (h : ∀ i j, φ (Pi.single i 1 ⊗ₜ Pi.single j 1) = ψ (Pi.single i 1 ⊗ₜ Pi.single j 1)) :
    φ = ψ := by
  refine AddMonoidHom.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul x y =>
    have step1 : ∀ i g (y : F R q),
        φ ((MonoidAlgebra.of ℤ B g • (Pi.single i 1 : F R p)) ⊗ₜ y) =
        ψ ((MonoidAlgebra.of ℤ B g • (Pi.single i 1 : F R p)) ⊗ₜ y) := by
      intro i g y
      have := freeMod_hom_ext
        (φ := φ.comp (TensorProduct.mk ℤ (F R p) (F R q)
          (MonoidAlgebra.of ℤ B g • (Pi.single i 1 : F R p))).toAddMonoidHom)
        (ψ := ψ.comp (TensorProduct.mk ℤ (F R p) (F R q)
          (MonoidAlgebra.of ℤ B g • (Pi.single i 1 : F R p))).toAddMonoidHom) (fun j g' => by
          have e : (MonoidAlgebra.of ℤ B g • (Pi.single i 1 : F R p)) ⊗ₜ[ℤ]
              (MonoidAlgebra.of ℤ B g' • (Pi.single j 1 : F R q)) =
              act R p q g g' (Pi.single i 1 ⊗ₜ Pi.single j 1) := rfl
          simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, mk_apply]
          rw [e, hφ, hψ, h])
      exact congrArg (fun f => f y) this
    have := freeMod_hom_ext
      (φ := φ.comp ((TensorProduct.mk ℤ (F R p) (F R q)).flip y).toAddMonoidHom)
      (ψ := ψ.comp ((TensorProduct.mk ℤ (F R p) (F R q)).flip y).toAddMonoidHom)
      (fun i g => by
        simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearMap.flip_apply,
          mk_apply]
        exact step1 i g y)
    exact congrArg (fun f => f x) this

section hExt

variable (α β : B →* B) (hαβ : ∀ b c, Commute (α b) (β c))
include hαβ

theorem commute_hat (a a' : ZG B) : Commute (hat α a) (hat β a') := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add]; exact ha.add_left hb
  | single g n =>
    induction a' using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact ha.add_right hb
    | single g' n' =>
      simp only [hat, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
      show _ * _ = _ * _
      rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, (hαβ g g').eq,
        mul_comm n n']

omit hαβ in
/-- The biadditive map behind `hExt`. -/
noncomputable def hBil {p q : ℕ} {M : Type*} [AddCommGroup M] [Module (ZG B) M]
    (Y : Fin (R.c p) → Fin (R.c q) → M) : F R p →+ F R q →+ M :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
    (fun y => ∑ i, ∑ j, (hat α (x i) * hat β (y j)) • Y i j)
    (fun y y' => by
      simp only [Pi.add_apply, map_add, mul_add, add_smul, Finset.sum_add_distrib]))
    (fun x x' => by
      refine AddMonoidHom.ext fun y => ?_
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Pi.add_apply, map_add, add_mul,
        add_smul, Finset.sum_add_distrib])

omit hαβ in
/-- The `η`-semilinear map `F_p ⊗ F_q → M` with values `Y i j` on basis tensors. -/
noncomputable def hExt {p q : ℕ} {M : Type*} [AddCommGroup M] [Module (ZG B) M]
    (Y : Fin (R.c p) → Fin (R.c q) → M) : T R p q →+ M :=
  TensorProduct.liftAddHom (hBil R α β Y) (fun r x y => by
    simp only [map_zsmul, AddMonoidHom.smul_apply])

omit hαβ in
theorem hExt_tmul {p q : ℕ} {M : Type*} [AddCommGroup M] [Module (ZG B) M]
    (Y : Fin (R.c p) → Fin (R.c q) → M) (x : F R p) (y : F R q) :
    hExt R α β Y (x ⊗ₜ y) = ∑ i, ∑ j, (hat α (x i) * hat β (y j)) • Y i j := rfl

omit hαβ in
theorem hExt_basis {p q : ℕ} {M : Type*} [AddCommGroup M] [Module (ZG B) M]
    (Y : Fin (R.c p) → Fin (R.c q) → M) (i : Fin (R.c p)) (j : Fin (R.c q)) :
    hExt R α β Y (Pi.single i 1 ⊗ₜ Pi.single j 1) = Y i j := by
  rw [hExt_tmul]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem hExt_act {p q : ℕ} {M : Type*} [AddCommGroup M] [Module (ZG B) M]
    (Y : Fin (R.c p) → Fin (R.c q) → M) (b c : B) (t : T R p q) :
    hExt R α β Y (act R p q b c t) = MonoidAlgebra.of ℤ B (α b * β c) • hExt R α β Y t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul x y =>
    have key : ∀ a a' : ZG B, hat α (MonoidAlgebra.of ℤ B b * a) * hat β (MonoidAlgebra.of ℤ B c * a')
        = MonoidAlgebra.of ℤ B (α b * β c) * (hat α a * hat β a') := by
      intro a a'
      have hc := (commute_hat α β hαβ a (MonoidAlgebra.of ℤ B c)).eq
      rw [hat_of] at hc
      rw [map_mul, map_mul, hat_of, hat_of, map_mul, mul_assoc, ← mul_assoc (hat α a), hc]
      simp only [mul_assoc]
    simp only [act, map_tmul, gsm_apply, hExt_tmul, Pi.smul_apply, smul_eq_mul, key, mul_smul,
      Finset.smul_sum]

end hExt

section ΔExt

/-- The diagonal action of `ℤ[B]` on bigraded families. -/
noncomputable def ρ : ZG B →ₐ[ℤ] Module.End ℤ (Qm R) :=
  MonoidAlgebra.lift ℤ (Module.End ℤ (Qm R)) B
    { toFun := fun g => (actQ R g g).toIntLinearMap
      map_one' := by
        refine LinearMap.ext fun z => ?_
        funext p q; exact act_one R p q (z p q)
      map_mul' := fun g g' => by
        refine LinearMap.ext fun z => ?_
        funext p q; exact act_mul R p q g g g' g' (z p q) }

theorem ρ_of (g : B) (z : Qm R) : ρ R (MonoidAlgebra.of ℤ B g) z = actQ R g g z := by
  simp [ρ]

/-- The diagonally equivariant map `F_n → Q` with values `y j` on the basis. -/
noncomputable def ΔExt {n : ℕ} (y : Fin (R.c n) → Qm R) : F R n →+ Qm R where
  toFun x := ∑ j, ρ R (x j) (y j)
  map_zero' := by simp
  map_add' x x' := by simp [Finset.sum_add_distrib]

theorem ΔExt_single {n : ℕ} (y : Fin (R.c n) → Qm R) (j : Fin (R.c n)) :
    ΔExt R y (Pi.single j 1) = y j := by
  simp only [ΔExt, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem ΔExt_of {n : ℕ} (y : Fin (R.c n) → Qm R) (g : B) (x : F R n) :
    ΔExt R y (MonoidAlgebra.of ℤ B g • x) = actQ R g g (ΔExt R y x) := by
  simp only [ΔExt, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, smul_eq_mul, map_mul,
    Module.End.mul_apply, ρ_of, map_sum]

/-- Diagonally equivariant additive maps `F_n → Q` agreeing on the basis are equal. -/
theorem diag_hom_ext {n : ℕ} {φ ψ : F R n →+ Qm R}
    (hφ : ∀ g x, φ (MonoidAlgebra.of ℤ B g • x) = actQ R g g (φ x))
    (hψ : ∀ g x, ψ (MonoidAlgebra.of ℤ B g • x) = actQ R g g (ψ x))
    (h : ∀ j, φ (Pi.single j 1) = ψ (Pi.single j 1)) : φ = ψ :=
  freeMod_hom_ext fun i g => by rw [hφ, hψ, h]

end ΔExt

end L42

end TheoremA
