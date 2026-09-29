module

public import RequestProject.TheoremA.Homological.HNNTorus

/-!
# The chain maps `T_i` of (5.2) on the induced complex
-/

@[expose] public section

namespace TheoremA

universe u

open MonoidAlgebra

variable {B E : Type u} [Group B] [Group E]

/-- The `ℤ[E]`-linear map `ℤ[E]^a → ℤ[E]^b` sending the `j`-th basis vector to `y j`. -/
noncomputable def matMap {a b : ℕ} (y : Fin a → FreeMod E b) : FreeMod E a →ₗ[ZG E] FreeMod E b where
  toFun x := ∑ j, x j • y j
  map_add' x x' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' l x := by simp [Finset.smul_sum, mul_smul]

theorem matMap_single {a b : ℕ} (y : Fin a → FreeMod E b) (j : Fin a) :
    matMap y (Pi.single j 1) = y j := by
  simp [matMap, Pi.single_apply]

/-- Two `ℤ[E]`-linear maps on `ℤ[E]^a` agreeing on the basis are equal. -/
theorem linear_ext_single {a : ℕ} {N : Type*} [AddCommGroup N] [Module (ZG E) N]
    (f g : FreeMod E a →ₗ[ZG E] N) (h : ∀ j, f (Pi.single j 1) = g (Pi.single j 1)) : f = g := by
  have := semilinear_ext (RingHom.id (ZG E)) f.toAddMonoidHom g.toAddMonoidHom
    (fun l x => by simp) (fun l x => by simp) h
  exact LinearMap.ext fun x => congrArg (fun F => F x) this

theorem ρV_single (ι : B →* E) {n : ℕ} (j : Fin n) :
    ρV ι (Pi.single j 1 : FreeMod B n) = Pi.single j 1 := by
  ext i : 1
  by_cases h : i = j
  · subst h; simp [ρV_apply]
  · simp [ρV_apply, h]

variable (φ : B →* B) (hφ : Function.Injective φ) {k : ℕ} (R : Res B k)
  (Φ : ∀ i, FreeMod B (R.c i) →+ FreeMod B (R.c i))

/-- `T_i(a ⊗ x) = a s ⊗ Φ_i(x)` (5.2), in coordinates. -/
noncomputable def Tmap (i : ℕ) : FreeMod (ascHNN φ hφ) (R.c i) →ₗ[ZG (ascHNN φ hφ)]
    FreeMod (ascHNN φ hφ) (R.c i) :=
  matMap fun j => MonoidAlgebra.single (sE φ hφ) (1 : ℤ) • ρV (ofE φ hφ) (Φ i (Pi.single j 1))

variable {φ hφ R Φ}

theorem Tmap_ρV (hΦ : IsChainLift R φ Φ) (i : ℕ) (w : FreeMod B (R.c i)) :
    Tmap φ hφ R Φ i (ρV (ofE φ hφ) w) =
      MonoidAlgebra.single (sE φ hφ) (1 : ℤ) • ρV (ofE φ hφ) (Φ i w) := by
  conv_rhs => rw [eq_sum_single w]
  conv_lhs => rw [eq_sum_single w]
  simp only [map_sum, ρV_smul, ρV_single, map_smul, Tmap, matMap_single, hΦ.semilinear,
    Finset.smul_sum, smul_smul, ρ_mul_sE]

theorem Tmap_comm (hΦ : IsChainLift R φ Φ) (i : ℕ) (hi : i ≤ k)
    (x : FreeMod (ascHNN φ hφ) (R.c (i + 1))) :
    indMap (ofE φ hφ) (R.d i) (Tmap φ hφ R Φ (i + 1) x) =
      Tmap φ hφ R Φ i (indMap (ofE φ hφ) (R.d i) x) := by
  have := linear_ext_single ((indMap (ofE φ hφ) (R.d i)).comp (Tmap φ hφ R Φ (i + 1)))
    ((Tmap φ hφ R Φ i).comp (indMap (ofE φ hφ) (R.d i))) (fun j => by
      simp only [LinearMap.comp_apply, Tmap, matMap_single, map_smul, indMap_ρV]
      rw [indMap_single, ← Tmap, Tmap_ρV hΦ, hΦ.comm i hi])
  exact congrArg (fun F => F x) this

theorem εM_smul_sE_ρV (hΦ : IsChainLift R φ Φ) (f : ZG (ascHNN φ hφ)) (j : Fin (R.c 0)) :
    εM (ofE φ hφ) R (f • (MonoidAlgebra.single (sE φ hφ) (1 : ℤ) •
      ρV (ofE φ hφ) (Φ 0 (Pi.single j 1)))) =
      R.ε (Pi.single j 1) • TM φ hφ (πM (ofE φ hφ) f) := by
  simp only [εM, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, ρV_apply, smul_eq_mul,
    πM_mul_sE_mul, smul_smul]
  rw [← Finset.sum_smul, ← hΦ.aug (Pi.single j 1), ε_eq_sum R (Φ 0 (Pi.single j 1))]
  congr 1
  exact Finset.sum_congr rfl fun j' _ => mul_comm _ _

theorem εM_smul_single (f : ZG (ascHNN φ hφ)) (j : Fin (R.c 0)) :
    εM (ofE φ hφ) R (f • (Pi.single j 1 : FreeMod (ascHNN φ hφ) (R.c 0))) =
      R.ε (Pi.single j 1) • πM (ofE φ hφ) f := by
  simp only [εM, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem εM_Tmap (hΦ : IsChainLift R φ Φ) (v : FreeMod (ascHNN φ hφ) (R.c 0)) :
    εM (ofE φ hφ) R (Tmap φ hφ R Φ 0 v) = TM φ hφ (εM (ofE φ hφ) R v) := by
  conv_lhs => rw [eq_sum_single v]
  conv_rhs => rw [eq_sum_single v]
  simp only [map_sum, map_smul, Tmap, matMap_single, εM_smul_sE_ρV hΦ, εM_smul_single,
    map_zsmul]

theorem εA_Tmap (hΦ : IsChainLift R φ Φ) (v : FreeMod (ascHNN φ hφ) (R.c 0)) :
    εA (ofE φ hφ) R (Tmap φ hφ R Φ 0 v) = εA (ofE φ hφ) R v := by
  simp only [εA, AddMonoidHom.comp_apply, εM_Tmap hΦ, augM_TM]

end TheoremA
