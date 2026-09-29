module

public import RequestProject.TheoremA.Homological.L42.HMap

/-!
# Lemma 4.2, part 5: construction of the chain map `h` through degree `m = k + 1`
-/

@[expose] public section

namespace TheoremA

open TensorProduct

universe u

variable {B : Type u} [Group B] {k : ℕ}

namespace L42

variable {R : Res B k} (C : Contr R) (α β : B →* B)

theorem ε_hExt_eq {Y : Lvl R 0} (hαβ : ∀ b c, Commute (α b) (β c))
    (haug : ∀ i j, R.ε (Y 0 0 i j) = R.ε (Pi.single i 1) * R.ε (Pi.single j 1)) (t : T R 0 0) :
    R.ε (Hm R α β Y 0 0 t) = εε R t := by
  have := tensor_hom_ext R (fun _ _ => AddMonoidHom.id ℤ)
    (φ := R.ε.comp (Hm R α β Y 0 0)) (ψ := (εε R).toAddMonoidHom)
    (fun b c t => by
      simp only [AddMonoidHom.comp_apply, Hm_act R hαβ, AddMonoidHom.id_apply]
      exact R.ε_inv _ _)
    (fun b c t => by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy, AddMonoidHom.id_apply] at *
      | tmul x y =>
        simp only [LinearMap.toAddMonoidHom_coe, act, map_tmul, gsm_apply, εε_tmul,
          AddMonoidHom.id_apply, R.ε_inv])
    (fun i j => by simp [hExt_basis, haug])
  exact congrArg (fun f => f t) this

/-- Level `0` of `h`: `e_i ⊗ e_j ↦ ε(e_i) ε(e_j) x₀`. -/
noncomputable def Y0 : Lvl R 0
  | 0, 0 => fun i j => (R.ε (Pi.single i 1) * R.ε (Pi.single j 1)) • C.x0
  | 0, _ + 1 => 0
  | _ + 1, _ => 0

open Classical in
/-- All levels of `h`, obtained by successive lifting. -/
noncomputable def YY : ∀ n, Lvl R n
  | 0 => Y0 C
  | n + 1 => fun p q i j =>
    if h : p + q = n + 1 ∧ ∃ y, R.d n y = bd R α β (YY n) p q (Pi.single i 1 ⊗ₜ Pi.single j 1)
    then h.2.choose else 0

open Classical in
theorem YY_succ_apply (n p q : ℕ) (i : Fin (R.c p)) (j : Fin (R.c q)) :
    YY C α β (n + 1) p q i j =
      if h : p + q = n + 1 ∧
          ∃ y, R.d n y = bd R α β (YY C α β n) p q (Pi.single i 1 ⊗ₜ Pi.single j 1)
      then h.2.choose else 0 := rfl

theorem YY_off (n : ℕ) : OffZero R (YY C α β n) := by
  intro p q hpq
  rcases n with _ | n
  · rcases p with _ | p
    · rcases q with _ | q
      · omega
      · rfl
    · rfl
  · funext i j
    rw [YY_succ_apply, dif_neg (fun h => hpq h.1)]
    rfl

theorem YY_aug (i j) : R.ε (YY C α β 0 0 0 i j) = R.ε (Pi.single i 1) * R.ε (Pi.single j 1) := by
  show R.ε ((R.ε (Pi.single i 1) * R.ε (Pi.single j 1)) • C.x0) = _
  rw [map_zsmul, C.hx0, smul_eq_mul, mul_one]

theorem ε_bd0 (hαβ : ∀ b c, Commute (α b) (β c)) (p q : ℕ) (t : T R p q) :
    R.ε (bd R α β (YY C α β 0) p q t) = 0 := by
  have hL : ∀ p q (t : T R p q), R.ε (bdL R α β (YY C α β 0) p q t) = 0 := by
    intro p q t
    rcases p with _ | p
    · simp
    · by_cases h : p = 0 ∧ q = 0
      · obtain ⟨rfl, rfl⟩ := h
        rw [bdL_succ, ε_hExt_eq α β hαβ (YY_aug C α β), εε_dL]
      · rw [bdL_succ, Hm_off R α β (YY_off C α β 0) (by omega), map_zero]
  have hR : ∀ p q (t : T R p q), R.ε (bdR R α β (YY C α β 0) p q t) = 0 := by
    intro p q t
    rcases q with _ | q
    · simp
    · by_cases h : p = 0 ∧ q = 0
      · obtain ⟨rfl, rfl⟩ := h
        rw [bdR_succ, ε_hExt_eq α β hαβ (YY_aug C α β), εε_dR]
      · rw [bdR_succ, Hm_off R α β (YY_off C α β 0) (by omega), map_zero]
  simp only [bd, map_add, map_zsmul, hL, hR, smul_zero, add_zero]

/-- The chain condition for `h` in degrees `≤ m`. -/
theorem YY_chain (hαβ : ∀ b c, Commute (α b) (β c)) :
    ∀ n, n ≤ k → ∀ p q (t : T R p q),
      R.d n (Hm R α β (YY C α β (n + 1)) p q t) = bd R α β (YY C α β n) p q t := by
  intro n
  induction n with
  | zero =>
    intro _ p q
    refine chain_of_basis R hαβ _ _ p q fun i j => ?_
    by_cases hpq : p + q = 0 + 1
    · have hex : ∃ y, R.d 0 y = bd R α β (YY C α β 0) p q (Pi.single i 1 ⊗ₜ Pi.single j 1) := by
        have : bd R α β (YY C α β 0) p q (Pi.single i 1 ⊗ₜ Pi.single j 1) ∈ R.ε.ker :=
          ε_bd0 C α β hαβ p q _
        rw [R.exact0] at this
        exact this
      have h : p + q = 0 + 1 ∧ ∃ y, R.d 0 y =
          bd R α β (YY C α β 0) p q (Pi.single i 1 ⊗ₜ Pi.single j 1) := ⟨hpq, hex⟩
      rw [YY_succ_apply, dif_pos h]
      exact h.2.choose_spec
    · rw [YY_off C α β 1 p q hpq, bd_off R α β (YY_off C α β 0) hpq]
      simp
  | succ n ih =>
    intro hn p q
    refine chain_of_basis R hαβ _ _ p q fun i j => ?_
    by_cases hpq : p + q = n + 1 + 1
    · have hex : ∃ y, R.d (n + 1) y =
          bd R α β (YY C α β (n + 1)) p q (Pi.single i 1 ⊗ₜ Pi.single j 1) := by
        have : bd R α β (YY C α β (n + 1)) p q (Pi.single i 1 ⊗ₜ Pi.single j 1) ∈
            LinearMap.ker (R.d n) :=
          d_bd R α β _ _ (ih (by omega)) p q (by omega) (by omega) _
        rw [R.exact n (by omega)] at this
        exact this
      have h : p + q = n + 1 + 1 ∧ ∃ y, R.d (n + 1) y =
          bd R α β (YY C α β (n + 1)) p q (Pi.single i 1 ⊗ₜ Pi.single j 1) := ⟨hpq, hex⟩
      rw [YY_succ_apply, dif_pos h]
      exact h.2.choose_spec
    · rw [YY_off C α β (n + 1 + 1) p q hpq, bd_off R α β (YY_off C α β (n + 1)) hpq]
      simp

end L42

end TheoremA
