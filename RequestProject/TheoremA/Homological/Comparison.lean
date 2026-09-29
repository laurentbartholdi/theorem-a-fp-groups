module

public import RequestProject.TheoremA.Homological.Lifts

/-!
# Lemma 4.1 (comparison)

For two chain lifts `f`, `g` of the same endomorphism `θ`, `(f_m - g_m)(S)` lies in a finitely
generated submodule of `S`.
-/

@[expose] public section

namespace TheoremA

universe u

variable {B : Type u} [Group B] {k : ℕ}

/-- The homotopy equation (4.3) in degree `n`. -/
def HomEq (R : Res B k) (f g : ∀ i, FreeMod B (R.c i) →+ FreeMod B (R.c i))
    (K : ∀ i, FreeMod B (R.c i) →+ FreeMod B (R.c (i + 1))) : ℕ → Prop
  | 0 => ∀ x, f 0 x - g 0 x = R.d 0 (K 0 x)
  | n + 1 => ∀ x, f (n + 1) x - g (n + 1) x = R.d (n + 1) (K (n + 1) x) + K n (R.d n x)

theorem exists_homotopy (R : Res B k) (θ : B →* B) (f g : ∀ i, FreeMod B (R.c i) →+ FreeMod B (R.c i))
    (hf : IsChainLift R θ f) (hg : IsChainLift R θ g) :
    ∀ n, ∃ K : ∀ i, FreeMod B (R.c i) →+ FreeMod B (R.c (i + 1)),
      (∀ i (l : ZG B) x, K i (l • x) = hat θ l • K i x) ∧
      ∀ j, j < n → j ≤ k → HomEq R f g K j := by
  intro n
  induction n with
  | zero => exact ⟨fun _ => 0, fun _ _ _ => by simp, fun j hj => by omega⟩
  | succ n ih =>
    obtain ⟨K, hsl, heq⟩ := ih
    by_cases hn : n ≤ k
    · classical
      cases n with
      | zero =>
        have hmem : ∀ j : Fin (R.c 0),
            f 0 (Pi.single j 1) - g 0 (Pi.single j 1) ∈ LinearMap.range (R.d 0) := by
          intro j
          have : f 0 (Pi.single j 1) - g 0 (Pi.single j 1) ∈ R.ε.ker := by
            show R.ε _ = 0
            rw [map_sub, hf.aug, hg.aug, sub_self]
          rw [R.exact0] at this; exact this
        choose y hy using hmem
        let K0 : FreeMod B (R.c 0) →+ FreeMod B (R.c 1) := semiExt (hat θ) y
        refine ⟨Function.update (β := fun i => FreeMod B (R.c i) →+ FreeMod B (R.c (i + 1)))
          K 0 K0, ?_, ?_⟩
        · intro i l x
          by_cases h : i = 0
          · subst h; simp [K0, semiExt_smul]
          · simp [Function.update_of_ne h, hsl]
        · intro j hj _
          obtain rfl : j = 0 := by omega
          intro x
          rw [Function.update_self]
          have := semilinear_ext (hat θ) (f 0 - g 0) ((R.d 0).toAddMonoidHom.comp K0)
            (fun l x => by simp [hf.semilinear, hg.semilinear, smul_sub])
            (fun l x => by simp [K0, semiExt_smul])
            (fun j => by simp [K0, semiExt_single, hy])
          exact congrArg (fun F => F x) this
      | succ n =>
        have hmem : ∀ j : Fin (R.c (n + 1)),
            f (n + 1) (Pi.single j 1) - g (n + 1) (Pi.single j 1) -
              K n (R.d n (Pi.single j 1)) ∈ LinearMap.range (R.d (n + 1)) := by
          intro j
          rw [← R.exact n (by omega)]
          show R.d n _ = 0
          rw [map_sub, map_sub, ← hf.comm n (by omega), ← hg.comm n (by omega)]
          cases n with
          | zero =>
            have h0 := heq 0 (by omega) (by omega) (R.d 0 (Pi.single j 1))
            rw [h0, sub_self]
          | succ n' =>
            have h0 := heq (n' + 1) (by omega) (by omega) (R.d (n' + 1) (Pi.single j 1))
            rw [h0, R.d_d n' (by omega), map_zero, add_zero, sub_self]
        choose y hy using hmem
        let K1 : FreeMod B (R.c (n + 1)) →+ FreeMod B (R.c (n + 1 + 1)) := semiExt (hat θ) y
        refine ⟨Function.update (β := fun i => FreeMod B (R.c i) →+ FreeMod B (R.c (i + 1)))
          K (n + 1) K1, ?_, ?_⟩
        · intro i l x
          by_cases h : i = n + 1
          · subst h; simp [K1, semiExt_smul]
          · simp [Function.update_of_ne h, hsl]
        · intro j hj hjk
          by_cases h : j = n + 1
          · subst h
            intro x
            simp only [Function.update_self, Function.update_of_ne (show n ≠ n + 1 by omega)]
            have := semilinear_ext (hat θ) (f (n + 1) - g (n + 1) - (K n).comp (R.d n).toAddMonoidHom)
              ((R.d (n + 1)).toAddMonoidHom.comp K1)
              (fun l x => by simp [hf.semilinear, hg.semilinear, hsl, smul_sub])
              (fun l x => by simp [K1, semiExt_smul])
              (fun j => by simp [K1, semiExt_single, hy])
            have hx := congrArg (fun F => F x) this
            simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
              LinearMap.toAddMonoidHom_coe] at hx
            rw [← hx]; abel
          · have hj' : j < n + 1 := by omega
            have := heq j hj' hjk
            cases j with
            | zero =>
              simp only [HomEq] at this ⊢
              rwa [Function.update_of_ne (show (0 : ℕ) ≠ n + 1 by omega)]
            | succ j =>
              simp only [HomEq] at this ⊢
              rwa [Function.update_of_ne (show j + 1 ≠ n + 1 by omega),
                Function.update_of_ne (show j ≠ n + 1 by omega)]
    · exact ⟨K, hsl, fun j hj hjk => heq j (by omega) hjk⟩

/-- **Lemma 4.1 (comparison).** -/
theorem comparison (R : Res B k) (θ : B →* B) (f g : ∀ i, FreeMod B (R.c i) →+ FreeMod B (R.c i))
    (hf : IsChainLift R θ f) (hg : IsChainLift R θ g) :
    ∃ N : Submodule (ZG B) (FreeMod B (R.c (k + 1))), N.FG ∧ N ≤ R.S ∧
      ∀ s ∈ R.S, f (k + 1) s - g (k + 1) s ∈ N := by
  obtain ⟨K, hsl, heq⟩ := exists_homotopy R θ f g hf hg (k + 1)
  let C : FreeMod B (R.c (k + 1)) →+ FreeMod B (R.c (k + 1)) :=
    f (k + 1) - g (k + 1) - (K k).comp (R.d k).toAddMonoidHom
  have hCsl : ∀ l x, C (l • x) = hat θ l • C x := by
    intro l x; simp [C, hf.semilinear, hg.semilinear, hsl, smul_sub]
  have hCS : ∀ x, C x ∈ R.S := by
    intro x
    show R.d k (C x) = 0
    simp only [C, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
      map_sub, ← hf.comm k le_rfl, ← hg.comm k le_rfl]
    cases k with
    | zero =>
      have h0 := heq 0 (by omega) le_rfl (R.d 0 x)
      rw [h0, sub_self]
    | succ k' =>
      have h0 := heq (k' + 1) (by omega) le_rfl (R.d (k' + 1) x)
      rw [h0, R.d_d k' (by omega), map_zero, add_zero, sub_self]
  refine ⟨Submodule.span (ZG B) (Set.range fun j => C (Pi.single j 1)),
    Submodule.fg_span (Set.finite_range _), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩; exact hCS _
  · intro s hs
    have hs' : R.d k s = 0 := hs
    have : C s = f (k + 1) s - g (k + 1) s := by
      simp [C, hs']
    rw [← this]
    exact semilinear_mem_span (hat θ) C hCsl s

end TheoremA
