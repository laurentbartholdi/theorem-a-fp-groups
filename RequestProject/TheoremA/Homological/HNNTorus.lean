module

public import RequestProject.TheoremA.Homological.CosetModule

/-!
# The ascending HNN extension: the exact sequence (5.3) and the maps `T_i` (5.2)

For `E = ascHNN φ hφ` we use the stable letter `s = t⁻¹`, which satisfies `b s = s φ(b)`
(the manuscript's `t`).  On `M = ℤ[E / B]`, `T_M(gB) = gsB`.  We prove (5.3): `1 - T_M` is
injective with cokernel `ℤ` (via the augmentation), and define the `ℤ[E]`-linear maps
`T_i(a ⊗ x) = a s ⊗ Φ_i(x)` of (5.2).
-/

@[expose] public section

namespace TheoremA

universe u

open MonoidAlgebra

variable {B : Type u} [Group B] (φ : B →* B) (hφ : Function.Injective φ)

/-- The inclusion of the base into the ascending HNN extension. -/
abbrev ofE : B →* ascHNN φ hφ := HNNExtension.of

/-- The stable letter `s = t⁻¹`, with `b s = s φ(b)`. -/
noncomputable def sE : ascHNN φ hφ := HNNExtension.t⁻¹

theorem of_mul_sE (b : B) : ofE φ hφ b * sE φ hφ = sE φ hφ * ofE φ hφ (φ b) := by
  have h : (HNNExtension.t : ascHNN φ hφ) * HNNExtension.of b =
      HNNExtension.of (φ b) * HNNExtension.t :=
    HNNExtension.t_mul_of (G := B) (A := ⊤) (B := φ.range)
      (φ := Subgroup.topEquiv.trans (MonoidHom.ofInjective hφ)) ⟨b, Subgroup.mem_top b⟩
  unfold sE ofE
  rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]

/-- Right multiplication by `s` on cosets `gB ↦ gsB`. -/
noncomputable def rmul : ascHNN φ hφ ⧸ (ofE φ hφ).range → ascHNN φ hφ ⧸ (ofE φ hφ).range :=
  Quotient.map' (· * sE φ hφ) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    obtain ⟨c, hc⟩ := hab
    refine ⟨φ c, ?_⟩
    rw [mul_inv_rev, mul_assoc, ← mul_assoc a⁻¹, ← hc, of_mul_sE, ← mul_assoc, inv_mul_cancel,
      one_mul])

theorem rmul_mk (g : ascHNN φ hφ) :
    rmul φ hφ (cosetOf (ofE φ hφ) g) = cosetOf (ofE φ hφ) (g * sE φ hφ) := rfl

/-- `T_M : M → M`, `gB ↦ gsB`. -/
noncomputable def TM : ((ascHNN φ hφ ⧸ (ofE φ hφ).range) →₀ ℤ) →+
    ((ascHNN φ hφ ⧸ (ofE φ hφ).range) →₀ ℤ) :=
  Finsupp.mapDomain.addMonoidHom (rmul φ hφ)

theorem TM_single (q : ascHNN φ hφ ⧸ (ofE φ hφ).range) (n : ℤ) :
    TM φ hφ (Finsupp.single q n) = Finsupp.single (rmul φ hφ q) n := by
  simp [TM]

/-- The height homomorphism `E → ℤ`, `t ↦ 1`, `B ↦ 0`. -/
noncomputable def ht : ascHNN φ hφ →* Multiplicative ℤ :=
  HNNExtension.lift (1 : B →* Multiplicative ℤ) (Multiplicative.ofAdd 1) (by simp)

theorem ht_of (b : B) : ht φ hφ (ofE φ hφ b) = 1 := by
  simp [ht, ofE, HNNExtension.lift_of]

theorem ht_sE : ht φ hφ (sE φ hφ) = Multiplicative.ofAdd (-1) := by
  simp [ht, sE, HNNExtension.lift_t]

/-- Height of a coset. -/
noncomputable def htQ : ascHNN φ hφ ⧸ (ofE φ hφ).range → ℤ :=
  fun q => Quotient.liftOn' q (fun g => Multiplicative.toAdd (ht φ hφ g)) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    obtain ⟨c, hc⟩ := hab
    have : ht φ hφ (a⁻¹ * b) = 1 := by rw [← hc]; exact ht_of φ hφ c
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    simp [this])

theorem htQ_mk (g : ascHNN φ hφ) :
    htQ φ hφ (cosetOf (ofE φ hφ) g) = Multiplicative.toAdd (ht φ hφ g) := rfl

theorem htQ_rmul (q : ascHNN φ hφ ⧸ (ofE φ hφ).range) : htQ φ hφ (rmul φ hφ q) = htQ φ hφ q - 1 := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    show htQ φ hφ (rmul φ hφ (cosetOf (ofE φ hφ) g)) = htQ φ hφ (cosetOf (ofE φ hφ) g) - 1
    rw [rmul_mk, htQ_mk, htQ_mk, map_mul, ht_sE, toAdd_mul, toAdd_ofAdd]
    ring

/-- (5.3), first part: `1 - T_M` is injective. -/
theorem oneSubTM_injective (x : (ascHNN φ hφ ⧸ (ofE φ hφ).range) →₀ ℤ)
    (h : x - TM φ hφ x = 0) : x = 0 := by
  classical
  by_contra hx
  have hne : x.support.Nonempty := Finsupp.support_nonempty_iff.2 hx
  obtain ⟨q0, hq0, hmax⟩ := x.support.exists_max_image (htQ φ hφ) hne
  have hT : TM φ hφ x q0 = 0 := by
    rw [← Finsupp.notMem_support_iff]
    intro hmem
    have := Finsupp.mapDomain_support hmem
    obtain ⟨q', hq', hq'eq⟩ := Finset.mem_image.1 this
    have h1 := hmax q' hq'
    rw [← hq'eq, htQ_rmul] at h1
    omega
  have := congrArg (fun y => y q0) h
  simp only [Finsupp.coe_sub, Pi.sub_apply, hT, sub_zero, Finsupp.coe_zero, Pi.zero_apply] at this
  exact (Finsupp.mem_support_iff.1 hq0) this

/-- The range of `1 - T_M`. -/
noncomputable def rangeOneSubTM : AddSubgroup ((ascHNN φ hφ ⧸ (ofE φ hφ).range) →₀ ℤ) :=
  (AddMonoidHom.id _ - TM φ hφ).range

theorem single_mul_sub_mem (g g' : ascHNN φ hφ) :
    Finsupp.single (cosetOf (ofE φ hφ) (g' * g)) (1 : ℤ) -
      Finsupp.single (cosetOf (ofE φ hφ) g') 1 ∈ rangeOneSubTM φ hφ := by
  induction g using HNNExtension.induction_on generalizing g' with
  | of b =>
    rw [cosetOf_mul_ι, sub_self]; exact zero_mem _
  | t =>
    refine ⟨Finsupp.single (cosetOf (ofE φ hφ) (g' * HNNExtension.t)) 1, ?_⟩
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.id_apply, TM_single, rmul_mk]
    congr 3
    simp [sE]
  | mul x y hx hy =>
    have := add_mem (hy (g' * x)) (hx g')
    rw [← mul_assoc]
    convert this using 1
    abel
  | inv x hx =>
    have := neg_mem (hx (g' * x⁻¹))
    rw [inv_mul_cancel_right] at this
    convert this using 1
    abel

theorem sub_augM_mem (x : (ascHNN φ hφ ⧸ (ofE φ hφ).range) →₀ ℤ) :
    x - augM (ofE φ hφ) x • Finsupp.single (cosetOf (ofE φ hφ) 1) 1 ∈ rangeOneSubTM φ hφ := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    have := add_mem hf hg
    rw [map_add, add_smul]
    convert this using 1
    abel
  | single q n =>
    rw [augM_single]
    have h := single_mul_sub_mem φ hφ q.out 1
    rw [one_mul, show cosetOf (ofE φ hφ) q.out = q from cosetOf_out _ q] at h
    have := zsmul_mem h n
    rw [smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one] at this
    exact this

/-- (5.3), second part: the kernel of the augmentation is the image of `1 - T_M`. -/
theorem exists_oneSubTM (x : (ascHNN φ hφ ⧸ (ofE φ hφ).range) →₀ ℤ) (hx : augM (ofE φ hφ) x = 0) :
    ∃ y, y - TM φ hφ y = x := by
  have := sub_augM_mem φ hφ x
  rw [hx, zero_smul, sub_zero] at this
  obtain ⟨y, hy⟩ := this
  exact ⟨y, hy⟩

theorem augM_TM (x : (ascHNN φ hφ ⧸ (ofE φ hφ).range) →₀ ℤ) :
    augM (ofE φ hφ) (TM φ hφ x) = augM (ofE φ hφ) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | single q n => rw [TM_single, augM_single, augM_single]

/-! ### Interaction with `ℤ[E]` -/

theorem ρ_mul_sE (l : ZG B) :
    ρ (ofE φ hφ) l * MonoidAlgebra.single (sE φ hφ) (1 : ℤ) =
      MonoidAlgebra.single (sE φ hφ) (1 : ℤ) * ρ (ofE φ hφ) (hat φ l) := by
  induction l using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, add_mul, ha, hb, map_add, map_add, mul_add]
  | single b n =>
    simp only [ρ_single, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
      MonoidAlgebra.single_mul_single, of_mul_sE, mul_one, one_mul]

theorem πM_mul_sE_mul (f : ZG (ascHNN φ hφ)) (l : ZG B) :
    πM (ofE φ hφ) (f * MonoidAlgebra.single (sE φ hφ) (1 : ℤ) * ρ (ofE φ hφ) l) =
      augZG l • TM φ hφ (πM (ofE φ hφ) f) := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [add_mul, add_mul, map_add, ha, hb, map_add, map_add, smul_add]
  | single e n =>
    induction l using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, mul_add, map_add, ha, hb, map_add, add_smul]
    | single b m =>
      simp only [ρ_single, MonoidAlgebra.single_mul_single, πM_single, TM_single, rmul_mk,
        cosetOf_mul_ι, augZG_single, mul_one, Finsupp.smul_single, smul_eq_mul]
      rw [mul_comm]

end TheoremA
