module

public import RequestProject.TheoremA.Homological.Lifts

/-!
# `ℤ[E]` is free as a right `ℤ[B]`-module (coset decomposition)

For an injective homomorphism `ι : B → E`, every element of `ℤ[E]` decomposes uniquely along the
left cosets `E / ι(B)`.  We use this to show that induction `ℤ[E] ⊗_{ℤ[B]} –`, written in
coordinates as `indMap`, preserves exactness (the step "induction is exact" in the proof of
Proposition 5.1).
-/

@[expose] public section

namespace TheoremA

universe u

open MonoidAlgebra

variable {B E : Type u} [Group B] [Group E] (ι : B →* E) (hι : Function.Injective ι)

/-- The ring homomorphism `ℤ[B] → ℤ[E]`. -/
noncomputable def ρ : ZG B →+* ZG E := MonoidAlgebra.mapDomainRingHom ℤ ι

theorem ρ_single (b : B) (n : ℤ) : ρ ι (MonoidAlgebra.single b n) = MonoidAlgebra.single (ι b) n := by
  simp [ρ, MonoidAlgebra.mapDomainRingHom_apply]

/-- The coset of `e`, in the quotient by `ι(B)`. -/
abbrev cosetOf (e : E) : E ⧸ ι.range := (e : E ⧸ ι.range)

theorem out_inv_mul_mem (e : E) : (cosetOf ι e).out⁻¹ * e ∈ ι.range := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ι.range e
  rw [hh, mul_inv_rev, inv_mul_cancel_right]
  exact inv_mem h.2

/-- The element `b_e ∈ B` with `e = out(eB) · ι(b_e)`. -/
noncomputable def bOf (e : E) : B :=
  (MonoidHom.ofInjective hι).symm ⟨_, out_inv_mul_mem ι e⟩

theorem ι_bOf (e : E) : ι (bOf ι hι e) = (cosetOf ι e).out⁻¹ * e := by
  have := (MonoidHom.ofInjective hι).apply_symm_apply ⟨_, out_inv_mul_mem ι e⟩
  exact congrArg Subtype.val this

theorem out_mul_ι_bOf (e : E) : (cosetOf ι e).out * ι (bOf ι hι e) = e := by
  rw [ι_bOf, mul_inv_cancel_left]

theorem cosetOf_mul_ι (e : E) (b : B) : cosetOf ι (e * ι b) = cosetOf ι e := by
  rw [QuotientGroup.eq]
  simp

theorem bOf_mul_ι (e : E) (b : B) : bOf ι hι (e * ι b) = bOf ι hι e * b := by
  apply hι
  rw [map_mul, ι_bOf, ι_bOf, cosetOf_mul_ι, mul_assoc]

theorem bOf_out (q : E ⧸ ι.range) : bOf ι hι q.out = 1 := by
  apply hι
  rw [ι_bOf, map_one]
  have : cosetOf ι q.out = q := Quotient.out_eq' q
  rw [this, inv_mul_cancel]

theorem cosetOf_out (q : E ⧸ ι.range) : cosetOf ι q.out = q := Quotient.out_eq' q

/-- The coset decomposition `ℤ[E] → ⊕_{E / ι B} ℤ[B]`. -/
noncomputable def decomp : ZG E →+ ((E ⧸ ι.range) →₀ ZG B) :=
  (Finsupp.liftAddHom fun e =>
    (Finsupp.singleAddHom (cosetOf ι e)).comp
      (MonoidAlgebra.singleAddHom (bOf ι hι e) : ℤ →+ ZG B)).comp
    MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

theorem decomp_single (e : E) (n : ℤ) :
    decomp ι hι (MonoidAlgebra.single e n) =
      Finsupp.single (cosetOf ι e) (MonoidAlgebra.single (bOf ι hι e) n) := by
  simp [decomp]

/-- Reassembly `⊕_{E / ι B} ℤ[B] → ℤ[E]`, `(q, l) ↦ out(q) · ι(l)`. -/
noncomputable def assemble : ((E ⧸ ι.range) →₀ ZG B) →+ ZG E :=
  Finsupp.liftAddHom fun q =>
    (AddMonoidHom.mulLeft (MonoidAlgebra.single q.out (1 : ℤ))).comp (ρ ι).toAddMonoidHom

theorem assemble_single (q : E ⧸ ι.range) (l : ZG B) :
    assemble ι (Finsupp.single q l) = MonoidAlgebra.single q.out 1 * ρ ι l := by
  simp [assemble]

theorem assemble_decomp (f : ZG E) : assemble ι (decomp ι hι f) = f := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | single e n =>
    rw [decomp_single, assemble_single]
    simp [ρ_single, MonoidAlgebra.single_mul_single, out_mul_ι_bOf]

theorem decomp_mul_ρ (f : ZG E) (l : ZG B) (q : E ⧸ ι.range) :
    decomp ι hι (f * ρ ι l) q = decomp ι hι f q * l := by
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [add_mul, map_add, Finsupp.add_apply, ha, hb, map_add,
      Finsupp.add_apply, add_mul]
  | single e n =>
    induction l using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, mul_add, map_add, Finsupp.add_apply, ha, hb, mul_add]
    | single b m =>
      simp only [ρ_single,
        MonoidAlgebra.single_mul_single, decomp_single, cosetOf_mul_ι, bOf_mul_ι]
      by_cases hq : cosetOf ι e = q
      · subst hq; simp [MonoidAlgebra.single_mul_single]
      · simp [hq]

open scoped Classical in
theorem decomp_out_mul (q q' : E ⧸ ι.range) (l : ZG B) :
    decomp ι hι (MonoidAlgebra.single q'.out 1 * ρ ι l) q = if q' = q then l else 0 := by
  rw [decomp_mul_ρ, decomp_single, bOf_out, cosetOf_out]
  by_cases h : q' = q
  · subst h; simp only [Finsupp.single_eq_same, if_true]; rw [← MonoidAlgebra.one_def, one_mul]
  · simp [h]

end TheoremA
