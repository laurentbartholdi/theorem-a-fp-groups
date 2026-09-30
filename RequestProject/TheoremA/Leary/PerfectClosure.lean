module

public import RequestProject.TheoremA.FP2.PerfectQuotient

/-!
# Normal closures of images of perfect groups are perfect

* `normalClosure_ranges_perfect` — if `A i` are perfect groups (indexed by an arbitrary type) and
  `f i : A i →* P` are arbitrary homomorphisms, then `N = ⟨⟨⋃ i, range (f i)⟩⟩` satisfies
  `N ≤ ⁅N, N⁆` (perfection, not the weaker `N ≤ ⁅⊤, N⁆`).
* `normalClosure_ranges_perfect'` — one perfect group and a family of maps indexed by a set.
* `isFP_two_quotient_normalClosure_ranges` — the `FP₂` corollary, via the already proved
  `isFP_two_quotient_of_perfect`.

No finite generation or injectivity is assumed.
-/

open scoped commutatorElement

@[expose] public section

namespace TheoremA.Leary

open Subgroup

/-- A group is perfect: `⊤ ≤ ⁅⊤, ⊤⁆`. -/
def IsPerfectGroup (A : Type*) [Group A] : Prop := (⊤ : Subgroup A) ≤ ⁅(⊤ : Subgroup A), ⊤⁆

/-- The image of a perfect group lies in the commutator subgroup of any subgroup containing it. -/
theorem range_le_commutator_of_perfect {A P : Type*} [Group A] [Group P] (hA : IsPerfectGroup A)
    (f : A →* P) {N : Subgroup P} (hN : f.range ≤ N) : f.range ≤ ⁅N, N⁆ := by
  rw [MonoidHom.range_eq_map]
  calc Subgroup.map f (⊤ : Subgroup A) ≤ Subgroup.map f ⁅(⊤ : Subgroup A), ⊤⁆ :=
        Subgroup.map_mono hA
    _ = ⁅Subgroup.map f (⊤ : Subgroup A), Subgroup.map f (⊤ : Subgroup A)⁆ :=
        Subgroup.map_commutator _ _ _
    _ ≤ ⁅N, N⁆ := by
      rw [← MonoidHom.range_eq_map]
      exact Subgroup.commutator_mono hN hN

/-- **Perfection of normal closures of perfect images.** -/
theorem normalClosure_ranges_perfect {P : Type*} [Group P] {ι : Type*} {A : ι → Type*}
    [∀ i, Group (A i)] (hA : ∀ i, IsPerfectGroup (A i)) (f : ∀ i, A i →* P) :
    normalClosure (⋃ i, Set.range (f i)) ≤
      ⁅normalClosure (⋃ i, Set.range (f i)), normalClosure (⋃ i, Set.range (f i))⁆ := by
  set N := normalClosure (⋃ i, Set.range (f i))
  haveI : N.Normal := normalClosure_normal
  haveI : (⁅N, N⁆).Normal := Subgroup.commutator_normal N N
  apply normalClosure_le_normal
  refine Set.iUnion_subset fun i => ?_
  have hle : (f i).range ≤ N := by
    rintro _ ⟨a, rfl⟩
    exact subset_normalClosure (Set.mem_iUnion.2 ⟨i, a, rfl⟩)
  intro x hx
  exact range_le_commutator_of_perfect (hA i) (f i) hle hx

/-- One perfect group `A` and maps `f s` for `s` in a set `S`. -/
theorem normalClosure_ranges_perfect' {P A : Type*} [Group P] [Group A] (hA : IsPerfectGroup A)
    {σ : Type*} (S : Set σ) (f : σ → A →* P) :
    normalClosure (⋃ s ∈ S, Set.range (f s)) ≤
      ⁅normalClosure (⋃ s ∈ S, Set.range (f s)), normalClosure (⋃ s ∈ S, Set.range (f s))⁆ := by
  have h := normalClosure_ranges_perfect (A := fun _ : S => A) (fun _ => hA)
    (fun s : S => f s.1)
  have hset : (⋃ s ∈ S, Set.range (f s)) = ⋃ s : S, Set.range (f s.1) := by
    ext x; simp
  rw [hset]; exact h

/-- **`FP₂` corollary.** Quotienting an `FP₂` group by the normal closure of images of perfect
groups preserves `FP₂`. -/
theorem isFP_two_quotient_normalClosure_ranges {P : Type*} [Group P] (hP : IsFP 2 P) {ι : Type*}
    {A : ι → Type*} [∀ i, Group (A i)] (hA : ∀ i, IsPerfectGroup (A i)) (f : ∀ i, A i →* P) :
    IsFP 2 (P ⧸ normalClosure (⋃ i, Set.range (f i))) :=
  isFP_two_quotient_of_perfect hP _ (normalClosure_ranges_perfect hA f)

end TheoremA.Leary
