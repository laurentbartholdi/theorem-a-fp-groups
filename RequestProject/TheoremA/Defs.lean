module

public import RequestProject.TripleSystem

/-!
# Definitions for Theorem A

* `TheoremA.IsFP n G` — the group `G` has type `FP_n` over `ℤ`: there is an exact sequence
  `P_n → ⋯ → P_1 → P_0 → ℤ → 0` of left `ℤ[G]`-modules with every `P_i` free of finite rank
  (the manuscript, §1, notes that free resolutions of finite rank may be used).
* `TheoremA.ascHNN φ hφ` — the ascending HNN extension of `B` along an injective endomorphism `φ`
  (eq. (5.1)); Mathlib's convention is `t * b * t⁻¹ = φ b`, i.e. `t⁻¹` plays the role of the
  manuscript's stable letter.
* `TheoremA.diagramGroup r T G` — the group `K_Σ(G)` of eq. (3.1), with canonical maps
  `TheoremA.diagramGroup.ι`.
* `TheoremA.DiagramRelations r T α` — endomorphisms `α_v` satisfy the commuting-product relations
  of `Σ`: for every triple `(i, j) ⟶ k`, the images of `α_i` and `α_j` commute and
  `α_k(b) = α_i(b) α_j(b)`.
-/

open scoped commutatorElement

@[expose] public section

namespace TheoremA

open TripleSystem

universe u

/-- The free left `ℤ[G]`-module of rank `k`. -/
abbrev FreeMod (G : Type*) [Group G] (k : ℕ) := Fin k → MonoidAlgebra ℤ G

/-- **Type `FP_n` over `ℤ`.**  There are ranks `c i`, `ℤ[G]`-linear maps
`d i : ℤ[G]^{c (i+1)} → ℤ[G]^{c i}` and an augmentation `ε : ℤ[G]^{c 0} → ℤ` (additive and
`G`-invariant, i.e. `ℤ[G]`-linear to the trivial module `ℤ`) such that
`ℤ[G]^{c n} → ⋯ → ℤ[G]^{c 0} → ℤ → 0` is exact. -/
def IsFP (n : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ (c : ℕ → ℕ)
    (d : ∀ i, FreeMod G (c (i + 1)) →ₗ[MonoidAlgebra ℤ G] FreeMod G (c i))
    (ε : FreeMod G (c 0) →+ ℤ),
    (∀ (g : G) (x : FreeMod G (c 0)), ε (MonoidAlgebra.of ℤ G g • x) = ε x) ∧
    Function.Surjective ε ∧
    (0 < n → ε.ker = (LinearMap.range (d 0)).toAddSubgroup) ∧
    (∀ i, i + 1 < n → LinearMap.ker (d i) = LinearMap.range (d (i + 1)))

/-- The ascending HNN extension `⟨B, t | t b t⁻¹ = φ(b)⟩` of `B` along an injective
endomorphism `φ` (eq. (5.1), up to replacing `t` by `t⁻¹`). -/
abbrev ascHNN {B : Type*} [Group B] (φ : B →* B) (hφ : Function.Injective φ) : Type _ :=
  HNNExtension B ⊤ φ.range (Subgroup.topEquiv.trans (MonoidHom.ofInjective hφ))

/-- The canonical embedding of the base into the ascending HNN extension (Britton's lemma). -/
theorem ascHNN_of_injective {B : Type*} [Group B] (φ : B →* B) (hφ : Function.Injective φ) :
    Function.Injective (HNNExtension.of : B →* ascHNN φ hφ) :=
  HNNExtension.of_injective _

/-- The inclusion of the `v`-th labelled copy `G_v` into the free product `∗_{v < r} G_v`. -/
def ofIdx (r : ℕ) (G : Type*) [Group G] (v : Fin r) : G →* Monoid.CoprodI fun _ : Fin r => G :=
  Monoid.CoprodI.of (M := fun _ : Fin r => G) (i := v)

/-- The relators `ℛ_Σ(G)` of eq. (3.1), inside the free product of `r` labelled copies of `G`:
for every triple `(i, j) ⟶ k` and `g, h ∈ G`, the commutator `[g_i, h_j]` and `g_k⁻¹ g_i g_j`. -/
def relators (r : ℕ) (T : List Triple) (G : Type*) [Group G] :
    Set (Monoid.CoprodI fun _ : Fin r => G) :=
  {x | ∃ t ∈ T, ∃ (hi : t.1 < r) (hj : t.2.1 < r) (hk : t.2.2 < r),
    (∃ g h : G, x = ⁅ofIdx r G ⟨t.1, hi⟩ g, ofIdx r G ⟨t.2.1, hj⟩ h⁆) ∨
    (∃ g : G, x = (ofIdx r G ⟨t.2.2, hk⟩ g)⁻¹ * ofIdx r G ⟨t.1, hi⟩ g * ofIdx r G ⟨t.2.1, hj⟩ g)}

/-- The group `K_Σ(G) = (∗_{v ∈ V} G_v) / ⟪ℛ_Σ(G)⟫` of eq. (3.1). -/
abbrev diagramGroup (r : ℕ) (T : List Triple) (G : Type*) [Group G] : Type _ :=
  (Monoid.CoprodI fun _ : Fin r => G) ⧸ Subgroup.normalClosure (relators r T G)

/-- The canonical homomorphisms `ι_v : G → K_Σ(G)`. -/
def diagramGroup.ι (r : ℕ) (T : List Triple) (G : Type*) [Group G] (v : Fin r) :
    G →* diagramGroup r T G :=
  (QuotientGroup.mk' _).comp (ofIdx r G v)

/-- Endomorphisms `α_v` (`v < r`) of `B` satisfy the commuting-product relations of `Σ`. -/
def DiagramRelations (r : ℕ) (T : List Triple) {B : Type*} [Group B] (α : Fin r → B →* B) :
    Prop :=
  ∀ t ∈ T, ∀ (hi : t.1 < r) (hj : t.2.1 < r) (hk : t.2.2 < r),
    (∀ b c : B, Commute (α ⟨t.1, hi⟩ b) (α ⟨t.2.1, hj⟩ c)) ∧
    (∀ b : B, α ⟨t.2.2, hk⟩ b = α ⟨t.1, hi⟩ b * α ⟨t.2.1, hj⟩ b)

end TheoremA
