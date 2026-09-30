module

public import RequestProject.TheoremA.Reduction

/-!
# Setup for §§4–5: finite free partial resolutions and chain lifts

For a group `B` and `m = k + 1`, a `Res B k` is a finite free partial resolution (4.1)
`F_m → ⋯ → F_0 → ℤ → 0` of `ℤ` over `Λ = ℤ[B]`, in coordinates `F_i = Λ^{c i}`.  Its top
syzygy is `S = ker (d_m : F_m → F_{m-1})` (`Res.S`).

A *chain lift* of an endomorphism `θ` of `B` (`IsChainLift`) is a family of additive maps
`Φ_i : F_i → F_i` which are `θ`-semilinear, commute with the differentials through degree `m`, and
induce the identity on `ℤ`.

We split Corollary 5.2 into
* `Cor43` — Corollary 4.3: some chain lift of `α_0` maps `S` into a finitely generated submodule;
* `Prop51` — Proposition 5.1: such a lift makes the ascending HNN extension `FP_{m+1}`;

and prove `corollary52_of : Cor43 → Prop51 → Corollary52`.
-/

@[expose] public section

namespace TheoremA

open TripleSystem

universe u

/-- The integral group ring `ℤ[B]`. -/
abbrev ZG (B : Type*) [Group B] := MonoidAlgebra ℤ B

/-- The ring endomorphism of `ℤ[B]` induced by a group endomorphism. -/
noncomputable abbrev hat {B : Type*} [Group B] (θ : B →* B) : ZG B →+* ZG B :=
  MonoidAlgebra.mapDomainRingHom ℤ θ

/-- A finite free partial resolution `F_{k+1} → ⋯ → F_0 → ℤ → 0` over `ℤ[B]` (length
`m = k + 1`). -/
structure Res (B : Type u) [Group B] (k : ℕ) where
  /-- ranks -/
  c : ℕ → ℕ
  /-- differentials `d i : F_{i+1} → F_i` -/
  d : ∀ i, FreeMod B (c (i + 1)) →ₗ[ZG B] FreeMod B (c i)
  /-- augmentation -/
  ε : FreeMod B (c 0) →+ ℤ
  ε_inv : ∀ (g : B) (x : FreeMod B (c 0)), ε (MonoidAlgebra.of ℤ B g • x) = ε x
  ε_surj : Function.Surjective ε
  exact0 : ε.ker = (LinearMap.range (d 0)).toAddSubgroup
  exact : ∀ i, i < k → LinearMap.ker (d i) = LinearMap.range (d (i + 1))

namespace Res

variable {B : Type u} [Group B] {k : ℕ}

/-- The top syzygy `S = ker (d_m : F_m → F_{m-1})`, `m = k + 1`. -/
noncomputable def S (R : Res B k) : Submodule (ZG B) (FreeMod B (R.c (k + 1))) := LinearMap.ker (R.d k)

/-- A group of type `FP_{k+1}` has a finite free partial resolution of length `k + 1`. -/
theorem nonempty_of_isFP (h : IsFP (k + 1) B) : Nonempty (Res B k) := by
  obtain ⟨c, d, ε, hinv, hsurj, h0, hex⟩ := h
  exact ⟨⟨c, d, ε, hinv, hsurj, h0 (Nat.succ_pos k), fun i hi => hex i (by omega)⟩⟩

end Res

/-- `Φ` is a chain lift of `θ` on the partial resolution `R` (through degree `k + 1`). -/
structure IsChainLift {B : Type u} [Group B] {k : ℕ} (R : Res B k) (θ : B →* B)
    (Φ : ∀ i, FreeMod B (R.c i) →+ FreeMod B (R.c i)) : Prop where
  semilinear : ∀ i (l : ZG B) (x : FreeMod B (R.c i)), Φ i (l • x) = hat θ l • Φ i x
  comm : ∀ i, i ≤ k → ∀ x, Φ i (R.d i x) = R.d i (Φ (i + 1) x)
  aug : ∀ x, R.ε (Φ 0 x) = R.ε x

/-- **Corollary 4.3** (statement): for endomorphisms satisfying the relations of `Σ`, some chain
lift of `α_0` maps the top syzygy `S` into a finitely generated submodule of `S`. -/
def Cor43 : Prop :=
  ∀ (r : ℕ) (T : List Triple) (a : Fin T.length → ℤ) (hr : 0 < r),
    WellFormed r T → RowIdentity r T a →
    ∀ (k : ℕ), 1 ≤ k → ∀ (B : Type u) [Group B] (R : Res B k) (α : Fin r → B →* B),
      DiagramRelations r T α →
      ∃ Φ, IsChainLift R (α ⟨0, hr⟩) Φ ∧
        ∃ N : Submodule (ZG B) (FreeMod B (R.c (k + 1))), N.FG ∧ N ≤ R.S ∧
          ∀ s ∈ R.S, Φ (k + 1) s ∈ N

/-- **Proposition 5.1** (statement): if a chain lift of an injective `φ` maps `S` into a finitely
generated submodule of `S`, the ascending HNN extension along `φ` has type `FP_{m+1}`. -/
def Prop51 : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (B : Type u) [Group B] (R : Res B k) (φ : B →* B)
    (hφ : Function.Injective φ) (Φ : ∀ i, FreeMod B (R.c i) →+ FreeMod B (R.c i)),
    IsChainLift R φ Φ →
    ∀ N : Submodule (ZG B) (FreeMod B (R.c (k + 1))), N.FG → N ≤ R.S →
      (∀ s ∈ R.S, Φ (k + 1) s ∈ N) → IsFP (k + 2) (ascHNN φ hφ)

/-- Corollary 5.2 is Corollary 4.3 followed by Proposition 5.1. -/
theorem corollary52_of (h43 : Cor43.{u}) (h51 : Prop51.{u}) : Corollary52.{u} := by
  intro r T a hr hw ha m hm B _ hB α hα hinj
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨R⟩ := Res.nonempty_of_isFP hB
  obtain ⟨Φ, hΦ, N, hNfg, hNS, hSN⟩ := h43 r T a hr hw ha k (by omega) B R α hα
  exact h51 k (by omega) B R _ hinj Φ hΦ N hNfg hNS hSN

end TheoremA
