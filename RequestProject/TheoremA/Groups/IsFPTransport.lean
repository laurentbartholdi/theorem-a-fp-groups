module

public import RequestProject.TheoremA.Defs

/-!
# Transport of `IsFP` along group isomorphisms

For a group isomorphism `e : G ≃* H`, the coefficient ring isomorphism
`ℤ[G] ≃ ℤ[H]` (Mathlib's `MonoidAlgebra.domCongr`) acts coordinatewise on the free modules
`ℤ[G]^c → ℤ[H]^c`.  Conjugating a partial free resolution by these maps gives a partial free
resolution over `ℤ[H]` of the same length.  Hence `IsFP n G ↔ IsFP n H` for every `n`.
-/

@[expose] public section

namespace TheoremA

variable {G H : Type*} [Group G] [Group H]

/-- The coefficient ring isomorphism `ℤ[G] ≃ ℤ[H]` induced by `e`. -/
noncomputable abbrev coeffEquiv (e : G ≃* H) : MonoidAlgebra ℤ G ≃ₐ[ℤ] MonoidAlgebra ℤ H :=
  MonoidAlgebra.domCongr ℤ ℤ e

theorem coeffEquiv_of (e : G ≃* H) (g : G) :
    coeffEquiv e (MonoidAlgebra.of ℤ G g) = MonoidAlgebra.of ℤ H (e g) := by
  simp [coeffEquiv, MonoidAlgebra.of_apply, MonoidAlgebra.domCongr_single]

theorem coeffEquiv_symm (e : G ≃* H) (a : MonoidAlgebra ℤ H) :
    (coeffEquiv e).symm a = coeffEquiv e.symm a := by
  simp only [coeffEquiv]
  rfl

/-- Coordinatewise transport of free modules. -/
noncomputable def freeTransport (e : G ≃* H) (c : ℕ) : FreeMod G c ≃+ FreeMod H c where
  toFun v i := coeffEquiv e (v i)
  invFun w i := (coeffEquiv e).symm (w i)
  left_inv v := by funext i; exact (coeffEquiv e).symm_apply_apply _
  right_inv w := by funext i; exact (coeffEquiv e).apply_symm_apply _
  map_add' v w := by funext i; simp

theorem freeTransport_smul (e : G ≃* H) {c : ℕ} (a : MonoidAlgebra ℤ G) (v : FreeMod G c) :
    freeTransport e c (a • v) = coeffEquiv e a • freeTransport e c v := by
  funext i
  simp [freeTransport]

theorem freeTransport_symm_smul (e : G ≃* H) {c : ℕ} (a : MonoidAlgebra ℤ H) (w : FreeMod H c) :
    (freeTransport e c).symm (a • w) = (coeffEquiv e).symm a • (freeTransport e c).symm w := by
  funext i
  simp [freeTransport]

/-- Conjugate a `ℤ[G]`-linear map between free modules to a `ℤ[H]`-linear one. -/
noncomputable def transportLin (e : G ≃* H) {c c' : ℕ}
    (d : FreeMod G c →ₗ[MonoidAlgebra ℤ G] FreeMod G c') :
    FreeMod H c →ₗ[MonoidAlgebra ℤ H] FreeMod H c' where
  toFun w := freeTransport e c' (d ((freeTransport e c).symm w))
  map_add' w w' := by simp
  map_smul' a w := by
    simp only [freeTransport_symm_smul, map_smul, freeTransport_smul, RingHom.id_apply,
      AlgEquiv.apply_symm_apply]

theorem transportLin_apply (e : G ≃* H) {c c' : ℕ}
    (d : FreeMod G c →ₗ[MonoidAlgebra ℤ G] FreeMod G c') (w : FreeMod H c) :
    transportLin e d w = freeTransport e c' (d ((freeTransport e c).symm w)) := rfl

theorem mem_ker_transportLin (e : G ≃* H) {c c' : ℕ}
    (d : FreeMod G c →ₗ[MonoidAlgebra ℤ G] FreeMod G c') (w : FreeMod H c) :
    w ∈ LinearMap.ker (transportLin e d) ↔
      (freeTransport e c).symm w ∈ LinearMap.ker d := by
  simp only [LinearMap.mem_ker, transportLin_apply]
  constructor
  · intro h
    have := congrArg (freeTransport e c').symm h
    simpa using this
  · intro h; rw [h]; simp

theorem mem_range_transportLin (e : G ≃* H) {c c' : ℕ}
    (d : FreeMod G c →ₗ[MonoidAlgebra ℤ G] FreeMod G c') (w : FreeMod H c') :
    w ∈ LinearMap.range (transportLin e d) ↔
      (freeTransport e c').symm w ∈ LinearMap.range d := by
  simp only [LinearMap.mem_range, transportLin_apply]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(freeTransport e c).symm y, by simp⟩
  · rintro ⟨y, hy⟩
    refine ⟨freeTransport e c y, ?_⟩
    simp [hy]

/-- **Transport of `IsFP` along a group isomorphism.** -/
theorem IsFP.of_mulEquiv {n : ℕ} (e : G ≃* H) (h : IsFP n G) : IsFP n H := by
  obtain ⟨c, d, ε, hinv, hsurj, h0, hex⟩ := h
  refine ⟨c, fun i => transportLin e (d i), ε.comp (freeTransport e (c 0)).symm.toAddMonoidHom,
    ?_, ?_, ?_, ?_⟩
  · intro g x
    simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply]
    rw [freeTransport_symm_smul, coeffEquiv_symm, coeffEquiv_of]
    exact hinv _ _
  · intro z
    obtain ⟨x, rfl⟩ := hsurj z
    exact ⟨freeTransport e (c 0) x, by simp⟩
  · intro hn
    ext w
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
      Function.comp_apply, Submodule.mem_toAddSubgroup, mem_range_transportLin]
    have := congrArg (fun A : AddSubgroup (FreeMod G (c 0)) =>
      (freeTransport e (c 0)).symm w ∈ A) (h0 hn)
    simpa using this
  · intro i hi
    ext w
    rw [mem_ker_transportLin, mem_range_transportLin, hex i hi]

theorem IsFP.congr {n : ℕ} (e : G ≃* H) : IsFP n G ↔ IsFP n H :=
  ⟨IsFP.of_mulEquiv e, IsFP.of_mulEquiv e.symm⟩

end TheoremA
