module

public import RequestProject.TheoremA.Kernel.CodeGroup
public import RequestProject.TheoremA.Leary.Package

/-!
# From benignness of `V_(S_N)` to benignness of `N`

For a normal subgroup `N ≤ F(a, b)` let `S_N = {code w | eval w ∈ N} ⊆ ℤ` (`codeSet N`).  Inside
`F_big`:

    Y = V_(S_N) ⊔ A,        A = ⟨a, b, h⟩,
    H = G_code ⊓ Y,
    D = H ⊔ C,              C = ⟨c₀, d, e, c₁, …, c₄, h⟩.

`comap_D_eq` proves `D ∩ F(a, b) = N` (for an arbitrary normal `N`, no enumerability used):
* `⊇`: for `n ∈ N` choose a raw word `w` with `eval w = n`; then `g_w ∈ H` and
  `n = g_w v_(code w)⁻¹ h⁻¹`;
* `⊆`: every element of `H` is a product of `g_w^{±1}` with `eval w ∈ N` (projection to `F_c` and
  freeness of the `v_s`, `mem_closure_of_vhom_mem_VS`), so the homomorphism
  `F_big → F(a, b)/N` killing `h` and `F_c` kills `D`.

`hb_of_codeSet` then combines, with the same oracle `R`:
`hb_VS_of_separation` (the only use of `FlagSeparation`), `HB.transfer` to `F_big`,
the **first** `HB.sup_fg` (with `A`), `HB.inf` with `hb_Gcode`, the **second** `HB.sup_fg`
(with `C`), and `HB.comap` along `F(a, b) → F_big`.  No join of two arbitrary benign subgroups
is used.
-/

@[expose] public section

namespace TheoremA.Kernel

open TheoremA.RelPres TheoremA.Coding TheoremA.Leary

/-- `S_N = {code w | eval w ∈ N}`. -/
def codeSet (N : Subgroup (FreeGroup (Fin 2))) : Set ℤ :=
  {z | ∃ w : RawWord (Fin 2), w.eval ∈ N ∧ (code w : ℤ) = z}

theorem zero_mem_codeSet (N : Subgroup (FreeGroup (Fin 2))) : (0 : ℤ) ∈ codeSet N :=
  ⟨[], N.one_mem, rfl⟩

theorem eval_mem_of_code_mem {N : Subgroup (FreeGroup (Fin 2))} {w : RawWord (Fin 2)}
    (h : (code w : ℤ) ∈ codeSet N) : w.eval ∈ N := by
  obtain ⟨w', hw', he⟩ := h
  rwa [code_injective (by exact_mod_cast he : code w' = code w)] at hw'

/-- `A = ⟨a, b, h⟩`. -/
def subA : Subgroup FB := Subgroup.closure {aB, bB, hB}

/-- `C = ⟨c₀, d, e, c₁, …, c₄, h⟩`. -/
def subC : Subgroup FB :=
  Subgroup.closure (insert hB (Set.range fun x : Fin 3 ⊕ Fin 4 => iC (FreeGroup.of x)))

/-- `Y = V_S ⊔ A` (with `V_S` transported to `F_big`). -/
def subY (S : Set ℤ) : Subgroup FB := (VS 4 S).map iC ⊔ subA

/-- `D = (G_code ⊓ Y) ⊔ C`. -/
def subD (S : Set ℤ) : Subgroup FB := (Gcode ⊓ subY S) ⊔ subC

theorem fg_subA : subA.FG := by
  classical exact ⟨{aB, bB, hB}, by simp [subA]⟩

theorem fg_subC : subC.FG := by
  classical
  exact ⟨insert hB (Finset.univ.image fun x : Fin 3 ⊕ Fin 4 => iC (FreeGroup.of x)),
    by simp [subC]⟩

theorem iAB_mem_subA (x : FreeGroup (Fin 2)) : iAB x ∈ subA := by
  have : iAB.range ≤ subA := by
    rw [MonoidHom.range_eq_map, ← FreeGroup.closure_range_of, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · exact Subgroup.subset_closure (by simp [aB, iAB])
    · exact Subgroup.subset_closure (by simp [bB, iAB])
  exact this ⟨x, rfl⟩

theorem hB_mem_subA : hB ∈ subA := Subgroup.subset_closure (by simp)

theorem iC_mem_subC (x : Fc 4) : iC x ∈ subC := by
  have : iC.range ≤ subC := by
    rw [MonoidHom.range_eq_map, ← FreeGroup.closure_range_of, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨y, rfl⟩)
  exact this ⟨x, rfl⟩

theorem hB_mem_subC : hB ∈ subC := Subgroup.subset_closure (Set.mem_insert _ _)

theorem map_pC_subY_le (S : Set ℤ) : (subY S).map pC ≤ VS 4 S := by
  rw [subY, Subgroup.map_sup, sup_le_iff]
  constructor
  · rw [Subgroup.map_map, pC_comp_iC, Subgroup.map_id]
  · rw [subA, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · rw [show aB = iAB (FreeGroup.of 0) from rfl, pC_iAB]; exact Subgroup.one_mem _
    · rw [show bB = iAB (FreeGroup.of 1) from rfl, pC_iAB]; exact Subgroup.one_mem _
    · rw [pC_hB]; exact Subgroup.one_mem _

/-- The homomorphism `F_big → F(a, b)/N` killing `h` and `F_c`. -/
def piN (N : Subgroup (FreeGroup (Fin 2))) [N.Normal] : FB →* FreeGroup (Fin 2) ⧸ N :=
  (QuotientGroup.mk' N).comp pAB

/-- **Elements of `G_code ⊓ Y` only involve selected codes.** -/
theorem mem_closure_of_mem_inf (S : Set ℤ) {u : FreeGroup (RawWord (Fin 2))}
    (hu : gammaC u ∈ subY S) :
    u ∈ Subgroup.closure (FreeGroup.of '' {w | (code w : ℤ) ∈ S}) := by
  have h1 : pC (gammaC u) ∈ VS 4 S := map_pC_subY_le S ⟨_, hu, rfl⟩
  rw [← MonoidHom.comp_apply, pC_comp_gammaC, MonoidHom.comp_apply] at h1
  exact mem_closure_of_codeMap_mem (mem_closure_of_vhom_mem_VS h1)

/-- **`D ∩ F(a, b) = N`.** -/
theorem comap_D_eq (N : Subgroup (FreeGroup (Fin 2))) [N.Normal] :
    (subD (codeSet N)).comap iAB = N := by
  apply le_antisymm
  · intro y hy
    have hker : subD (codeSet N) ≤ (piN N).ker := by
      refine sup_le ?_ ?_
      · rintro x ⟨hxG, hxY⟩
        rw [← range_gammaC] at hxG
        obtain ⟨u, rfl⟩ := hxG
        have hu := mem_closure_of_mem_inf _ hxY
        have : Subgroup.closure (FreeGroup.of '' {w | (code w : ℤ) ∈ codeSet N}) ≤
            ((piN N).comp gammaC).ker := by
          rw [Subgroup.closure_le]
          rintro _ ⟨w, hw, rfl⟩
          rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
          have e1 : gammaC (FreeGroup.of w) = gw w := FreeGroup.lift_apply_of
          have e2 : pAB (gw w) = w.eval := by
            rw [gw, map_mul, map_mul, pAB_iAB, pAB_hB, pAB_iC, mul_one, mul_one]
          rw [e1, piN, MonoidHom.comp_apply, e2]
          exact (QuotientGroup.eq_one_iff _).2 (eval_mem_of_code_mem hw)
        exact this hu
      · rw [subC, Subgroup.closure_le]
        rintro _ hx
        rcases hx with rfl | ⟨x, rfl⟩
        · simp [piN, pAB_hB]
        · simp [piN, pAB_iC]
    have h := hker hy
    simp only [MonoidHom.mem_ker, piN, MonoidHom.comp_apply, pAB_iAB] at h
    exact (QuotientGroup.eq_one_iff _).1 h
  · intro n hn
    obtain ⟨w, rfl⟩ := RawWord.eval_surjective n
    have hc : (code w : ℤ) ∈ codeSet N := ⟨w, hn, rfl⟩
    have hv : iC (vv (code w : ℤ)) ∈ (VS 4 (codeSet N)).map iC :=
      ⟨_, Subgroup.subset_closure ⟨_, hc, rfl⟩, rfl⟩
    have hg : gw w ∈ Gcode ⊓ subY (codeSet N) := by
      refine ⟨Subgroup.subset_closure ⟨w, rfl⟩, ?_⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (iAB_mem_subA _))
        (Subgroup.mem_sup_right hB_mem_subA)) (Subgroup.mem_sup_left hv)
    have he : iAB w.eval = gw w * (iC (vv (code w : ℤ)))⁻¹ * hB⁻¹ := by
      simp only [gw]; group
    show iAB w.eval ∈ subD (codeSet N)
    rw [he]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hg)
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ (iC_mem_subC _))))
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ hB_mem_subC))

/-- **Benignness of `N` from separation and enumerability of `S_N`** (same oracle `R`). -/
theorem hb_of_codeSet (hSep : FlagSeparation) {R : Set ℕ} (N : Subgroup (FreeGroup (Fin 2)))
    [N.Normal] (hS : IntEnumerable R (codeSet N)) : HB R N := by
  have hV := hb_VS_of_separation hSep hS (zero_mem_codeSet N)
  have hsuit : EmbedsSuitable R FB := ⟨FB, inferInstance, (classCR_isFP_two_FB (R := R)).1,
    (classCR_isFP_two_FB (R := R)).2, MonoidHom.id _, Function.injective_id⟩
  have hV' := HB.transfer fg_Fc hV iC iC_injective hsuit
  have hY : HB R (subY (codeSet N)) := HB.sup_fg fg_FB hV' fg_subA
  have hH := (hb_Gcode R).inf hY
  have hD : HB R (subD (codeSet N)) := HB.sup_fg fg_FB hH fg_subC
  have := hD.comap iAB iAB_injective
  rwa [comap_D_eq] at this

end TheoremA.Kernel
