module

public import RequestProject.TheoremA.Groups.CodingHB
public import RequestProject.TheoremA.Kernel.PowerSubst
public import RequestProject.TheoremA.Kernel.Tower
public import RequestProject.TheoremA.Kernel.RawCode

/-!
# The coding subgroup `G_code` and its benignness

`F_big = F(a, b, h) * F_c` is `FreeGroup (Fin 3 ⊕ (Fin 3 ⊕ Fin 4))`: `inl 0 = a`, `inl 1 = b`,
`inl 2 = h`, and `inr` is the existing `F_c = Fc 4` (`c₀, d, e, c₁, …, c₄`).

* `gw w = eval(w) · h · v_(code w)` for raw words `w` over `a, b`; `Gcode = ⟨g_w⟩`.
* `Ppow` — the power substitution `c_i ↦ c_i^10`, `e ↦ e^10`, `d ↦ d` of `F_c`;
  `phiC δ = ψ_δ ∘ Ppow` sends `v_s ↦ v_(10s+δ)`.
* `phiL λ = τ_λ ∘ Ψ_δ ∘ Pbig` on `F_big`: the injective power substitution, then the shift
  automorphism `ψ_δ` on `F_c`, then the automorphism `h ↦ λ h`.  `phiL_injective`,
  `phiL_gw : phiL λ (g_w) = g_(w ++ [λ])`.
* `Gcode_inf_range_le` — **saturation**: `Gcode ∩ range(phiL λ) ≤ phiL λ (Gcode)`.  Proof by
  projecting to `F_c`: the image of `γ(u) ∈ Gcode` is `vhom(code_*(u))`; lying in
  `range(phiL λ)` forces it into `ψ_δ(range Ppow) ∩ V_ℤ ≤ ψ_δ(V_{10ℤ})` (the twisted/untwisted
  comparison with `J = ℤ/10`), hence every generator of `u` has code `≡ δ (mod 10)`, i.e. ends with
  the letter `λ` (last-digit property).
* `hb_Gcode` — **`Gcode` is `HB_R` in `F_big`** for every oracle `R`, via four ascending HNN
  extensions (`hb_of_saturated`).  No separation hypothesis is used.
-/

@[expose] public section

namespace TheoremA.Kernel

open TheoremA.RelPres TheoremA.Coding

/-! ### The group `F_big` -/

/-- `F_big = F(a, b, h) * F(c₀, d, e, c₁, …, c₄)`. -/
abbrev FB : Type := FreeGroup (Fin 3 ⊕ (Fin 3 ⊕ Fin 4))

/-- `a`. -/
def aB : FB := FreeGroup.of (Sum.inl 0)
/-- `b`. -/
def bB : FB := FreeGroup.of (Sum.inl 1)
/-- `h`. -/
def hB : FB := FreeGroup.of (Sum.inl 2)

/-- `F(a, b) → F_big`. -/
def iAB : FreeGroup (Fin 2) →* FB := FreeGroup.map fun i => Sum.inl (Fin.castSucc i)

/-- `F_c → F_big`. -/
def iC : Fc 4 →* FB := FreeGroup.map Sum.inr

/-- The retraction `F_big → F_c` killing `a, b, h`. -/
def pC : FB →* Fc 4 := FreeGroup.lift (Sum.elim (fun _ => 1) FreeGroup.of)

/-- The retraction `F_big → F(a, b)` killing `h` and `F_c`. -/
def pAB : FB →* FreeGroup (Fin 2) :=
  FreeGroup.lift (Sum.elim (fun i => if h : i.val < 2 then FreeGroup.of ⟨i.val, h⟩ else 1)
    (fun _ => 1))

theorem pC_comp_iC : pC.comp iC = MonoidHom.id (Fc 4) :=
  FreeGroup.ext_hom _ _ fun x => by simp [pC, iC]

theorem pC_iC (x : Fc 4) : pC (iC x) = x := by
  rw [← MonoidHom.comp_apply, pC_comp_iC]; rfl

theorem iC_injective : Function.Injective iC :=
  Function.LeftInverse.injective (g := pC) pC_iC

theorem pAB_comp_iAB : pAB.comp iAB = MonoidHom.id (FreeGroup (Fin 2)) :=
  FreeGroup.ext_hom _ _ fun i => by fin_cases i <;> simp [pAB, iAB]

theorem pAB_iAB (x : FreeGroup (Fin 2)) : pAB (iAB x) = x := by
  rw [← MonoidHom.comp_apply, pAB_comp_iAB]; rfl

theorem iAB_injective : Function.Injective iAB :=
  Function.LeftInverse.injective (g := pAB) pAB_iAB

theorem pC_comp_iAB : pC.comp iAB = 1 :=
  FreeGroup.ext_hom _ _ fun i => by simp [pC, iAB]

theorem pC_iAB (x : FreeGroup (Fin 2)) : pC (iAB x) = 1 := by
  rw [← MonoidHom.comp_apply, pC_comp_iAB]; rfl

theorem pC_hB : pC hB = 1 := by simp [pC, hB]

theorem pAB_comp_iC : pAB.comp iC = 1 :=
  FreeGroup.ext_hom _ _ fun x => by simp [pAB, iC]

theorem pAB_iC (x : Fc 4) : pAB (iC x) = 1 := by
  rw [← MonoidHom.comp_apply, pAB_comp_iC]; rfl

theorem pAB_hB : pAB hB = 1 := by simp [pAB, hB]

theorem classCR_isFP_two_FB {R : Set ℕ} : ClassCR R FB ∧ IsFP 2 FB :=
  classCR_isFP_two_freeGroup' _

theorem fg_FB : Group.FG FB := (classCR_isFP_two_FB (R := ∅)).1.fg

/-! ### The coding elements `g_w` -/

/-- `g_w = eval(w) · h · v_(code w)`. -/
def gw (w : RawWord (Fin 2)) : FB := iAB w.eval * hB * iC (vv (code w : ℤ))

/-- `u ↦ ∏ g_w^{±1}` on the free group on raw words. -/
def gammaC : FreeGroup (RawWord (Fin 2)) →* FB := FreeGroup.lift gw

/-- `G_code = ⟨g_w | w a raw word⟩`. -/
def Gcode : Subgroup FB := Subgroup.closure (Set.range gw)

theorem range_gammaC : gammaC.range = Gcode := FreeGroup.range_lift_eq_closure

/-- Raw words to their codes, on free groups. -/
def codeMap : FreeGroup (RawWord (Fin 2)) →* FreeGroup ℤ := FreeGroup.map fun w => (code w : ℤ)

theorem pC_gw (w : RawWord (Fin 2)) : pC (gw w) = vv (code w : ℤ) := by
  simp [gw, pC_iAB, pC_hB, pC_iC]

theorem pC_comp_gammaC : pC.comp gammaC = (vhom : FreeGroup ℤ →* Fc 4).comp codeMap :=
  FreeGroup.ext_hom _ _ fun w => by simp [gammaC, pC_gw, codeMap, vhom]

open Classical in
/-- A left inverse of `codeMap` (codes are injective). -/
noncomputable def decodeZ : FreeGroup ℤ →* FreeGroup (RawWord (Fin 2)) :=
  FreeGroup.lift fun s =>
    if h : ∃ w : RawWord (Fin 2), (code w : ℤ) = s then FreeGroup.of h.choose else 1

theorem decodeZ_comp_codeMap : decodeZ.comp codeMap = MonoidHom.id _ := by
  refine FreeGroup.ext_hom _ _ fun w => ?_
  have h : ∃ w' : RawWord (Fin 2), (code w' : ℤ) = code w := ⟨w, rfl⟩
  simp only [MonoidHom.comp_apply, codeMap, FreeGroup.map.of, decodeZ, FreeGroup.lift_apply_of,
    dif_pos h, MonoidHom.id_apply]
  congr 1
  exact code_injective (by exact_mod_cast h.choose_spec)

theorem decodeZ_codeMap (u : FreeGroup (RawWord (Fin 2))) : decodeZ (codeMap u) = u := by
  rw [← MonoidHom.comp_apply, decodeZ_comp_codeMap]; rfl

/-- If the codes of `u` lie in `T`, then the generators of `u` have codes in `T`. -/
theorem mem_closure_of_codeMap_mem {T : Set ℤ} {u : FreeGroup (RawWord (Fin 2))}
    (h : codeMap u ∈ Subgroup.closure (FreeGroup.of '' T)) :
    u ∈ Subgroup.closure (FreeGroup.of '' {w | (code w : ℤ) ∈ T}) := by
  rw [← decodeZ_codeMap u]
  have : (Subgroup.closure (FreeGroup.of '' T)).map decodeZ ≤
      Subgroup.closure (FreeGroup.of '' {w | (code w : ℤ) ∈ T}) := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    simp only [decodeZ, FreeGroup.lift_apply_of]
    split_ifs with hw
    · exact Subgroup.subset_closure ⟨hw.choose, by
        simp only [Set.mem_setOf_eq]; rw [hw.choose_spec]; exact hs, rfl⟩
    · exact Subgroup.one_mem _
  exact this ⟨_, h, rfl⟩

theorem VS_eq_map (T : Set ℤ) :
    VS 4 T = (Subgroup.closure (FreeGroup.of '' T)).map (vhom : FreeGroup ℤ →* Fc 4) := by
  rw [MonoidHom.map_closure, VS, Set.image_image]
  simp [vhom]

theorem mem_closure_of_vhom_mem_VS {T : Set ℤ} {u : FreeGroup ℤ}
    (h : (vhom : FreeGroup ℤ →* Fc 4) u ∈ VS 4 T) :
    u ∈ Subgroup.closure (FreeGroup.of '' T) := by
  rw [VS_eq_map] at h
  obtain ⟨u', hu', he⟩ := h
  rwa [vhom_injective (by norm_num) he] at hu'

/-! ### The power substitution `Ppow` on `F_c` -/

/-- Exponents: `c₀ ↦ 10`, `d ↦ 1`, `e ↦ 10`, `c_i ↦ 10`. -/
def kPow : Fin 3 ⊕ Fin 4 → ℕ := Sum.elim ![10, 1, 10] fun _ => 10

theorem kPow_pos (x : Fin 3 ⊕ Fin 4) : 0 < kPow x := by
  rcases x with k | i
  · fin_cases k <;> simp [kPow]
  · simp [kPow]

/-- `c_i ↦ c_i^10`, `e ↦ e^10`, `d ↦ d`. -/
def Ppow : Fc 4 →* Fc 4 := powSubst kPow

theorem Ppow_injective : Function.Injective Ppow := powSubst_injective kPow kPow_pos

theorem Ppow_of (x : Fin 3 ⊕ Fin 4) : Ppow (FreeGroup.of x) = FreeGroup.of x ^ kPow x := by
  simp [Ppow, powSubst]

theorem zpow_pow_ten {G : Type*} [Group G] (g : G) (s : ℤ) : (g ^ 10) ^ s = g ^ (10 * s) := by
  rw [zpow_mul]; norm_cast

theorem Ppow_vv (s : ℤ) : Ppow (vv s) = vv (10 * s) := by
  have hc0 : Ppow (c0 : Fc 4) = c0 ^ 10 := Ppow_of (Sum.inl 0)
  have hdd : Ppow (dd : Fc 4) = dd := by rw [dd, Ppow_of]; simp [kPow]
  have hee : Ppow (ee : Fc 4) = ee ^ 10 := Ppow_of (Sum.inl 2)
  have hcc : ∀ i : Fin 4, Ppow (cc i) = cc i ^ 10 := fun i => Ppow_of (Sum.inr i)
  have hCs : Ppow (Cs s : Fc 4) = Cs (10 * s) := by
    simp only [Cs, map_list_prod, List.map_ofFn, Function.comp_def, map_zpow, hcc, zpow_pow_ten]
  simp only [vv, map_mul, map_zpow, hc0, hdd, hee, hCs, zpow_pow_ten]

/-- `phiC δ = ψ_δ ∘ Ppow`. -/
def phiC (δ : ℤ) : Fc 4 →* Fc 4 := (psi δ).comp Ppow

theorem phiC_vv (δ s : ℤ) : phiC δ (vv s) = vv (10 * s + δ) := by
  simp [phiC, Ppow_vv, psi_vv]

theorem psi_psi_neg (δ : ℤ) (x : Fc 4) : psi (-δ) (psi δ x) = x := by
  rw [← MonoidHom.comp_apply, psi_comp, add_neg_cancel, psi_zero]; rfl

theorem psi_neg_psi' (δ : ℤ) (x : Fc 4) : psi δ (psi (-δ) x) = x := by
  rw [← MonoidHom.comp_apply, psi_comp, neg_add_cancel, psi_zero]; rfl

/-- The shift `s ↦ s + c` on `F(ℤ)`. -/
def shiftZ (c : ℤ) : FreeGroup ℤ →* FreeGroup ℤ := FreeGroup.map fun s => s + c

theorem psi_vhom (c : ℤ) (y : FreeGroup ℤ) :
    psi c ((vhom : FreeGroup ℤ →* Fc 4) y) = vhom (shiftZ c y) := by
  rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply (vhom : FreeGroup ℤ →* Fc 4)]
  congr 1
  exact FreeGroup.ext_hom _ _ fun s => by simp [vhom, shiftZ, psi_vv]

theorem shiftZ_shiftZ (c c' : ℤ) (y : FreeGroup ℤ) : shiftZ c (shiftZ c' y) = shiftZ (c' + c) y := by
  rw [← MonoidHom.comp_apply]
  congr 1
  exact FreeGroup.ext_hom _ _ fun s => by simp [shiftZ, add_assoc]

theorem shiftZ_zero (y : FreeGroup ℤ) : shiftZ 0 y = y := by
  rw [show shiftZ 0 = MonoidHom.id _ from FreeGroup.ext_hom _ _ fun s => by simp [shiftZ]]; rfl

/-! ### `range Ppow ∩ V_ℤ ≤ V_{10ℤ}` -/

/-- `J = ℤ/10`, with `j₁ = 1` and `j₂ = j₃ = j₄ = 0`. -/
def jTen : Fin 4 → Multiplicative (ZMod 10) := fun i => if i = 0 then Multiplicative.ofAdd 1 else 1

theorem Ys_jTen (s : ℤ) : Ys jTen s = Multiplicative.ofAdd (s : ZMod 10) := by
  simp only [Ys, List.prod_ofFn]
  rw [Finset.prod_eq_single (0 : Fin 4)]
  · rw [show jTen 0 = Multiplicative.ofAdd 1 from rfl, ← ofAdd_zsmul, zsmul_one]
  · intro i _ hi; rw [show jTen i = 1 from if_neg hi, one_zpow]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem Ys_jTen_eq_one_iff (s : ℤ) : Ys jTen s = 1 ↔ s ∈ {s : ℤ | 10 ∣ s} := by
  rw [Ys_jTen, Set.mem_setOf_eq, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
  exact_mod_cast ZMod.intCast_zmod_eq_zero_iff_dvd s 10

theorem jTen_pow_ten (i : Fin 4) : jTen i ^ 10 = 1 := by
  unfold jTen; split_ifs <;> decide

theorem kappa_comp_Ppow :
    (kappa (yT jTen)).comp Ppow = (kappa (yU (J := Multiplicative (ZMod 10)))).comp Ppow := by
  refine FreeGroup.ext_hom _ _ fun x => ?_
  simp only [MonoidHom.comp_apply, Ppow_of, map_pow]
  rcases x with k | i
  · simp [kappa]
  · simp only [kappa, FreeGroup.lift_apply_of, Sum.elim_inr, ← map_pow]
    congr 1
    show (FreeGroup.of i, jTen i) ^ 10 = (FreeGroup.of i, (1 : Multiplicative (ZMod 10))) ^ 10
    rw [Prod.pow_mk, Prod.pow_mk, jTen_pow_ten, one_pow]

theorem range_Ppow_inf_VZ_le : Ppow.range ⊓ VZ 4 ≤ VS 4 {s : ℤ | 10 ∣ s} := by
  rintro x ⟨⟨y, rfl⟩, hx⟩
  refine mem_VS_of_kappa_eq (by norm_num) jTen Ys_jTen_eq_one_iff (by simp) hx ?_
  rw [← MonoidHom.comp_apply, kappa_comp_Ppow]; rfl

/-! ### The maps `phiL λ` -/

/-- Exponents on `F_big`: `1` on `a, b, h`, `kPow` on `F_c`. -/
def kBig : Fin 3 ⊕ (Fin 3 ⊕ Fin 4) → ℕ := Sum.elim (fun _ => 1) kPow

theorem kBig_pos (x : Fin 3 ⊕ (Fin 3 ⊕ Fin 4)) : 0 < kBig x := by
  rcases x with k | y
  · simp [kBig]
  · exact kPow_pos y

/-- The injective power substitution on `F_big`. -/
def Pbig : FB →* FB := powSubst kBig

/-- `ψ_δ` on the `F_c` factor, identity on `a, b, h`. -/
def PsiB (δ : ℤ) : FB →* FB :=
  FreeGroup.lift (Sum.elim (fun i => FreeGroup.of (Sum.inl i)) fun x => iC (psi δ (FreeGroup.of x)))

/-- `h ↦ g h` (for a fixed `g ∈ F(a, b)`), identity on `a, b` and `F_c`. -/
def tauB (g : FreeGroup (Fin 2)) : FB →* FB :=
  FreeGroup.lift (Sum.elim (fun i : Fin 3 => ![aB, bB, iAB g * hB] i) fun x => iC (FreeGroup.of x))

theorem PsiB_iC (δ : ℤ) (x : Fc 4) : PsiB δ (iC x) = iC (psi δ x) := by
  rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply iC]
  congr 1
  exact FreeGroup.ext_hom _ _ fun y => by simp [PsiB, iC]

theorem PsiB_iAB (δ : ℤ) (x : FreeGroup (Fin 2)) : PsiB δ (iAB x) = iAB x := by
  rw [← MonoidHom.comp_apply]
  congr 1
  exact FreeGroup.ext_hom _ _ fun i => by simp [PsiB, iAB]

theorem PsiB_hB (δ : ℤ) : PsiB δ hB = hB := by simp [PsiB, hB]

theorem PsiB_neg_PsiB (δ : ℤ) (x : FB) : PsiB (-δ) (PsiB δ x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [show (PsiB (-δ)).comp (PsiB δ) = MonoidHom.id FB from FreeGroup.ext_hom _ _ fun y => by
    rcases y with k | y
    · simp [PsiB]
    · simp only [MonoidHom.comp_apply, PsiB, FreeGroup.lift_apply_of, Sum.elim_inr]
      rw [show (FreeGroup.lift (Sum.elim (fun i => FreeGroup.of (Sum.inl i)) fun x =>
          iC (psi (-δ) (FreeGroup.of x)))) = PsiB (-δ) from rfl, PsiB_iC, psi_psi_neg]
      simp [iC]]
  rfl

theorem tauB_iAB (g : FreeGroup (Fin 2)) (x : FreeGroup (Fin 2)) : tauB g (iAB x) = iAB x := by
  rw [← MonoidHom.comp_apply]
  congr 1
  exact FreeGroup.ext_hom _ _ fun i => by fin_cases i <;> simp [tauB, iAB, aB, bB]

theorem tauB_hB (g : FreeGroup (Fin 2)) : tauB g hB = iAB g * hB := by simp [tauB, hB]

theorem tauB_iC (g : FreeGroup (Fin 2)) (x : Fc 4) : tauB g (iC x) = iC x := by
  rw [← MonoidHom.comp_apply]
  congr 1
  exact FreeGroup.ext_hom _ _ fun y => by simp [tauB, iC]

theorem tauB_inv_tauB (g : FreeGroup (Fin 2)) (x : FB) : tauB g⁻¹ (tauB g x) = x := by
  rw [← MonoidHom.comp_apply]
  rw [show (tauB g⁻¹).comp (tauB g) = MonoidHom.id FB from FreeGroup.ext_hom _ _ fun y => by
    rcases y with k | y
    · fin_cases k
      · simp [tauB, aB]
      · simp [tauB, bB]
      · show tauB g⁻¹ (tauB g hB) = hB
        rw [tauB_hB, map_mul, tauB_iAB,
          tauB_hB, map_inv]
        group
    · simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      rw [show (FreeGroup.of (Sum.inr y) : FB) = iC (FreeGroup.of y) from rfl, tauB_iC, tauB_iC]]
  rfl

theorem Pbig_iAB (x : FreeGroup (Fin 2)) : Pbig (iAB x) = iAB x := by
  rw [← MonoidHom.comp_apply]
  congr 1
  exact FreeGroup.ext_hom _ _ fun i => by simp [Pbig, powSubst, iAB, kBig]

theorem Pbig_hB : Pbig hB = hB := by simp [Pbig, powSubst, hB, kBig]

theorem Pbig_iC (x : Fc 4) : Pbig (iC x) = iC (Ppow x) := by
  rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply iC]
  congr 1
  exact FreeGroup.ext_hom _ _ fun y => by simp [Pbig, Ppow, powSubst, iC, kBig]

/-- **`phiL λ`**: power substitution, then the shift by `δ = digit λ`, then `h ↦ λ h`. -/
def phiL (p : Fin 2 × Bool) : FB →* FB :=
  (tauB (RawWord.eval [p])).comp ((PsiB (digit p : ℤ)).comp Pbig)

theorem phiL_injective (p : Fin 2 × Bool) : Function.Injective (phiL p) := by
  refine (Function.LeftInverse.injective (g := tauB (RawWord.eval [p])⁻¹) (tauB_inv_tauB _)).comp
    ((Function.LeftInverse.injective (g := PsiB (-(digit p : ℤ))) (PsiB_neg_PsiB _)).comp
      (powSubst_injective kBig kBig_pos))

theorem phiL_iAB (p : Fin 2 × Bool) (x : FreeGroup (Fin 2)) : phiL p (iAB x) = iAB x := by
  simp [phiL, Pbig_iAB, PsiB_iAB, tauB_iAB]

theorem phiL_hB (p : Fin 2 × Bool) : phiL p hB = iAB (RawWord.eval [p]) * hB := by
  simp [phiL, Pbig_hB, PsiB_hB, tauB_hB]

theorem phiL_iC (p : Fin 2 × Bool) (x : Fc 4) : phiL p (iC x) = iC (phiC (digit p : ℤ) x) := by
  simp [phiL, Pbig_iC, PsiB_iC, tauB_iC, phiC]

/-- **`phiL λ (g_w) = g_(w ++ [λ])`.** -/
theorem phiL_gw (p : Fin 2 × Bool) (w : RawWord (Fin 2)) : phiL p (gw w) = gw (w ++ [p]) := by
  simp only [gw, map_mul, phiL_iAB, phiL_hB, phiL_iC, phiC_vv, RawWord.eval_append,
    code_append_single]
  push_cast
  group

theorem pC_phiL (p : Fin 2 × Bool) (x : FB) : pC (phiL p x) = phiC (digit p : ℤ) (pC x) := by
  rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply (phiC (digit p : ℤ))]
  congr 1
  refine FreeGroup.ext_hom _ _ fun y => ?_
  rcases y with k | y
  · fin_cases k
    · show pC (phiL p (iAB (FreeGroup.of 0))) = phiC (digit p : ℤ) (pC (iAB (FreeGroup.of 0)))
      rw [phiL_iAB, pC_iAB, map_one]
    · show pC (phiL p (iAB (FreeGroup.of 1))) = phiC (digit p : ℤ) (pC (iAB (FreeGroup.of 1)))
      rw [phiL_iAB, pC_iAB, map_one]
    · show pC (phiL p hB) = phiC (digit p : ℤ) (pC hB)
      rw [phiL_hB, map_mul, pC_iAB, pC_hB, map_one, one_mul]
  · show pC (phiL p (iC (FreeGroup.of y))) = phiC (digit p : ℤ) (pC (iC (FreeGroup.of y)))
    rw [phiL_iC, pC_iC, pC_iC]

theorem gammaC_comp_map (p : Fin 2 × Bool) :
    gammaC.comp (FreeGroup.map fun w : RawWord (Fin 2) => w ++ [p]) = (phiL p).comp gammaC :=
  FreeGroup.ext_hom _ _ fun w => by simp [gammaC, phiL_gw]

/-! ### Invariance and saturation -/

theorem Gcode_map_le (p : Fin 2 × Bool) : Gcode.map (phiL p) ≤ Gcode := by
  rw [Gcode, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  rw [phiL_gw]
  exact Subgroup.subset_closure ⟨_, rfl⟩

/-- **Saturation**: `G_code ∩ range(phiL λ) ≤ phiL λ (G_code)`. -/
theorem Gcode_inf_range_le (p : Fin 2 × Bool) : Gcode ⊓ (phiL p).range ≤ Gcode.map (phiL p) := by
  rintro x ⟨hxG, z, rfl⟩
  rw [← range_gammaC] at hxG
  obtain ⟨u, hu⟩ := hxG
  set δ : ℤ := (digit p : ℤ) with hδ
  have h1 : (vhom : FreeGroup ℤ →* Fc 4) (codeMap u) = psi δ (Ppow (pC z)) := by
    rw [← MonoidHom.comp_apply, ← pC_comp_gammaC, MonoidHom.comp_apply, hu, pC_phiL]; rfl
  have h2 : (vhom : FreeGroup ℤ →* Fc 4) (shiftZ (-δ) (codeMap u)) ∈ Ppow.range := by
    rw [← psi_vhom, h1, psi_psi_neg]; exact ⟨_, rfl⟩
  have h3 : (vhom : FreeGroup ℤ →* Fc 4) (shiftZ (-δ) (codeMap u)) ∈ VZ 4 := by
    rw [← range_vhom]; exact ⟨_, rfl⟩
  have h4 := mem_closure_of_vhom_mem_VS (range_Ppow_inf_VZ_le ⟨h2, h3⟩)
  have h5 : codeMap u ∈ Subgroup.closure (FreeGroup.of '' {s : ℤ | 10 ∣ s - δ}) := by
    have : (Subgroup.closure (FreeGroup.of '' {s : ℤ | 10 ∣ s})).map (shiftZ δ) ≤
        Subgroup.closure (FreeGroup.of '' {s : ℤ | 10 ∣ s - δ}) := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨s + δ, ?_, by simp [shiftZ]⟩
      simpa using hs
    have h := this ⟨_, h4, rfl⟩
    rwa [shiftZ_shiftZ, neg_add_cancel, shiftZ_zero] at h
  have h6 := mem_closure_of_codeMap_mem h5
  have h7 : u ∈ (FreeGroup.map fun w : RawWord (Fin 2) => w ++ [p]).range := by
    rw [show (FreeGroup.map fun w : RawWord (Fin 2) => w ++ [p]) =
      FreeGroup.lift (FreeGroup.of ∘ fun w : RawWord (Fin 2) => w ++ [p]) from
        FreeGroup.ext_hom _ _ fun w => by simp,
      FreeGroup.range_lift_eq_closure]
    refine Subgroup.closure_mono ?_ h6
    rintro _ ⟨w, hw, rfl⟩
    have hw' : code w % 10 = digit p := by
      simp only [Set.mem_setOf_eq] at hw
      have := digit_le p
      omega
    obtain ⟨u', rfl⟩ := (mod_ten_code_eq_digit_iff w p).1 hw'
    exact ⟨u', rfl⟩
  obtain ⟨u₀, rfl⟩ := h7
  refine ⟨gammaC u₀, ?_, ?_⟩
  · rw [← range_gammaC]; exact ⟨u₀, rfl⟩
  · rw [← hu, ← MonoidHom.comp_apply, ← gammaC_comp_map]; rfl

/-! ### Benignness of `G_code` -/

/-- The four letters `a, b, a⁻¹, b⁻¹`. -/
def letters : List (Fin 2 × Bool) := [(0, true), (1, true), (0, false), (1, false)]

theorem mem_letters (p : Fin 2 × Bool) : p ∈ letters := by
  obtain ⟨a, b⟩ := p
  fin_cases a <;> cases b <;> simp [letters]

theorem gw_mem_of_closed (L : Subgroup FB) (h0 : gw [] ∈ L)
    (hL : ∀ p : Fin 2 × Bool, L.map (phiL p) ≤ L) (w : RawWord (Fin 2)) : gw w ∈ L := by
  induction w using List.reverseRecOn with
  | nil => exact h0
  | append_singleton u p ih =>
    rw [← phiL_gw]; exact hL p ⟨_, ih, rfl⟩

/-- **`G_code` is `HB_R` in `F_big`**, for every oracle `R` (unconditionally). -/
theorem hb_Gcode (R : Set ℕ) : HB R Gcode := by
  classical
  refine hb_of_saturated fg_FB (classCR_isFP_two_FB (R := R)).1 (classCR_isFP_two_FB (R := R)).2
    Gcode
    (letters.map phiL) ?_ ?_ ?_ {gw []} ?_ ?_
  · intro φ hφ
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hφ
    exact phiL_injective p
  · intro φ hφ
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hφ
    exact Gcode_map_le p
  · intro φ hφ
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hφ
    exact Gcode_inf_range_le p
  · intro x hx
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx
    subst hx
    exact Subgroup.subset_closure ⟨[], rfl⟩
  · intro L h0 hL
    rw [Gcode, Subgroup.closure_le]
    rintro _ ⟨w, rfl⟩
    exact gw_mem_of_closed L (h0 (by simp))
      (fun p => hL (phiL p) (List.mem_map.2 ⟨p, mem_letters p, rfl⟩)) w

end TheoremA.Kernel
