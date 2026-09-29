module

public import RequestProject.TheoremA.Groups.FreeProdNF
public import RequestProject.TheoremA.Groups.SegForm
public import RequestProject.TheoremA.Groups.ProdAmalgPres

/-!
# The subgroups `V_S = ⟨v_s | s ∈ S⟩` (normal forms)

`F_c = F(c₀, d, e, c₁, …, c_ℓ)` is `FreeGroup (Fin 3 ⊕ Fin ℓ)` (`inl 0 = c₀`, `inl 1 = d`,
`inl 2 = e`, `inr i = c_{i+1}`), and `v_s = c₀^s c₁^s ⋯ c_ℓ^s d e^s`.

For a group `B` and `y : Fin ℓ → B`, `kappa y : F_c → A₃ ∗ B` sends `c₀, d, e` to the free factor
`A₃ = F(3)` and `c_{i+1}` to `y i`.  An admissible segment form of an element of `V_ℤ` maps to an
alternating product whose `B`-pieces are `(∏ yᵢ^s)^{±1}` (`kappa_segEval`, `altOK_tailAlt`).

* `vhom_injective` — (`ℓ ≥ 1`) the `v_s` freely generate `V_ℤ`;
* `mem_VS_of_kappa_eq` — the key step of [Leary 2018, Lemma 2.4]: if `J`, `j` detect `S`
  (`j₁^s ⋯ j_ℓ^s = 1 ↔ s ∈ S`) and `x ∈ V_ℤ` has the same image under the untwisted and the
  twisted embedding into `A₃ ∗ (F(ℓ) × J)`, then `x ∈ V_S`.
-/

@[expose] public section

namespace TheoremA.Coding

open Monoid NF TheoremA.RelPres

/-- The free group `F(c₀, d, e, c₁, …, c_ℓ)`. -/
abbrev Fc (ℓ : ℕ) : Type := FreeGroup (Fin 3 ⊕ Fin ℓ)

variable {ℓ : ℕ}

/-- `c₀`. -/
def c0 : Fc ℓ := FreeGroup.of (Sum.inl 0)
/-- `d`. -/
def dd : Fc ℓ := FreeGroup.of (Sum.inl 1)
/-- `e`. -/
def ee : Fc ℓ := FreeGroup.of (Sum.inl 2)
/-- `c_{i+1}`. -/
def cc (i : Fin ℓ) : Fc ℓ := FreeGroup.of (Sum.inr i)

/-- `c₁^s ⋯ c_ℓ^s`. -/
def Cs (s : ℤ) : Fc ℓ := (List.ofFn fun i => cc i ^ s).prod

/-- `v_s = c₀^s c₁^s ⋯ c_ℓ^s d e^s`. -/
def vv (s : ℤ) : Fc ℓ := c0 ^ s * Cs s * dd * ee ^ s

variable (ℓ) in
/-- `V_ℤ`. -/
def VZ : Subgroup (Fc ℓ) := Subgroup.closure (Set.range vv)

variable (ℓ) in
/-- `V_S`. -/
def VS (S : Set ℤ) : Subgroup (Fc ℓ) := Subgroup.closure (vv '' S)

theorem Cs_zero : (Cs 0 : Fc ℓ) = 1 := by simp [Cs]

theorem vv_zero : (vv 0 : Fc ℓ) = dd := by simp [vv, Cs_zero]

theorem VS_le_VZ (S : Set ℤ) : VS ℓ S ≤ VZ ℓ :=
  Subgroup.closure_mono (Set.image_subset_range _ _)

/-! ### The free factor `A₃` and the maps `kappa` -/

/-- `A₃ = F(c₀, d, e)` (abstractly). -/
abbrev A3 : Type := FreeGroup (Fin 3)

/-- The generators of `A₃`. -/
def a0 : A3 := FreeGroup.of 0
/-- The generators of `A₃`. -/
def ad : A3 := FreeGroup.of 1
/-- The generators of `A₃`. -/
def ae : A3 := FreeGroup.of 2

variable {B : Type} [Group B]

/-- `A₃ ∗ B`. -/
abbrev KF (B : Type) [Group B] : Type := CoprodI (amalgFam A3 B)

/-- The left factor. -/
def inlK : A3 →* KF B := CoprodI.of (M := amalgFam A3 B) (i := false)
/-- The right factor. -/
def inrK : B →* KF B := CoprodI.of (M := amalgFam A3 B) (i := true)

/-- `kappa y`. -/
def kappa (y : Fin ℓ → B) : Fc ℓ →* KF B :=
  FreeGroup.lift (Sum.elim (fun j => inlK (FreeGroup.of j)) (fun i => inrK (y i)))

/-- `y₁^s ⋯ y_ℓ^s`. -/
def Ys (y : Fin ℓ → B) (s : ℤ) : B := (List.ofFn fun i => y i ^ s).prod

theorem kappa_c0 (y : Fin ℓ → B) : kappa y c0 = inlK a0 := by simp [kappa, c0, a0]
theorem kappa_dd (y : Fin ℓ → B) : kappa y dd = inlK ad := by simp [kappa, dd, ad]
theorem kappa_ee (y : Fin ℓ → B) : kappa y ee = inlK ae := by simp [kappa, ee, ae]

theorem kappa_Cs (y : Fin ℓ → B) (s : ℤ) : kappa y (Cs s) = inrK (Ys y s) := by
  simp [Cs, Ys, map_list_prod, List.map_ofFn, Function.comp_def, kappa, cc]

theorem kappa_vv (y : Fin ℓ → B) (s : ℤ) :
    kappa y (vv s) = inlK (a0 ^ s) * inrK (Ys y s) * inlK (ad * ae ^ s) := by
  simp only [vv, map_mul, map_zpow, kappa_c0, kappa_dd, kappa_ee, kappa_Cs, mul_assoc]

/-! ### Alternating images of segment forms -/

/-- The `A₃`-piece before a factor `v_s^{±1}`. -/
def pre (s : ℤ) (b : Bool) : A3 := if b then a0 ^ s else (ad * ae ^ s)⁻¹

/-- The `A₃`-piece after a factor `v_s^{±1}`. -/
def post (s : ℤ) (b : Bool) : A3 := if b then ad * ae ^ s else a0 ^ (-s)

theorem kappa_sgn_vv (y : Fin ℓ → B) (s : ℤ) (b : Bool) :
    kappa y (Seg.sgn (vv s) b) = inlK (pre s b) * inrK (Seg.sgn (Ys y s) b) * inlK (post s b) := by
  cases b
  · simp only [Seg.sgn, map_inv, kappa_vv, pre, post, mul_inv_rev, zpow_neg, Bool.false_eq_true,
      if_false, mul_assoc, map_mul, map_zpow]
  · simp only [Seg.sgn, kappa_vv, pre, post, if_true]

/-- The `B`/`A₃` pieces of the image of a segment tail. -/
def tailAlt (y : Fin ℓ → B) : List (ℤ × Bool × ℤ) → List (B × A3)
  | [] => []
  | [e] => [(Seg.sgn (Ys y e.1) e.2.1, post e.1 e.2.1 * ad ^ e.2.2)]
  | e :: f :: L => (Seg.sgn (Ys y e.1) e.2.1, post e.1 e.2.1 * ad ^ e.2.2 * pre f.1 f.2.1) ::
      tailAlt y (f :: L)

/-- The first `A₃`-piece. -/
def headA (z₀ : ℤ) : List (ℤ × Bool × ℤ) → A3
  | [] => ad ^ z₀
  | e :: _ => ad ^ z₀ * pre e.1 e.2.1

theorem altProd_mul_left (x a : A3) (L : List (B × A3)) :
    CoprodI.of (M := amalgFam A3 B) (i := false) x * altProd (P := amalgFam A3 B) a L =
      altProd (P := amalgFam A3 B) (x * a) L := by
  cases L with
  | nil => simp only [altProd, map_mul]
  | cons p L => simp only [altProd, map_mul, mul_assoc]

theorem kappa_eval_aux (y : Fin ℓ → B) : ∀ (z₀ : ℤ) (L : List (ℤ × Bool × ℤ)),
    kappa y (vv 0 ^ z₀ * Seg.tail vv L) = altProd (P := amalgFam A3 B) (headA z₀ L) (tailAlt y L)
  | z₀, [] => by
    simp only [Seg.tail, mul_one, map_zpow, vv_zero, kappa_dd, headA, tailAlt, altProd]
    rfl
  | z₀, [e] => by
    have h := kappa_eval_aux y e.2.2 []
    simp only [Seg.tail, mul_one] at h ⊢
    rw [show vv 0 ^ z₀ * (Seg.sgn (vv e.1) e.2.1 * vv 0 ^ e.2.2) =
      vv 0 ^ z₀ * Seg.sgn (vv e.1) e.2.1 * vv 0 ^ e.2.2 by group, map_mul, h, map_mul,
      kappa_sgn_vv]
    simp only [headA, tailAlt, altProd, map_zpow, vv_zero, kappa_dd, map_mul, inlK, inrK,
      mul_assoc]
    rfl
  | z₀, e :: f :: L => by
    have h := kappa_eval_aux y e.2.2 (f :: L)
    rw [show vv 0 ^ z₀ * Seg.tail vv (e :: f :: L) =
      vv 0 ^ z₀ * Seg.sgn (vv e.1) e.2.1 * (vv 0 ^ e.2.2 * Seg.tail vv (f :: L)) by
        simp only [Seg.tail]; group, map_mul, h, map_mul, kappa_sgn_vv]
    simp only [headA, tailAlt, altProd]
    rw [show post e.1 e.2.1 * ad ^ e.2.2 * pre f.1 f.2.1 =
      post e.1 e.2.1 * (ad ^ e.2.2 * pre f.1 f.2.1) by group,
      ← altProd_mul_left (post e.1 e.2.1) (ad ^ e.2.2 * pre f.1 f.2.1)]
    simp only [map_zpow, vv_zero, kappa_dd, map_mul, inlK, inrK, mul_assoc]
    rfl

/-- **Images of segment forms.** -/
theorem kappa_segEval (y : Fin ℓ → B) (z₀ : ℤ) (L : List (ℤ × Bool × ℤ)) :
    kappa y (Seg.eval vv z₀ L) = altProd (P := amalgFam A3 B) (headA z₀ L) (tailAlt y L) :=
  kappa_eval_aux y z₀ L

theorem map_fst_tailAlt (y : Fin ℓ → B) : ∀ L : List (ℤ × Bool × ℤ),
    (tailAlt y L).map Prod.fst = L.map fun e => Seg.sgn (Ys y e.1) e.2.1
  | [] => rfl
  | [e] => rfl
  | e :: f :: L => by
    simp only [tailAlt, List.map_cons]
    rw [map_fst_tailAlt y (f :: L)]
    rfl

theorem tailAlt_eq_nil (y : Fin ℓ → B) {L : List (ℤ × Bool × ℤ)} (h : tailAlt y L = []) :
    L = [] := by
  have := congrArg List.length (map_fst_tailAlt y L)
  rw [h] at this
  simpa using this.symm

/-! ### Nontriviality of the internal pieces (abelianization) -/

/-- Exponent-sum homomorphism of `A₃`. -/
def expA (j : Fin 3) : A3 →* Multiplicative ℤ :=
  FreeGroup.lift fun i => if i = j then Multiplicative.ofAdd 1 else 1

theorem piece_ne_one {s s' z : ℤ} {b b' : Bool} (hs : s ≠ 0) (hs' : s' ≠ 0)
    (h : z = 0 → ¬ (s = s' ∧ b ≠ b')) : post s b * ad ^ z * pre s' b' ≠ 1 := by
  intro he
  have h0 := congrArg (fun x => Multiplicative.toAdd (expA 0 x)) he
  have h1 := congrArg (fun x => Multiplicative.toAdd (expA 1 x)) he
  have h2 := congrArg (fun x => Multiplicative.toAdd (expA 2 x)) he
  cases b <;> cases b' <;>
    simp [post, pre, expA, a0, ad, ae, toAdd_zpow] at h0 h1 h2 h <;> omega

theorem altOK_cons (p : B × A3) (M : List (B × A3)) :
    AltOK (P := amalgFam A3 B) (p :: M) ↔
      p.1 ≠ 1 ∧ (M ≠ [] → p.2 ≠ 1) ∧ AltOK (P := amalgFam A3 B) M := by
  cases M <;> simp [AltOK]

theorem altOK_tailAlt (y : Fin ℓ → B) (hY : ∀ s, s ≠ 0 → Ys y s ≠ 1) :
    ∀ L : List (ℤ × Bool × ℤ), Seg.OK L → AltOK (P := amalgFam A3 B) (tailAlt y L)
  | [], _ => trivial
  | [e], h => by
    show Seg.sgn (Ys y e.1) e.2.1 ≠ 1
    have := hY e.1 (h.1 e (by simp))
    unfold Seg.sgn; split_ifs <;> simpa using this
  | e :: f :: L, h => by
    rw [tailAlt, altOK_cons]
    refine ⟨?_, fun _ => ?_, altOK_tailAlt y hY (f :: L) ⟨fun g hg => h.1 g (by simp [hg]),
      h.2.tail⟩⟩
    · show Seg.sgn (Ys y e.1) e.2.1 ≠ 1
      have := hY e.1 (h.1 e (by simp))
      unfold Seg.sgn; split_ifs <;> simpa using this
    · exact piece_ne_one (h.1 e (by simp)) (h.1 f (by simp)) (List.isChain_cons_cons.1 h.2).1

/-! ### Freeness of the `v_s` -/

/-- Exponent-sum homomorphism of `F(ℓ)` for the first generator. -/
def expFirst (hℓ : 1 ≤ ℓ) : FreeGroup (Fin ℓ) →* Multiplicative ℤ :=
  FreeGroup.lift fun i => if i = ⟨0, hℓ⟩ then Multiplicative.ofAdd 1 else 1

theorem expFirst_Ys (hℓ : 1 ≤ ℓ) (s : ℤ) :
    Multiplicative.toAdd (expFirst hℓ (Ys FreeGroup.of s)) = s := by
  simp only [Ys, map_list_prod, List.map_ofFn, Function.comp_def, map_zpow, expFirst,
    FreeGroup.lift_apply_of, List.prod_ofFn]
  rw [Finset.prod_eq_single ⟨0, hℓ⟩]
  · simp
  · intro i _ hi; simp [hi]
  · simp

theorem Ys_of_ne_one (hℓ : 1 ≤ ℓ) {s : ℤ} (hs : s ≠ 0) : Ys (FreeGroup.of : Fin ℓ → _) s ≠ 1 := by
  intro h
  have := expFirst_Ys hℓ s
  rw [h] at this
  simp at this
  exact hs this.symm

/-- `s ↦ v_s` on a free group of rank `ℤ`. -/
def vhom : FreeGroup ℤ →* Fc ℓ := FreeGroup.lift vv

/-- **The `v_s` are free generators** (`ℓ ≥ 1`). -/
theorem vhom_injective (hℓ : 1 ≤ ℓ) : Function.Injective (vhom : FreeGroup ℤ →* Fc ℓ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ Subgroup.closure (Set.range (FreeGroup.of : ℤ → FreeGroup ℤ)) := by
    rw [FreeGroup.closure_range_of]; trivial
  obtain ⟨z₀, L, hL, rfl⟩ := Seg.exists_segForm FreeGroup.of hmem
  rw [Seg.map_eval] at hg
  simp only [vhom, FreeGroup.lift_apply_of] at hg
  have hk := congrArg (kappa (B := FreeGroup (Fin ℓ)) FreeGroup.of) hg
  rw [kappa_segEval, map_one] at hk
  rcases L.eq_nil_or_concat with rfl | ⟨L', e, hLe⟩
  · simp only [Seg.eval, Seg.tail, mul_one, vv_zero] at hg ⊢
    have := congrArg (fun x => Multiplicative.toAdd
      (expA 1 ((FreeGroup.lift (Sum.elim FreeGroup.of fun _ => 1) : Fc ℓ →* A3) x))) hg
    simp [dd, expA] at this
    simp [this]
  · exfalso
    have hne : tailAlt (FreeGroup.of : Fin ℓ → FreeGroup (Fin ℓ)) L ≠ [] := by
      intro h; have := tailAlt_eq_nil _ h; simp [hLe] at this
    exact altProd_not_mem_range (altOK_tailAlt _ (fun s hs => Ys_of_ne_one hℓ hs) L hL) hne 1
      (by rw [hk, map_one])

theorem range_vhom : (vhom : FreeGroup ℤ →* Fc ℓ).range = VZ ℓ := by
  rw [VZ, vhom, FreeGroup.range_lift_eq_closure]

/-! ### The untwisted and twisted embeddings into `A₃ ∗ (F(ℓ) × J)` -/

section Twist

variable {J : Type} [Group J]

/-- Untwisted: `c_{i+1} ↦ (c_{i+1}, 1)`. -/
def yU : Fin ℓ → FreeGroup (Fin ℓ) × J := fun i => (FreeGroup.of i, 1)

/-- Twisted: `c_{i+1} ↦ (c_{i+1}, jᵢ)`. -/
def yT (j : Fin ℓ → J) : Fin ℓ → FreeGroup (Fin ℓ) × J := fun i => (FreeGroup.of i, j i)

theorem Ys_pair {B₁ B₂ : Type} [Group B₁] [Group B₂] (y₁ : Fin ℓ → B₁) (y₂ : Fin ℓ → B₂)
    (s : ℤ) : Ys (fun i => (y₁ i, y₂ i)) s = (Ys y₁ s, Ys y₂ s) := by
  ext
  · have := (MonoidHom.fst B₁ B₂).map_list_prod (List.ofFn fun i => (y₁ i, y₂ i) ^ s)
    simpa [Ys, List.map_ofFn, Function.comp_def] using this
  · have := (MonoidHom.snd B₁ B₂).map_list_prod (List.ofFn fun i => (y₁ i, y₂ i) ^ s)
    simpa [Ys, List.map_ofFn, Function.comp_def] using this

theorem Ys_yU (s : ℤ) : Ys (yU (ℓ := ℓ) (J := J)) s = (Ys FreeGroup.of s, 1) := by
  have := Ys_pair (FreeGroup.of : Fin ℓ → FreeGroup (Fin ℓ)) (fun _ => (1 : J)) s
  exact this.trans (by simp [Ys])

theorem Ys_yT (j : Fin ℓ → J) (s : ℤ) : Ys (yT j) s = (Ys FreeGroup.of s, Ys j s) :=
  Ys_pair _ j s

theorem Ys_yU_ne_one (hℓ : 1 ≤ ℓ) {s : ℤ} (hs : s ≠ 0) : Ys (yU (ℓ := ℓ) (J := J)) s ≠ 1 := by
  rw [Ys_yU]; intro h; exact Ys_of_ne_one hℓ hs (congrArg Prod.fst h)

theorem Ys_yT_ne_one (hℓ : 1 ≤ ℓ) (j : Fin ℓ → J) {s : ℤ} (hs : s ≠ 0) : Ys (yT j) s ≠ 1 := by
  rw [Ys_yT]; intro h; exact Ys_of_ne_one hℓ hs (congrArg Prod.fst h)

theorem sgn_injective {G : Type*} [Group G] {g h : G} (b : Bool) (he : Seg.sgn g b = Seg.sgn h b) :
    g = h := by
  cases b <;> simpa [Seg.sgn] using he

/-- **The key step of Lemma 2.4.**  If `j` detects `S` and `x ∈ V_ℤ` has equal images under the
twisted and untwisted embeddings, then `x ∈ V_S`. -/
theorem mem_VS_of_kappa_eq (hℓ : 1 ≤ ℓ) (j : Fin ℓ → J) {S : Set ℤ}
    (hD : ∀ s, Ys j s = 1 ↔ s ∈ S) (h0 : (0 : ℤ) ∈ S) {x : Fc ℓ} (hx : x ∈ VZ ℓ)
    (he : kappa (yT j) x = kappa yU x) : x ∈ VS ℓ S := by
  obtain ⟨z₀, L, hL, rfl⟩ := Seg.exists_segForm vv hx
  rw [kappa_segEval, kappa_segEval] at he
  have hm := eq_of_altProd_eq (altOK_tailAlt _ (fun s hs => Ys_yT_ne_one hℓ j hs) L hL)
    (altOK_tailAlt _ (fun s hs => Ys_yU_ne_one hℓ hs) L hL) he
  have hm' : (tailAlt (yT j) L).map Prod.fst = (tailAlt yU L).map Prod.fst := hm
  rw [map_fst_tailAlt, map_fst_tailAlt] at hm'
  clear hm
  have hm := hm'
  refine Seg.eval_mem vv z₀ L (Subgroup.subset_closure ⟨0, h0, rfl⟩) ?_
  intro e he'
  refine Subgroup.subset_closure ⟨e.1, ?_, rfl⟩
  have := congrArg (fun l => l[L.idxOf e]?) hm
  simp only [List.getElem?_map, List.getElem?_idxOf he', Option.map_some, Option.some.injEq]
    at this
  have h2 := sgn_injective _ this
  rw [Ys_yT, Ys_yU] at h2
  exact (hD e.1).1 (congrArg Prod.snd h2)

theorem kappa_eq_of_mem_VS (j : Fin ℓ → J) {S : Set ℤ} (hD : ∀ s, Ys j s = 1 ↔ s ∈ S)
    {x : Fc ℓ} (hx : x ∈ VS ℓ S) : kappa (yT j) x = kappa yU x := by
  have : VS ℓ S ≤ MonoidHom.eqLocus (kappa (yT j)) (kappa yU) := by
    rw [VS, Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    show kappa (yT j) (vv s) = kappa yU (vv s)
    rw [kappa_vv, kappa_vv, Ys_yT, Ys_yU, (hD s).2 hs]
  exact this hx

/-- The retraction killing `J`. -/
def retr : KF (FreeGroup (Fin ℓ) × J) →* Fc ℓ :=
  CoprodI.lift (amalgLiftFam (FreeGroup.lift fun k => FreeGroup.of (Sum.inl k))
    ((FreeGroup.lift fun i => FreeGroup.of (Sum.inr i)).comp (MonoidHom.fst _ _)))

theorem retr_kappa (y : Fin ℓ → FreeGroup (Fin ℓ) × J) (hy : ∀ i, (y i).1 = FreeGroup.of i) :
    (retr (J := J)).comp (kappa y) = MonoidHom.id (Fc ℓ) := by
  ext k
  rcases k with k | i
  · simp only [MonoidHom.comp_apply, kappa, FreeGroup.lift_apply_of, Sum.elim_inl,
      MonoidHom.id_apply, retr, inlK]
    erw [CoprodI.lift_of]
    exact FreeGroup.lift_apply_of (f := fun k : Fin 3 => (FreeGroup.of (Sum.inl k) : Fc ℓ))
  · simp only [MonoidHom.comp_apply, kappa, FreeGroup.lift_apply_of, Sum.elim_inr,
      MonoidHom.id_apply, retr, inrK]
    erw [CoprodI.lift_of]
    show FreeGroup.lift _ ((y i).1) = _
    rw [hy]
    exact FreeGroup.lift_apply_of (f := fun k : Fin ℓ => (FreeGroup.of (Sum.inr k) : Fc ℓ))

theorem kappa_yU_injective : Function.Injective (kappa (yU (ℓ := ℓ) (J := J))) :=
  Function.LeftInverse.injective (g := retr) fun x => by
    rw [← MonoidHom.comp_apply, retr_kappa _ (fun i => rfl)]; rfl

theorem kappa_yT_injective (j : Fin ℓ → J) : Function.Injective (kappa (yT j)) :=
  Function.LeftInverse.injective (g := retr) fun x => by
    rw [← MonoidHom.comp_apply, retr_kappa _ (fun i => rfl)]; rfl

theorem retr_apply_kappa (y : Fin ℓ → FreeGroup (Fin ℓ) × J) (hy : ∀ i, (y i).1 = FreeGroup.of i)
    (x : Fc ℓ) : retr (kappa y x) = x := by
  rw [← MonoidHom.comp_apply, retr_kappa y hy]; rfl

end Twist

end TheoremA.Coding
