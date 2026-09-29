module

public import Mathlib.GroupTheory.HNNExtension

/-!
# Consequences of Britton's lemma

Built on Mathlib's reduced words for `HNNExtension G A B φ` (convention
`t * of a * t⁻¹ = of (φ a)`) and Mathlib's Britton lemma
`HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range`.

* `exists_pinch` — a word `h t^{u₁} g₁ ⋯ t^{uₖ} gₖ` (`k ≥ 1`) representing an element of the base
  contains a pinch `t^u g t^{-u}` with `g ∈ toSubgroup A B u`;
* `exists_mem_of_reduce` — an abstract reduction principle;
* `mem_of_mem_closure_invariant` — for `W₀ ≤ G` with `φ(W₀ ∩ A) ⊆ W₀` and `φ⁻¹(W₀ ∩ B) ⊆ W₀`,
  `⟨W₀, t⟩ ∩ G = W₀`;
* `mem_of_mem_closure_centralizing` — in the HNN extension centralizing `V`, if `X ⊓ V ≤ W₀` and
  `W₀ ⊓ V ≤ X` then `⟨W₀, t X t⁻¹⟩ ∩ G = W₀`;
* `hnnMap_injective` — functoriality of HNN extensions along an injective map `f` with
  `f⁻¹(A') = A`, `f⁻¹(B') = B`.
-/

@[expose] public section

namespace TheoremA.Britton

open HNNExtension HNNExtension.NormalWord

section Core

variable {G : Type*} [Group G] {A B : Subgroup G} (φ : A ≃* B)

/-- The element `of h * ∏ (t^{u} * of g)` of a head and a list of pairs. -/
def wprod (h : G) (l : List (ℤˣ × G)) : HNNExtension G A B φ :=
  of h * (l.map fun x => t ^ (x.1 : ℤ) * of x.2).prod

theorem wprod_nil (h : G) : wprod φ h [] = of h := by simp [wprod]

theorem wprod_cons (h : G) (x : ℤˣ × G) (l : List (ℤˣ × G)) :
    wprod φ h (x :: l) = of h * (t ^ (x.1 : ℤ) * of x.2) * wprod φ 1 l := by
  simp [wprod, mul_assoc]

theorem wprod_append (h : G) (l₁ l₂ : List (ℤˣ × G)) :
    wprod φ h (l₁ ++ l₂) = wprod φ h l₁ * wprod φ 1 l₂ := by
  simp [wprod, mul_assoc]

theorem of_mul_wprod (k h : G) (l : List (ℤˣ × G)) :
    (of k : HNNExtension G A B φ) * wprod φ h l = wprod φ (k * h) l := by
  simp [wprod, mul_assoc]

theorem wprod_concat_mul_of (h : G) (L : List (ℤˣ × G)) (b : ℤˣ × G) (k : G) :
    wprod φ h (L ++ [b]) * of k = wprod φ h (L ++ [(b.1, b.2 * k)]) := by
  simp [wprod, mul_assoc]

theorem eq_nil_or_append_singleton {α : Type*} (l : List α) :
    l = [] ∨ ∃ L b, l = L ++ [b] := by
  rcases l.eq_nil_or_concat with h | ⟨L, b, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨L, b, by simp [h]⟩

theorem units_eq_neg_of_ne {u v : ℤˣ} (h : u ≠ v) : v = -u := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
    simp_all

/-- Absence of pinches gives Mathlib's chain condition for reduced words. -/
theorem isChain_of_no_pinch : ∀ (l : List (ℤˣ × G)),
    (∀ l₁ u g g' l₂, l = l₁ ++ (u, g) :: (-u, g') :: l₂ → g ∉ toSubgroup A B u) →
    l.IsChain (fun a b => a.2 ∈ toSubgroup A B a.1 → a.1 = b.1)
  | [], _ => List.IsChain.nil
  | [_], _ => List.isChain_singleton _
  | a :: b :: l, H => by
    rw [List.isChain_cons_cons]
    refine ⟨fun ha => ?_, isChain_of_no_pinch (b :: l) fun l₁ u g g' l₂ h => ?_⟩
    · by_contra hne
      have hb := units_eq_neg_of_ne hne
      exact H [] a.1 a.2 b.2 l (by rw [← hb]; rfl) ha
    · exact H (a :: l₁) u g g' l₂ (by rw [h]; rfl)

/-- **Britton's lemma, pinch form.** -/
theorem exists_pinch {h : G} {l : List (ℤˣ × G)} (hl : l ≠ [])
    (hr : wprod φ h l ∈ (of : G →* HNNExtension G A B φ).range) :
    ∃ l₁ u g g' l₂, l = l₁ ++ (u, g) :: (-u, g') :: l₂ ∧ g ∈ toSubgroup A B u := by
  by_contra hne
  push_neg at hne
  have hc := isChain_of_no_pinch l hne
  exact hl (ReducedWord.toList_eq_nil_of_mem_of_range φ ⟨h, l, hc⟩ hr)

/-- Every element is the product of a reduced word. -/
theorem exists_wprod (x : HNNExtension G A B φ) : ∃ h l, wprod φ h l = x ∧
    l.IsChain (fun a b => a.2 ∈ toSubgroup A B a.1 → a.1 = b.1) := by
  obtain ⟨d⟩ := TransversalPair.nonempty G A B
  exact ⟨((NormalWord.equiv φ d) x).head, ((NormalWord.equiv φ d) x).toList,
    (NormalWord.equiv φ d).symm_apply_apply x, ((NormalWord.equiv φ d) x).chain⟩

/-- Evaluation of a pinch. -/
theorem pinch_eq (u : ℤˣ) (g : G) (hg : g ∈ toSubgroup A B u) :
    ((u = 1 ∧ ∃ h : g ∈ A, (t ^ (u : ℤ) * of g * t ^ ((-u : ℤˣ) : ℤ) : HNNExtension G A B φ) =
        of (φ ⟨g, h⟩ : G)) ∨
      (u = -1 ∧ ∃ h : g ∈ B, (t ^ (u : ℤ) * of g * t ^ ((-u : ℤˣ) : ℤ) :
        HNNExtension G A B φ) = of (φ.symm ⟨g, h⟩ : G))) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact Or.inl ⟨rfl, hg, by simpa using (equiv_eq_conj (φ := φ) ⟨g, hg⟩).symm⟩
  · exact Or.inr ⟨rfl, hg, by simpa using (equiv_symm_eq_conj (φ := φ) ⟨g, hg⟩).symm⟩

/-- **Abstract reduction principle.** -/
theorem exists_mem_of_reduce (W₀ : Subgroup G) (Good : G → List (ℤˣ × G) → Prop)
    (hnil : ∀ h, Good h [] → h ∈ W₀)
    (hred : ∀ h l₁ u g g' l₂, Good h (l₁ ++ (u, g) :: (-u, g') :: l₂) → g ∈ toSubgroup A B u →
      ∃ h' l', Good h' l' ∧ l'.length < (l₁ ++ (u, g) :: (-u, g') :: l₂).length ∧
        wprod φ h' l' = wprod φ h (l₁ ++ (u, g) :: (-u, g') :: l₂)) :
    ∀ h l, Good h l → wprod φ h l ∈ (of : G →* HNNExtension G A B φ).range →
      ∃ w ∈ W₀, (of w : HNNExtension G A B φ) = wprod φ h l := by
  intro h l
  induction hlen : l.length using Nat.strong_induction_on generalizing h l with
  | _ n ih =>
  intro hg hr
  by_cases hl : l = []
  · subst hl; exact ⟨h, hnil h hg, (wprod_nil φ h).symm⟩
  · obtain ⟨l₁, u, g, g', l₂, rfl, hmem⟩ := exists_pinch φ hl hr
    obtain ⟨h', l', hg', hlt, heq⟩ := hred h l₁ u g g' l₂ hg hmem
    obtain ⟨w, hw, hweq⟩ := ih l'.length (hlen ▸ hlt) h' l' rfl hg' (heq ▸ hr)
    exact ⟨w, hw, hweq.trans heq⟩

/-- Reduction of a pinch for words with entries in `W₀`. -/
theorem wprod_pinch (h : G) (l₁ : List (ℤˣ × G)) (u : ℤˣ) (g g' : G) (l₂ : List (ℤˣ × G))
    (k : G) (hk : (t ^ (u : ℤ) * of g * t ^ ((-u : ℤˣ) : ℤ) : HNNExtension G A B φ) = of k) :
    wprod φ h (l₁ ++ (u, g) :: (-u, g') :: l₂) = wprod φ h l₁ * of (k * g') * wprod φ 1 l₂ := by
  rw [wprod_append, wprod_cons, wprod_cons, map_mul, ← hk]
  simp [mul_assoc]

/-- **Invariant subgroups.**  If `φ(W₀ ∩ A) ⊆ W₀` and `φ⁻¹(W₀ ∩ B) ⊆ W₀` then every element of
`⟨W₀, t⟩` lying in the base lies in `W₀`. -/
theorem mem_of_mem_closure_invariant (W₀ : Subgroup G)
    (hA : ∀ a : A, (a : G) ∈ W₀ → (φ a : G) ∈ W₀)
    (hB : ∀ b : B, (b : G) ∈ W₀ → (φ.symm b : G) ∈ W₀) (x : HNNExtension G A B φ)
    (hx : x ∈ Subgroup.closure ((of '' (W₀ : Set G)) ∪ {t}))
    (hxr : x ∈ (of : G →* HNNExtension G A B φ).range) :
    ∃ w ∈ W₀, (of w : HNNExtension G A B φ) = x := by
  let Good : G → List (ℤˣ × G) → Prop := fun h l => h ∈ W₀ ∧ ∀ p ∈ l, p.2 ∈ W₀
  have hrep : ∃ h l, Good h l ∧ wprod φ h l = x := by
    clear hxr
    induction hx using Subgroup.closure_induction_left with
    | one => exact ⟨1, [], ⟨W₀.one_mem, by simp⟩, by simp [wprod]⟩
    | mul_left y hy z _ ih =>
      obtain ⟨h, l, ⟨hh, hl⟩, rfl⟩ := ih
      rcases hy with ⟨w, hw, rfl⟩ | rfl
      · exact ⟨w * h, l, ⟨W₀.mul_mem hw hh, hl⟩, (of_mul_wprod φ w h l).symm⟩
      · refine ⟨1, (1, h) :: l, ⟨W₀.one_mem, ?_⟩, ?_⟩
        · rintro p (_ | ⟨_, hp⟩); exacts [hh, hl p hp]
        · rw [wprod_cons]; simp [wprod, mul_assoc]
    | inv_mul_cancel y hy z _ ih =>
      obtain ⟨h, l, ⟨hh, hl⟩, rfl⟩ := ih
      rcases hy with ⟨w, hw, rfl⟩ | rfl
      · exact ⟨w⁻¹ * h, l, ⟨W₀.mul_mem (W₀.inv_mem hw) hh, hl⟩, by
          rw [← of_mul_wprod, map_inv]⟩
      · refine ⟨1, (-1, h) :: l, ⟨W₀.one_mem, ?_⟩, ?_⟩
        · rintro p (_ | ⟨_, hp⟩); exacts [hh, hl p hp]
        · rw [wprod_cons]; simp [wprod, mul_assoc]
  obtain ⟨h, l, hg, rfl⟩ := hrep
  refine exists_mem_of_reduce φ W₀ Good (fun h hh => hh.1) ?_ h l hg hxr
  intro h l₁ u g g' l₂ ⟨hh, hl⟩ hgu
  have hgW : g ∈ W₀ := hl (u, g) (by simp)
  have hg'W : g' ∈ W₀ := hl (-u, g') (by simp)
  obtain ⟨k, hkW, hk⟩ : ∃ k ∈ W₀, (t ^ (u : ℤ) * of g * t ^ ((-u : ℤˣ) : ℤ) :
      HNNExtension G A B φ) = of k := by
    rcases pinch_eq φ u g hgu with ⟨-, h1, e⟩ | ⟨-, h1, e⟩
    · exact ⟨_, hA ⟨g, h1⟩ hgW, e⟩
    · exact ⟨_, hB ⟨g, h1⟩ hgW, e⟩
  rw [wprod_pinch φ h l₁ u g g' l₂ k hk]
  have hl₁ : ∀ p ∈ l₁, p.2 ∈ W₀ := fun p hp => hl p (by simp [hp])
  have hl₂ : ∀ p ∈ l₂, p.2 ∈ W₀ := fun p hp => hl p (by simp [hp])
  rcases eq_nil_or_append_singleton l₁ with rfl | ⟨L, b, rfl⟩
  · refine ⟨h * (k * g'), l₂, ⟨W₀.mul_mem hh (W₀.mul_mem hkW hg'W), hl₂⟩, by simp, ?_⟩
    rw [wprod_nil, ← map_mul, of_mul_wprod, mul_one]
  · refine ⟨h, L ++ [(b.1, b.2 * (k * g'))] ++ l₂, ⟨hh, ?_⟩, by simp, ?_⟩
    · intro p hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with (hp | rfl) | hp
      · exact hl₁ p (by simp [hp])
      · exact W₀.mul_mem (hl₁ b (by simp)) (W₀.mul_mem hkW hg'W)
      · exact hl₂ p hp
    · rw [wprod_append, wprod_concat_mul_of]

end Core

section Centralizing

variable {G : Type*} [Group G] (V : Subgroup G)

/-- Alternating lists `(1, x₁), (-1, w₁), …, (1, xₖ), (-1, wₖ)`. -/
def pairList (m : List (G × G)) : List (ℤˣ × G) :=
  m.flatMap fun p => [((1 : ℤˣ), p.1), ((-1 : ℤˣ), p.2)]

omit [Group G] in
theorem pairList_nil : pairList ([] : List (G × G)) = [] := rfl

omit [Group G] in
theorem pairList_cons (p : G × G) (m : List (G × G)) :
    pairList (p :: m) = ((1 : ℤˣ), p.1) :: ((-1 : ℤˣ), p.2) :: pairList m := rfl

omit [Group G] in
theorem pairList_append (m₁ m₂ : List (G × G)) :
    pairList (m₁ ++ m₂) = pairList m₁ ++ pairList m₂ := by
  simp [pairList]

omit [Group G] in
theorem pairList_decomp : ∀ (m : List (G × G)) (l₁ l₂ : List (ℤˣ × G)) (a b : ℤˣ × G),
    pairList m = l₁ ++ a :: b :: l₂ →
    (∃ m₁ p m₂, m = m₁ ++ p :: m₂ ∧ l₁ = pairList m₁ ∧ a = (1, p.1) ∧ b = (-1, p.2) ∧
        l₂ = pairList m₂) ∨
    (∃ m₁ p q m₂, m = m₁ ++ p :: q :: m₂ ∧ l₁ = pairList m₁ ++ [(1, p.1)] ∧ a = (-1, p.2) ∧
        b = (1, q.1) ∧ l₂ = (-1, q.2) :: pairList m₂)
  | [], l₁, l₂, a, b, h => by cases l₁ <;> simp [pairList_nil] at h
  | p :: m, [], l₂, a, b, h => by
    rw [pairList_cons] at h
    simp only [List.nil_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inl ⟨[], p, m, rfl, rfl, rfl, rfl, rfl⟩
  | p :: m, [c], l₂, a, b, h => by
    rw [pairList_cons] at h
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl, h⟩ := h
    cases m with
    | nil => simp [pairList_nil] at h
    | cons q m' =>
      rw [pairList_cons] at h
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨[], p, q, m', rfl, rfl, rfl, rfl, rfl⟩
  | p :: m, c :: d :: l₁, l₂, a, b, h => by
    rw [pairList_cons] at h
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl, h⟩ := h
    rcases pairList_decomp m l₁ l₂ a b h with ⟨m₁, q, m₂, rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨m₁, q, r, m₂, rfl, rfl, rfl, rfl, rfl⟩
    · exact Or.inl ⟨p :: m₁, q, m₂, rfl, rfl, rfl, rfl, rfl⟩
    · exact Or.inr ⟨p :: m₁, q, r, m₂, rfl, rfl, rfl, rfl, rfl⟩

theorem toSubgroup_self (u : ℤˣ) : toSubgroup V V u = V := by
  unfold toSubgroup; split_ifs <;> rfl

/-- In the HNN extension centralizing `V`, the stable letter commutes with `V`. -/
theorem conj_centralizing (u : ℤˣ) (g : G) (hg : g ∈ V) :
    (t ^ (u : ℤ) * of g * t ^ ((-u : ℤˣ) : ℤ) : HNNExtension G V V (MulEquiv.refl V)) = of g := by
  rcases pinch_eq (MulEquiv.refl V) u g (by rw [toSubgroup_self]; exact hg) with
    ⟨-, _, e⟩ | ⟨-, _, e⟩ <;> simpa using e

/-- **Centralizing join lemma.**  In the HNN extension of `G` centralizing `V`, if
`X ⊓ V ≤ W₀` and `W₀ ⊓ V ≤ X`, then every element of `⟨W₀, t X t⁻¹⟩` lying in the base lies
in `W₀`. -/
theorem mem_of_mem_closure_centralizing (X W₀ : Subgroup G) (hXV : X ⊓ V ≤ W₀)
    (hWV : W₀ ⊓ V ≤ X) (x : HNNExtension G V V (MulEquiv.refl V))
    (hx : x ∈ Subgroup.closure ((of '' (W₀ : Set G)) ∪
      ((fun y => t * of y * t⁻¹) '' (X : Set G))))
    (hxr : x ∈ (of : G →* HNNExtension G V V (MulEquiv.refl V)).range) :
    ∃ w ∈ W₀, (of w : HNNExtension G V V (MulEquiv.refl V)) = x := by
  let φ := MulEquiv.refl V
  let Good : G → List (ℤˣ × G) → Prop := fun h l => h ∈ W₀ ∧
    ∃ m : List (G × G), l = pairList m ∧ ∀ p ∈ m, p.1 ∈ X ∧ p.2 ∈ W₀
  have hrep : ∃ h l, Good h l ∧ wprod φ h l = x := by
    clear hxr
    induction hx using Subgroup.closure_induction_left with
    | one => exact ⟨1, [], ⟨W₀.one_mem, [], rfl, by simp⟩, by simp [wprod]⟩
    | mul_left y hy z _ ih =>
      obtain ⟨h, l, ⟨hh, m, rfl, hm⟩, rfl⟩ := ih
      rcases hy with ⟨w, hw, rfl⟩ | ⟨y, hy, rfl⟩
      · exact ⟨w * h, _, ⟨W₀.mul_mem hw hh, m, rfl, hm⟩, (of_mul_wprod φ w h _).symm⟩
      · refine ⟨1, pairList ((y, h) :: m), ⟨W₀.one_mem, (y, h) :: m, rfl, ?_⟩, ?_⟩
        · rintro p (_ | ⟨_, hp⟩); exacts [⟨hy, hh⟩, hm p hp]
        · rw [pairList_cons, wprod_cons, wprod_cons]; simp [wprod, mul_assoc]; try rfl
    | inv_mul_cancel y hy z _ ih =>
      obtain ⟨h, l, ⟨hh, m, rfl, hm⟩, rfl⟩ := ih
      rcases hy with ⟨w, hw, rfl⟩ | ⟨y, hy, rfl⟩
      · exact ⟨w⁻¹ * h, _, ⟨W₀.mul_mem (W₀.inv_mem hw) hh, m, rfl, hm⟩, by
          rw [← of_mul_wprod, map_inv]⟩
      · refine ⟨1, pairList ((y⁻¹, h) :: m), ⟨W₀.one_mem, (y⁻¹, h) :: m, rfl, ?_⟩, ?_⟩
        · rintro p (_ | ⟨_, hp⟩); exacts [⟨X.inv_mem hy, hh⟩, hm p hp]
        · rw [pairList_cons, wprod_cons, wprod_cons]; simp [wprod, mul_assoc]; try rfl
  obtain ⟨h, l, hg, rfl⟩ := hrep
  refine exists_mem_of_reduce φ W₀ Good (fun h hh => hh.1) ?_ h l hg hxr
  rintro h l₁ u g g' l₂ ⟨hh, m, hml, hm⟩ hgu
  rw [toSubgroup_self] at hgu
  rcases pairList_decomp m l₁ l₂ (u, g) (-u, g') hml.symm with
    ⟨m₁, p, m₂, rfl, rfl, hua, hub, rfl⟩ | ⟨m₁, p, q, m₂, rfl, rfl, hua, hub, rfl⟩
  · -- pinch `t x t⁻¹` with `x ∈ X ⊓ V`
    simp only [Prod.mk.injEq] at hua hub
    obtain ⟨rfl, rfl⟩ := hua
    obtain ⟨-, rfl⟩ := hub
    have hp := hm p (by simp)
    have hpW : p.1 ∈ W₀ := hXV ⟨hp.1, hgu⟩
    rw [wprod_pinch φ h _ 1 p.1 p.2 _ p.1 (conj_centralizing V 1 p.1 hgu)]
    have hm₁ : ∀ r ∈ m₁, r.1 ∈ X ∧ r.2 ∈ W₀ := fun r hr => hm r (by simp [hr])
    have hm₂ : ∀ r ∈ m₂, r.1 ∈ X ∧ r.2 ∈ W₀ := fun r hr => hm r (by simp [hr])
    rcases eq_nil_or_append_singleton m₁ with rfl | ⟨M, r, rfl⟩
    · refine ⟨h * (p.1 * p.2), pairList m₂, ⟨W₀.mul_mem hh (W₀.mul_mem hpW hp.2), m₂, rfl, hm₂⟩,
        by simp [pairList_nil], ?_⟩
      rw [pairList_nil, wprod_nil, ← map_mul, of_mul_wprod, mul_one]
    · have hr := hm₁ r (by simp)
      refine ⟨h, pairList (M ++ (r.1, r.2 * (p.1 * p.2)) :: m₂),
        ⟨hh, M ++ (r.1, r.2 * (p.1 * p.2)) :: m₂, rfl, ?_⟩,
        by simp [pairList_append, pairList_cons, pairList_nil], ?_⟩
      · intro s hs
        simp only [List.mem_append, List.mem_cons] at hs
        rcases hs with hs | rfl | hs
        · exact hm₁ s (by simp [hs])
        · exact ⟨hr.1, W₀.mul_mem hr.2 (W₀.mul_mem hpW hp.2)⟩
        · exact hm₂ s hs
      · rw [pairList_append, pairList_append, pairList_cons, pairList_cons, pairList_nil]
        have e1 : pairList M ++ [((1 : ℤˣ), r.1), ((-1 : ℤˣ), r.2)] =
            (pairList M ++ [((1 : ℤˣ), r.1)]) ++ [((-1 : ℤˣ), r.2)] := by simp
        have e2 : pairList M ++ ((1 : ℤˣ), r.1) :: ((-1 : ℤˣ), r.2 * (p.1 * p.2)) ::
            pairList m₂ = ((pairList M ++ [((1 : ℤˣ), r.1)]) ++
              [((-1 : ℤˣ), r.2 * (p.1 * p.2))]) ++ pairList m₂ := by simp
        rw [e1, wprod_concat_mul_of, e2, wprod_append]
  · -- pinch `t⁻¹ w t` with `w ∈ W₀ ⊓ V`
    simp only [Prod.mk.injEq] at hua hub
    obtain ⟨rfl, rfl⟩ := hua
    obtain ⟨-, rfl⟩ := hub
    have hp := hm p (by simp)
    have hq := hm q (by simp)
    have hpX : p.2 ∈ X := hWV ⟨hp.2, hgu⟩
    have hm₁ : ∀ r ∈ m₁, r.1 ∈ X ∧ r.2 ∈ W₀ := fun r hr => hm r (by simp [hr])
    have hm₂ : ∀ r ∈ m₂, r.1 ∈ X ∧ r.2 ∈ W₀ := fun r hr => hm r (by simp [hr])
    refine ⟨h, pairList (m₁ ++ (p.1 * p.2 * q.1, q.2) :: m₂),
      ⟨hh, m₁ ++ (p.1 * p.2 * q.1, q.2) :: m₂, rfl, ?_⟩,
      by simp [pairList_append, pairList_cons], ?_⟩
    · intro s hs
      simp only [List.mem_append, List.mem_cons] at hs
      rcases hs with hs | rfl | hs
      · exact hm₁ s (by simp [hs])
      · exact ⟨X.mul_mem (X.mul_mem hp.1 hpX) hq.1, hq.2⟩
      · exact hm₂ s hs
    · rw [wprod_pinch φ h _ (-1) p.2 q.1 _ p.2 (conj_centralizing V (-1) p.2 hgu)]
      rw [pairList_append, pairList_cons, wprod_append, wprod_append, wprod_cons, wprod_cons,
        wprod_cons]
      simp [mul_assoc, wprod_nil]

end Centralizing

section Map

variable {G G' : Type*} [Group G] [Group G'] {A B : Subgroup G} {A' B' : Subgroup G'}
  (φ : A ≃* B) (φ' : A' ≃* B') (f : G →* G') (hfA : ∀ a ∈ A, f a ∈ A')
  (hφ : ∀ a : A, (φ' ⟨f a, hfA a a.2⟩ : G') = f (φ a))

/-- The homomorphism of HNN extensions induced by `f`. -/
noncomputable def hnnMap : HNNExtension G A B φ →* HNNExtension G' A' B' φ' :=
  HNNExtension.lift (of.comp f) t (by
    intro a
    have := t_mul_of (φ := φ') ⟨f a, hfA a a.2⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    rw [this, hφ])

theorem hnnMap_of (g : G) : hnnMap φ φ' f hfA hφ (of g) = of (f g) := by
  simp [hnnMap]

theorem hnnMap_t : hnnMap φ φ' f hfA hφ t = t := by
  simp [hnnMap]

theorem hnnMap_wprod (h : G) (l : List (ℤˣ × G)) :
    hnnMap φ φ' f hfA hφ (wprod φ h l) = wprod φ' (f h) (l.map fun p => (p.1, f p.2)) := by
  simp only [wprod, map_mul, hnnMap_of, map_list_prod, List.map_map]
  congr 2
  apply List.map_congr_left
  intro x _
  simp [hnnMap_of, hnnMap_t]

/-- **Functoriality of HNN extensions**: injective when `f` is injective and
`f⁻¹(A') ⊆ A`, `f⁻¹(B') ⊆ B`. -/
theorem hnnMap_injective (hf : Function.Injective f) (hA' : ∀ g, f g ∈ A' → g ∈ A)
    (hB' : ∀ g, f g ∈ B' → g ∈ B) : Function.Injective (hnnMap φ φ' f hfA hφ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨h, l, rfl, hc⟩ := exists_wprod φ x
  rw [hnnMap_wprod] at hx
  have hc' : (l.map fun p => (p.1, f p.2)).IsChain
      (fun a b => a.2 ∈ toSubgroup A' B' a.1 → a.1 = b.1) := by
    rw [List.isChain_map]
    refine hc.imp fun a b hab ha => hab ?_
    rcases Int.units_eq_one_or a.1 with h1 | h1 <;> rw [h1] at ha ⊢
    · exact hA' _ ha
    · exact hB' _ ha
  have hnil := ReducedWord.toList_eq_nil_of_mem_of_range φ'
    ⟨f h, l.map fun p => (p.1, f p.2), hc'⟩ ⟨1, by rw [map_one]; exact hx.symm⟩
  simp only [List.map_eq_nil_iff] at hnil
  subst hnil
  simp only [List.map_nil, wprod_nil] at hx
  rw [wprod_nil]
  have : f h = 1 := of_injective (φ := φ') (by rw [hx, map_one])
  rw [hf (this.trans (map_one f).symm), map_one]

end Map

end TheoremA.Britton
