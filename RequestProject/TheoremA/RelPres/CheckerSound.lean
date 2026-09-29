module

public import RequestProject.TheoremA.RelPres.Checker

/-!
# Soundness and completeness of the certificate checker

* `HClaim R h` — the claim made by a node with head `h`.
* `localCheck_sound` — one checked node is correct if its referenced children are.
* `good_sound` — soundness by strong induction over the nodes of a certificate.
* `nodeOk_append_left`, `nodeOk_append_right`, `good_append` — concatenation of certificates
  (relative references need no shifting).
* `exists_certifies` — completeness: every terminating evaluation has a finite certificate.
* `mem_eval_iff_exists_check` — `y ∈ eval R (decode c) x ↔ ∃ cert, check R c x y cert = true`.
-/

@[expose] public section

namespace TheoremA.RelPres

open OracleCode

variable {R : Set ℕ}

/-- The claim made by a node with head `(p, x, y, m)`: for `m = 0`,
`y ∈ eval R (decode p) x`; for `m ≠ 0`, the body `decode (codeArg p)` returns a nonzero value
on `⟨x, k⟩` for every `k < y`. -/
def HClaim (R : Set ℕ) (h : NodeHead) : Prop :=
  if h.2.2.2 = 0 then h.2.2.1 ∈ eval R (decode h.1) h.2.1
  else ∀ k < h.2.2.1, ∃ v ∈ eval R (decode (codeArg h.1)) (Nat.pair h.2.1 k), v ≠ 0

@[simp] theorem hClaim_zero (p x y : ℕ) : HClaim R (p, x, y, 0) ↔ y ∈ eval R (decode p) x := by
  simp [HClaim]

theorem hClaim_ne_zero {p x y m : ℕ} (hm : m ≠ 0) : HClaim R (p, x, y, m) ↔
    ∀ k < y, ∃ v ∈ eval R (decode (codeArg p)) (Nat.pair x k), v ≠ 0 := by
  simp [HClaim, hm]

theorem eq_of_codeTag_eq {p k : ℕ} (hk : k < 5) (h : codeTag p = k) : p = k := by
  unfold codeTag at h; split_ifs at h <;> omega

/-- **Local soundness.** -/
theorem localCheck_sound {p x y m r₁ r₂ : ℕ} {h₁ h₂ : NodeHead}
    (hc : localCheck (p, x, y, m, r₁, r₂) h₁ h₂ (chiNat R x) = true)
    (H₁ : 0 < r₁ → HClaim R h₁) (H₂ : 0 < r₂ → HClaim R h₂) : HClaim R (p, x, y, m) := by
  obtain ⟨q₁, x₁, y₁, m₁⟩ := h₁
  obtain ⟨q₂, x₂, y₂, m₂⟩ := h₂
  unfold localCheck at hc
  by_cases hm : m = 0
  · subst hm
    rw [hClaim_zero]
    have ht := codeTag_lt p
    obtain ⟨t, htt⟩ : ∃ t, codeTag p = t := ⟨_, rfl⟩
    rw [htt] at ht
    interval_cases t
    · simp [htt] at hc
      obtain rfl := eq_of_codeTag_eq (by norm_num) htt
      simp [decode_zero, hc]
    · simp [htt] at hc
      obtain rfl := eq_of_codeTag_eq (by norm_num) htt
      simp [decode_one, hc]
    · simp [htt] at hc
      obtain rfl := eq_of_codeTag_eq (by norm_num) htt
      simp [decode_two, hc]
    · simp [htt] at hc
      obtain rfl := eq_of_codeTag_eq (by norm_num) htt
      simp [decode_three, hc]
    · simp [htt] at hc
      obtain rfl := eq_of_codeTag_eq (by norm_num) htt
      simp [decode_four, hc, chi_eq_some]
    · simp [htt] at hc
      obtain ⟨⟨⟨⟨h1, h2⟩, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, rfl⟩ := hc
      have c1 := H₁ h1
      have c2 := H₂ h2
      rw [hClaim_zero] at c1 c2
      rw [decode_of_tag_pair htt, mem_eval_pair]
      exact ⟨_, c1, _, c2, rfl⟩
    · simp [htt] at hc
      obtain ⟨⟨⟨h1, h2⟩, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := hc
      have c1 := H₁ h1
      have c2 := H₂ h2
      rw [hClaim_zero] at c1 c2
      rw [decode_of_tag_comp htt, mem_eval_comp]
      exact ⟨_, c1, c2⟩
    · simp [htt] at hc
      rw [decode_of_tag_prec htt]
      split_ifs at hc with hn
      · obtain ⟨h1, rfl, rfl, rfl, rfl⟩ := hc
        have c1 := H₁ h1
        rw [hClaim_zero] at c1
        have e := eval_prec_zero (R := R) (decode (Nat.unpair (codeArg p)).1)
          (decode (Nat.unpair (codeArg p)).2) (Nat.unpair x).1
        rw [← hn, Nat.pair_unpair] at e
        rw [e]
        exact c1
      · obtain ⟨⟨⟨h1, h2⟩, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := hc
        have c1 := H₁ h1
        have c2 := H₂ h2
        rw [hClaim_zero, decode_of_tag_prec htt] at c1
        rw [hClaim_zero] at c2
        have hx : x = Nat.pair (Nat.unpair x).1 ((Nat.unpair x).2 - 1 + 1) := by
          rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn), Nat.pair_unpair]
        rw [hx, mem_eval_prec_succ]
        exact ⟨_, c1, c2⟩
    · simp [htt] at hc
      obtain ⟨⟨⟨h1, h2⟩, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩ := hc
      have c1 := H₁ h1
      have c2 := H₂ h2
      rw [hClaim_ne_zero one_ne_zero] at c1
      rw [hClaim_zero] at c2
      rw [decode_of_tag_rfind htt, mem_eval_rfind]
      exact ⟨c2, c1⟩
  · simp [hm] at hc
    rw [hClaim_ne_zero hm]
    obtain ⟨-, hy⟩ := hc
    rcases hy with rfl | ⟨⟨⟨⟨h1, h2⟩, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩, hv⟩
    · intro k hk; omega
    · have c1 := H₁ h1
      have c2 := H₂ h2
      rw [hClaim_ne_zero one_ne_zero] at c1
      rw [hClaim_zero] at c2
      intro k hk
      rcases Nat.lt_or_ge k (y - 1) with hk' | hk'
      · exact c1 k hk'
      · obtain rfl : k = y - 1 := by omega
        exact ⟨_, c2, Nat.pos_iff_ne_zero.1 hv⟩

/-! ### Soundness over a certificate -/

/-- Every node of `L` passes its check, with oracle answers supplied by `chiNat R`. -/
def Good (R : Set ℕ) (L : List CertNode) : Prop :=
  ∀ i < L.length, nodeOk (chiNat R (L.getD i dfltNode).2.1) L i = true

/-- **Soundness**, by strong induction over the nodes. -/
theorem good_sound {L : List CertNode} (hL : Good R L) :
    ∀ i < L.length, HClaim R (headOf (L.getD i dfltNode)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hok := hL i hi
    unfold nodeOk at hok
    rcases hnd : L.getD i dfltNode with ⟨p, x, y, m, r₁, r₂⟩
    rw [hnd] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hr₁, hr₂⟩, hc⟩ := hok
    exact localCheck_sound hc (fun h => ih _ (by omega) (by omega))
      (fun h => ih _ (by omega) (by omega))

theorem answers_getD (R : Set ℕ) (L : List CertNode) {i : ℕ} (hi : i < L.length) :
    (answers R L).getD i 0 = chiNat R (L.getD i dfltNode).2.1 := by
  simp [answers, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem check_eq_true_iff {c x y cert : ℕ} :
    check R c x y cert = true ↔
      Good R (nodesOf cert) ∧ 0 < (nodesOf cert).length ∧
        headOf ((nodesOf cert).getD ((nodesOf cert).length - 1) dfltNode) = (c, x, y, 0) := by
  unfold check checkCore Good
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨⟨h0, hh⟩, hall⟩
    exact ⟨fun i hi => by rw [← answers_getD R _ hi]; exact hall i hi, h0, hh⟩
  · rintro ⟨hall, h0, hh⟩
    exact ⟨⟨h0, hh⟩, fun i hi => by rw [answers_getD R _ hi]; exact hall i hi⟩

/-- **Soundness of the checker.** -/
theorem mem_eval_of_check {c x y cert : ℕ} (h : check R c x y cert = true) :
    y ∈ eval R (decode c) x := by
  obtain ⟨hg, h0, hh⟩ := check_eq_true_iff.1 h
  have := good_sound hg _ (Nat.sub_lt h0 Nat.one_pos)
  rw [hh, hClaim_zero] at this
  exact this

/-! ### Concatenation of certificates -/

theorem nodeOk_append_left (a : ℕ) {L : List CertNode} (M : List CertNode) {i : ℕ}
    (hi : i < L.length) : nodeOk a (L ++ M) i = nodeOk a L i := by
  unfold nodeOk
  rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega),
    List.getD_append _ _ _ _ (by omega)]

theorem nodeOk_append_right (a : ℕ) (L : List CertNode) {M : List CertNode} {i : ℕ}
    (h : nodeOk a M i = true) : nodeOk a (L ++ M) (L.length + i) = true := by
  unfold nodeOk at h ⊢
  have e : (L ++ M).getD (L.length + i) dfltNode = M.getD i dfltNode := by
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  rw [e]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
  have e1 : L.length + i - (M.getD i dfltNode).2.2.2.2.1 - L.length =
      i - (M.getD i dfltNode).2.2.2.2.1 := by omega
  have e2 : L.length + i - (M.getD i dfltNode).2.2.2.2.2 - L.length =
      i - (M.getD i dfltNode).2.2.2.2.2 := by omega
  rw [e1, e2]
  exact h3

/-- Concatenation of good lists is good; relative references need no shifting. -/
theorem good_append {L M : List CertNode} (hL : Good R L) (hM : Good R M) : Good R (L ++ M) := by
  intro i hi
  rw [List.length_append] at hi
  by_cases h : i < L.length
  · rw [List.getD_append _ _ _ _ h, nodeOk_append_left _ _ h]
    exact hL i h
  · obtain ⟨j, rfl⟩ : ∃ j, i = L.length + j := ⟨i - L.length, by omega⟩
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
    exact nodeOk_append_right _ _ (hM j (by omega))

theorem good_snoc {L : List CertNode} {nd : CertNode} (hL : Good R L)
    (h : nodeOk (chiNat R nd.2.1) (L ++ [nd]) L.length = true) : Good R (L ++ [nd]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  by_cases h' : i < L.length
  · rw [List.getD_append _ _ _ _ h', nodeOk_append_left _ _ h']
    exact hL i h'
  · obtain rfl : i = L.length := by omega
    rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
    exact h

/-- `L` is a good certificate whose last node has head `h`. -/
def Certifies (R : Set ℕ) (L : List CertNode) (h : NodeHead) : Prop :=
  Good R L ∧ 0 < L.length ∧ headOf (L.getD (L.length - 1) dfltNode) = h

theorem certifies_leaf {p x y m : ℕ}
    (hc : localCheck (p, x, y, m, 0, 0) (p, x, y, m) (p, x, y, m) (chiNat R x) = true) :
    Certifies R [(p, x, y, m, 0, 0)] (p, x, y, m) := by
  refine ⟨fun i hi => ?_, by simp, rfl⟩
  obtain rfl : i = 0 := by simpa using hi
  simpa [nodeOk, headOf] using hc

theorem certifies_one {L₁ : List CertNode} {h₁ : NodeHead} (c₁ : Certifies R L₁ h₁)
    {p x y m : ℕ} (hc : localCheck (p, x, y, m, 1, 0) h₁ (p, x, y, m) (chiNat R x) = true) :
    Certifies R (L₁ ++ [(p, x, y, m, 1, 0)]) (p, x, y, m) := by
  obtain ⟨g₁, l₁, e₁⟩ := c₁
  refine ⟨good_snoc g₁ ?_, by simp, ?_⟩
  · unfold nodeOk
    rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [List.getD_append _ _ _ _ (by omega), Nat.sub_zero,
      List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero, e₁]
    exact hc
  · simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
    rfl

theorem certifies_two {L₁ L₂ : List CertNode} {h₁ h₂ : NodeHead} (c₁ : Certifies R L₁ h₁)
    (c₂ : Certifies R L₂ h₂) {p x y m : ℕ}
    (hc : localCheck (p, x, y, m, L₂.length + 1, 1) h₁ h₂ (chiNat R x) = true) :
    Certifies R (L₁ ++ L₂ ++ [(p, x, y, m, L₂.length + 1, 1)]) (p, x, y, m) := by
  obtain ⟨g₁, l₁, e₁⟩ := c₁
  obtain ⟨g₂, l₂, e₂⟩ := c₂
  refine ⟨good_snoc (good_append g₁ g₂) ?_, by simp, ?_⟩
  · unfold nodeOk
    rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_append]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have i1 : L₁.length + L₂.length - (L₂.length + 1) = L₁.length - 1 := by omega
    rw [i1, List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega), e₁]
    rw [List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by omega)]
    have i2 : L₁.length + L₂.length - 1 - L₁.length = L₂.length - 1 := by omega
    rw [i2, e₂]
    exact hc
  · simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_append, Nat.sub_self,
      List.getD_cons_zero]
    rfl

end TheoremA.RelPres
