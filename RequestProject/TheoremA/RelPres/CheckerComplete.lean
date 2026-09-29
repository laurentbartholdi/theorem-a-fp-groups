module

public import RequestProject.TheoremA.RelPres.CheckerSound

/-!
# Completeness of the certificate checker

* `exists_certifies` — every terminating evaluation `y ∈ eval R c x` has a finite certificate,
  built by induction on `c` (with inner inductions for `prec` and for the `rfind` prefix
  chain) from `certifies_leaf`, `certifies_one` and `certifies_two`.
* `mem_eval_iff_exists_check` — `y ∈ eval R (decode c) x ↔ ∃ cert, check R c x y cert = true`.
-/

@[expose] public section

namespace TheoremA.RelPres

open OracleCode

variable {R : Set ℕ}

/-- The mode-`1` prefix chain for `rfind f`: if the body terminates with nonzero values at all
candidates below `k`, there is a certificate for the head `(encode (rfind f), x, k, 1)`. -/
theorem exists_certifies_rfind_prefix (f : OracleCode)
    (ihf : ∀ x y, y ∈ eval R f x → ∃ L, Certifies R L (encode f, x, y, 0)) (x : ℕ) :
    ∀ k, (∀ j < k, ∃ v ∈ eval R f (Nat.pair x j), v ≠ 0) →
      ∃ L, Certifies R L (encode (rfind f), x, k, 1) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨_, certifies_leaf ?_⟩
    simp [localCheck]
  | succ k ih =>
    intro hk
    obtain ⟨L₁, c₁⟩ := ih fun j hj => hk j (by omega)
    obtain ⟨v, hv, hv0⟩ := hk k (by omega)
    obtain ⟨L₂, c₂⟩ := ihf _ _ hv
    refine ⟨_, certifies_two c₁ c₂ ?_⟩
    simp [localCheck, Nat.pos_of_ne_zero hv0]

/-- **Completeness**: every terminating evaluation has a finite certificate. -/
theorem exists_certifies (c : OracleCode) :
    ∀ x y, y ∈ eval R c x → ∃ L, Certifies R L (encode c, x, y, 0) := by
  induction c with
  | zero =>
    intro x y hy
    obtain rfl : y = 0 := by simpa using hy
    exact ⟨_, certifies_leaf (by simp [localCheck, encode, codeTag])⟩
  | succ =>
    intro x y hy
    obtain rfl : y = x + 1 := by simpa using hy
    exact ⟨_, certifies_leaf (by simp [localCheck, encode, codeTag])⟩
  | left =>
    intro x y hy
    obtain rfl : y = (Nat.unpair x).1 := by simpa using hy
    exact ⟨_, certifies_leaf (by simp [localCheck, encode, codeTag])⟩
  | right =>
    intro x y hy
    obtain rfl : y = (Nat.unpair x).2 := by simpa using hy
    exact ⟨_, certifies_leaf (by simp [localCheck, encode, codeTag])⟩
  | query =>
    intro x y hy
    obtain rfl : y = chiNat R x := by simpa [chi_eq_some] using hy
    exact ⟨_, certifies_leaf (by simp [localCheck, encode, codeTag])⟩
  | pair f g ihf ihg =>
    intro x y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_eval_pair.1 hy
    obtain ⟨L₁, c₁⟩ := ihf _ _ ha
    obtain ⟨L₂, c₂⟩ := ihg _ _ hb
    exact ⟨_, certifies_two c₁ c₂ (by simp [localCheck])⟩
  | comp f g ihf ihg =>
    intro x y hy
    obtain ⟨z, hz, hy⟩ := mem_eval_comp.1 hy
    obtain ⟨L₁, c₁⟩ := ihg _ _ hz
    obtain ⟨L₂, c₂⟩ := ihf _ _ hy
    exact ⟨_, certifies_two c₁ c₂ (by simp [localCheck])⟩
  | prec f g ihf ihg =>
    intro x
    rw [← Nat.pair_unpair x]
    generalize (Nat.unpair x).1 = a
    generalize (Nat.unpair x).2 = n
    induction n with
    | zero =>
      intro y hy
      rw [eval_prec_zero] at hy
      obtain ⟨L₁, c₁⟩ := ihf _ _ hy
      exact ⟨_, certifies_one c₁ (by simp [localCheck, Nat.unpair_pair])⟩
    | succ n ihn =>
      intro y hy
      obtain ⟨i, hi, hy⟩ := mem_eval_prec_succ.1 hy
      obtain ⟨L₁, c₁⟩ := ihn _ hi
      obtain ⟨L₂, c₂⟩ := ihg _ _ hy
      exact ⟨_, certifies_two c₁ c₂ (by simp [localCheck, Nat.unpair_pair])⟩
  | rfind f ihf =>
    intro x y hy
    obtain ⟨h0, hlt⟩ := mem_eval_rfind.1 hy
    obtain ⟨L₁, c₁⟩ := exists_certifies_rfind_prefix f ihf x y hlt
    obtain ⟨L₂, c₂⟩ := ihf _ _ h0
    exact ⟨_, certifies_two c₁ c₂ (by simp [localCheck])⟩

theorem nodesOf_encode (L : List CertNode) : nodesOf (Encodable.encode L) = L := by
  simp [nodesOf]

/-- **Soundness and completeness of the checker.** -/
theorem mem_eval_iff_exists_check {c x y : ℕ} :
    y ∈ eval R (decode c) x ↔ ∃ cert, check R c x y cert = true := by
  constructor
  · intro h
    obtain ⟨L, hg, h0, hh⟩ := exists_certifies (decode c) x y h
    rw [encode_decode] at hh
    refine ⟨Encodable.encode L, check_eq_true_iff.2 ?_⟩
    rw [nodesOf_encode]
    exact ⟨hg, h0, hh⟩
  · rintro ⟨cert, h⟩
    exact mem_eval_of_check h

end TheoremA.RelPres
