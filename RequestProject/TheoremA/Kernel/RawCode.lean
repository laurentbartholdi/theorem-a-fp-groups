module

public import RequestProject.TheoremA.RelPres.Class

/-!
# Decimal coding of raw words on `a, b, a⁻¹, b⁻¹`

Raw words (not reduced words) over `Fin 2`.  The letters get the digits
`a ↦ 1`, `b ↦ 2`, `a⁻¹ ↦ 3`, `b⁻¹ ↦ 4`, and

    code [] = 0,     code (w ++ [λ]) = 10 * code w + digit λ.

* `code_append_single`, `code_nil`;
* `code_injective` — injectivity on raw words;
* `mod_ten_code_eq_digit_iff` — the last-digit property: `code w % 10 = digit λ` iff `w` ends
  with the letter `λ`;
* `primrec_code` — `code` is primitive recursive for the structural coding of raw words.
-/

@[expose] public section

namespace TheoremA.Kernel

open TheoremA.RelPres

/-- The digit of a letter: `a ↦ 1`, `b ↦ 2`, `a⁻¹ ↦ 3`, `b⁻¹ ↦ 4`. -/
def digit (p : Fin 2 × Bool) : ℕ := if p.2 then p.1.val + 1 else p.1.val + 3

theorem digit_pos (p : Fin 2 × Bool) : 1 ≤ digit p := by
  unfold digit; split_ifs <;> omega

theorem digit_le (p : Fin 2 × Bool) : digit p ≤ 4 := by
  unfold digit; have := p.1.isLt; split_ifs <;> omega

theorem digit_injective : Function.Injective digit := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  unfold digit at h
  have := a.isLt; have := a'.isLt
  cases b <;> cases b' <;> simp at h <;> first | omega | (congr 1; exact Fin.ext (by omega))

/-- The decimal code of a raw word. -/
def code (w : RawWord (Fin 2)) : ℕ := w.foldl (fun n p => 10 * n + digit p) 0

@[simp] theorem code_nil : code [] = 0 := rfl

theorem code_append_single (w : RawWord (Fin 2)) (p : Fin 2 × Bool) :
    code (w ++ [p]) = 10 * code w + digit p := by
  simp [code, List.foldl_append]

theorem code_pos_of_ne_nil {w : RawWord (Fin 2)} (hw : w ≠ []) : 0 < code w := by
  obtain ⟨u, p, rfl⟩ := List.eq_nil_or_concat w |>.resolve_left hw
  rw [List.concat_eq_append, code_append_single]; have := digit_pos p; omega

theorem code_eq_zero_iff {w : RawWord (Fin 2)} : code w = 0 ↔ w = [] := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  by_contra hw; have := code_pos_of_ne_nil hw; omega

/-- **Injectivity of the coding on raw words.** -/
theorem code_injective : Function.Injective code := by
  intro w
  induction w using List.reverseRecOn with
  | nil => intro w' h; exact (code_eq_zero_iff.1 h.symm).symm
  | append_singleton u p ih =>
    intro w' h
    rcases List.eq_nil_or_concat w' with rfl | ⟨u', p', rfl⟩
    · exact absurd h (code_pos_of_ne_nil (by simp)).ne'
    · simp only [List.concat_eq_append] at h ⊢
      rw [code_append_single, code_append_single] at h
      have h1 := digit_le p; have h2 := digit_le p'
      have h3 := digit_pos p; have h4 := digit_pos p'
      have hd : digit p = digit p' := by omega
      have hc : code u = code u' := by omega
      rw [ih hc, digit_injective hd]

/-- **The last-digit property.** -/
theorem mod_ten_code_eq_digit_iff (w : RawWord (Fin 2)) (p : Fin 2 × Bool) :
    code w % 10 = digit p ↔ ∃ u, w = u ++ [p] := by
  constructor
  · intro h
    rcases List.eq_nil_or_concat w with rfl | ⟨u, q, rfl⟩
    · have := digit_pos p; simp at h; omega
    · simp only [List.concat_eq_append] at h ⊢
      rw [code_append_single] at h
      have := digit_le q; have := digit_pos q
      have hd : digit q = digit p := by omega
      exact ⟨u, by rw [digit_injective hd]⟩
  · rintro ⟨u, rfl⟩
    rw [code_append_single]; have := digit_le p; omega

theorem primrec_digit : Primrec digit := Primrec.dom_finite digit

/-- **`code` is primitive recursive.** -/
theorem primrec_code : Primrec code := by
  have hstep : Primrec₂ fun (n : ℕ) (p : Fin 2 × Bool) => 10 * n + digit p :=
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10) Primrec.fst)
      (primrec_digit.comp Primrec.snd)).to₂
  exact Primrec.list_foldl Primrec.id (Primrec.const 0)
    (hstep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

end TheoremA.Kernel
