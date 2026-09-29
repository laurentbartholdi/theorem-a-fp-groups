module

public import RequestProject.TheoremA.RelPres.Class

/-!
# The raw-word bridge: one fixed output syntax `RawWord ℕ`

Machine outputs are always read as codes of raw words on the natural-number alphabet, using the
structural `Primcodable` coding of `List (ℕ × Bool)`.  This coding does not depend on any finite
alphabet size.

* `RawWord.up n w` — rename a word on `Fin n` by `Fin.val`.
* `RawWord.bounded n w` — every letter index of `w` is `< n` (Boolean version `boundedB`).
* `RawWord.down n w` — the partial restriction `RawWord ℕ → Option (RawWord (Fin n))`.
* round trips: `down_up`, `up_of_down_eq_some`, `down_isSome_iff`, `down_nil`.
* coding: `restrictCode` (decode + bounds check, **uniform** in `n` and the code,
  `primrec_restrictCode`), and for each fixed `n` the conversions `natCodeOfFinCode`,
  `finCodeOfNatCode` between finite-alphabet codes and natural-alphabet codes.
-/

@[expose] public section

namespace TheoremA.RelPres

/-- Encoding of raw words on the natural-number alphabet (structural `Primcodable` coding). -/
def encodeRawWordNat (w : RawWord ℕ) : ℕ := Encodable.encode w

/-- Decoding of raw words on the natural-number alphabet (`none` on invalid codes). -/
def decodeRawWordNat (z : ℕ) : Option (RawWord ℕ) := Encodable.decode z

@[simp] theorem decodeRawWordNat_encode (w : RawWord ℕ) :
    decodeRawWordNat (encodeRawWordNat w) = some w := Encodable.encodek w

theorem primrec_encodeRawWordNat : Primrec encodeRawWordNat := Primrec.encode

theorem primrec_decodeRawWordNat : Primrec decodeRawWordNat := Primrec.decode

theorem encodeRawWordNat_injective : Function.Injective encodeRawWordNat :=
  Encodable.encode_injective

namespace RawWord

/-- Rename a word on `Fin n` to a word on `ℕ` by `Fin.val`. -/
def up (n : ℕ) (w : RawWord (Fin n)) : RawWord ℕ := rename Fin.val w

/-- Every letter index occurring in `w` is `< n`. -/
def bounded (n : ℕ) (w : RawWord ℕ) : Prop := ∀ p ∈ w, p.1 < n

instance (n : ℕ) : DecidablePred (bounded n) := fun w =>
  inferInstanceAs (Decidable (∀ p ∈ w, p.1 < n))

/-- Boolean version of `bounded`, written as a fold (for primitive recursiveness). -/
def boundedB (n : ℕ) (w : RawWord ℕ) : Bool := w.foldr (fun p b => decide (p.1 < n) && b) true

theorem boundedB_iff (n : ℕ) (w : RawWord ℕ) : boundedB n w = true ↔ bounded n w := by
  induction w with
  | nil => simp [boundedB, bounded]
  | cons p w ih =>
    simp only [boundedB, List.foldr_cons, Bool.and_eq_true, decide_eq_true_eq] at ih ⊢
    rw [ih]; simp [bounded]

/-- `Fin n`-valued partial reading of a natural number. -/
def finOpt (n a : ℕ) : Option (Fin n) := if h : a < n then some ⟨a, h⟩ else none

theorem finOpt_eq_decode₂ (n a : ℕ) : finOpt n a = Encodable.decode₂ (Fin n) a := by
  unfold finOpt
  split_ifs with h
  · exact (Encodable.mem_decode₂.2 rfl).symm
  · rcases hx : Encodable.decode₂ (Fin n) a with _ | x
    · rfl
    · have := Encodable.mem_decode₂.1 hx
      exact absurd (this ▸ x.2) h

/-- Letterwise restriction. -/
def letterDown (n : ℕ) (p : ℕ × Bool) : Option (Fin n × Bool) :=
  (finOpt n p.1).map fun a => (a, p.2)

/-- **The partial restriction** `down_n : RawWord ℕ → Option (RawWord (Fin n))`: the word with
its indices read in `Fin n` if `bounded n w`, and `none` otherwise. -/
def down (n : ℕ) (w : RawWord ℕ) : Option (RawWord (Fin n)) :=
  if bounded n w then some (w.filterMap (letterDown n)) else none

@[simp] theorem up_nil (n : ℕ) : up n [] = [] := rfl

theorem bounded_up (n : ℕ) (w : RawWord (Fin n)) : bounded n (up n w) := by
  intro p hp
  simp only [up, rename, List.mem_map] at hp
  obtain ⟨q, -, rfl⟩ := hp
  exact q.1.2

theorem filterMap_letterDown_up (n : ℕ) (w : RawWord (Fin n)) :
    (up n w).filterMap (letterDown n) = w := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    simp only [up, rename, List.map_cons] at ih ⊢
    rw [List.filterMap_cons_some (b := p)]
    · rw [ih]
    · simp [letterDown, finOpt, p.1.2]

/-- **Round trip** `down_n (up_n w) = some w`. -/
@[simp] theorem down_up (n : ℕ) (w : RawWord (Fin n)) : down n (up n w) = some w := by
  simp [down, bounded_up, filterMap_letterDown_up]

theorem up_filterMap_letterDown (n : ℕ) (w : RawWord ℕ) (h : bounded n w) :
    up n (w.filterMap (letterDown n)) = w := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    have hp : p.1 < n := h p (by simp)
    have hw : bounded n w := fun q hq => h q (by simp [hq])
    rw [List.filterMap_cons_some (b := (⟨p.1, hp⟩, p.2))]
    · simp only [up, rename, List.map_cons] at ih ⊢
      rw [ih hw]
    · simp [letterDown, finOpt, hp]

/-- **Forgetting the indices of a successful restriction recovers the word.** -/
theorem up_of_down_eq_some {n : ℕ} {w : RawWord ℕ} {v : RawWord (Fin n)}
    (h : down n w = some v) : up n v = w := by
  unfold down at h
  split_ifs at h with hb
  cases h
  exact up_filterMap_letterDown n w hb

theorem down_isSome_iff (n : ℕ) (w : RawWord ℕ) : (down n w).isSome ↔ bounded n w := by
  unfold down; split_ifs with h <;> simp [h]

theorem down_eq_none_iff (n : ℕ) (w : RawWord ℕ) : down n w = none ↔ ¬ bounded n w := by
  unfold down; split_ifs with h <;> simp [h]

theorem down_eq_some_iff (n : ℕ) (w : RawWord ℕ) (v : RawWord (Fin n)) :
    down n w = some v ↔ up n v = w := by
  constructor
  · exact up_of_down_eq_some
  · rintro rfl; exact down_up n v

/-- The empty word is valid for every `n`, including `n = 0`. -/
@[simp] theorem down_nil (n : ℕ) : down n [] = some [] := down_up n []

theorem up_injective (n : ℕ) : Function.Injective (up n) := by
  intro v v' h
  have := down_up n v
  rw [h, down_up] at this
  exact (Option.some.inj this).symm

theorem eval_up (n : ℕ) (w : RawWord (Fin n)) :
    eval (up n w) = FreeGroup.map Fin.val (eval w) := eval_rename _ _

/-! ### Primitive recursiveness -/

theorem primrec_boundedB : Primrec₂ boundedB := by
  have : Primrec fun a : ℕ × RawWord ℕ =>
      a.2.foldr (fun p b => (fun a q => decide (q.1.1 < a.1) && q.2) a (p, b)) true :=
    Primrec.list_foldr Primrec.snd (Primrec.const true)
      (Primrec.and.comp
        (Primrec.nat_lt.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.fst.comp Primrec.fst)).decide
        (Primrec.snd.comp Primrec.snd)).to₂
  exact this.of_eq fun a => rfl

theorem primrec_up (n : ℕ) : Primrec (up n) :=
  Primrec.list_map Primrec.id
    (Primrec.pair (Primrec.fin_val.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

theorem primrec_letterDown (n : ℕ) : Primrec (letterDown n) := by
  have h1 : Primrec fun p : ℕ × Bool => finOpt n p.1 := by
    simp only [finOpt_eq_decode₂]
    exact Primrec.decode₂.comp Primrec.fst
  exact Primrec.option_map h1 (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂

theorem primrec_down (n : ℕ) : Primrec (down n) := by
  have hf : Primrec fun w : RawWord ℕ => w.filterMap (letterDown n) :=
    Primrec.listFilterMap Primrec.id ((primrec_letterDown n).comp Primrec.snd).to₂
  have hb : Primrec fun w => boundedB n w := primrec_boundedB.comp (Primrec.const n) Primrec.id
  have := Primrec.cond hb (Primrec.option_some.comp hf) (Primrec.const none)
  refine this.of_eq fun w => ?_
  unfold down
  by_cases h : bounded n w
  · simp [h, (boundedB_iff n w).2 h]
  · have : boundedB n w = false := by
      rw [← Bool.not_eq_true, boundedB_iff]; exact h
    simp [h, this]

end RawWord

open RawWord

/-! ### Coding facts -/

/-- Decode a `RawWord ℕ` code and keep the word iff it is `bounded n`. -/
def restrictCode (n z : ℕ) : Option (RawWord ℕ) :=
  (decodeRawWordNat z).bind fun w => if bounded n w then some w else none

/-- **Uniformity**: decoding, checking `bounded n` and retaining the word is primitive recursive
jointly in `n` and the code. -/
theorem primrec_restrictCode : Primrec₂ restrictCode := by
  have := Primrec.option_bind (primrec_decodeRawWordNat.comp Primrec.snd)
    (Primrec.cond (primrec_boundedB.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂
  refine this.of_eq fun a => ?_
  simp only [restrictCode]
  congr 1; funext w
  by_cases h : bounded a.1 w
  · simp [h, (boundedB_iff _ w).2 h]
  · have : boundedB a.1 w = false := by
      rw [← Bool.not_eq_true, boundedB_iff]; exact h
    simp [h, this]

theorem restrictCode_eq (n z : ℕ) :
    restrictCode n z = ((decodeRawWordNat z).bind (down n)).map (up n) := by
  unfold restrictCode
  cases decodeRawWordNat z with
  | none => rfl
  | some w =>
    simp only [Option.bind_some]
    by_cases h : bounded n w
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 ((down_isSome_iff n w).2 h)
      simp [h, hv, up_of_down_eq_some hv]
    · simp [h, (down_eq_none_iff n w).2 h]

/-- Natural-alphabet code of a finite-alphabet code (for a fixed `n`). -/
def natCodeOfFinCode (n z : ℕ) : Option ℕ :=
  (Encodable.decode z : Option (RawWord (Fin n))).map fun w => encodeRawWordNat (up n w)

/-- Finite-alphabet code of a valid natural-alphabet code (for a fixed `n`). -/
def finCodeOfNatCode (n z : ℕ) : Option ℕ :=
  ((decodeRawWordNat z).bind (down n)).map Encodable.encode

theorem primrec_natCodeOfFinCode (n : ℕ) : Primrec (natCodeOfFinCode n) :=
  Primrec.option_map Primrec.decode
    (primrec_encodeRawWordNat.comp ((primrec_up n).comp Primrec.snd)).to₂

theorem primrec_finCodeOfNatCode (n : ℕ) : Primrec (finCodeOfNatCode n) :=
  Primrec.option_map (Primrec.option_bind primrec_decodeRawWordNat
      ((primrec_down n).comp Primrec.snd).to₂)
    (Primrec.encode.comp Primrec.snd).to₂

@[simp] theorem natCodeOfFinCode_encode (n : ℕ) (w : RawWord (Fin n)) :
    natCodeOfFinCode n (Encodable.encode w) = some (encodeRawWordNat (up n w)) := by
  simp [natCodeOfFinCode]

@[simp] theorem finCodeOfNatCode_encode_up (n : ℕ) (w : RawWord (Fin n)) :
    finCodeOfNatCode n (encodeRawWordNat (up n w)) = some (Encodable.encode w) := by
  simp [finCodeOfNatCode]

theorem finCodeOfNatCode_encode_of_not_bounded (n : ℕ) (w : RawWord ℕ) (h : ¬ bounded n w) :
    finCodeOfNatCode n (encodeRawWordNat w) = none := by
  simp [finCodeOfNatCode, (down_eq_none_iff n w).2 h]

end TheoremA.RelPres
