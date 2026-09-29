module

public import RequestProject.TheoremA.RelPres.Family

/-!
# The explicit natural-number presentation of `Ω_R`

* `tag n c a = ⟪⟪n, c⟫, a⟫` with decoding `labelN`, `labelC`, `labelA`; `ValidLabel q` means
  `labelA q < labelN q`.
* `omegaRels R` — every relator of `G_(n,c)` renamed by `a ↦ tag n c a`, together with the
  one-letter relator `q` for every invalid label `q`.
* `omegaEnum R` — the concrete partial enumerator (even inputs run `W`, odd inputs list the
  invalid labels; parity is tested before `U` is called).
* the natural-alphabet interface `IsNatEnumerator`, `enumRelatorsNat`, `CountablyPresentedIn`.
* `isNatEnumerator_omegaEnum`, `enumRelatorsNat_omegaEnum` (exact relator set),
  `Omega R := PresentedGroup (omegaRels R)` and `countablyPresentedIn_Omega`.
-/

@[expose] public section

namespace TheoremA.RelPres

open RawWord

universe u

variable {R : Set ℕ}

/-! ### Generator labels -/

/-- The natural-number label of the local generator `a` of block `(n, c)`. -/
def tag (n c a : ℕ) : ℕ := Nat.pair (Nat.pair n c) a

/-- Decoded block size of a label. -/
def labelN (q : ℕ) : ℕ := (Nat.unpair (Nat.unpair q).1).1
/-- Decoded program number of a label. -/
def labelC (q : ℕ) : ℕ := (Nat.unpair (Nat.unpair q).1).2
/-- Decoded local letter of a label. -/
def labelA (q : ℕ) : ℕ := (Nat.unpair q).2

@[simp] theorem labelN_tag (n c a : ℕ) : labelN (tag n c a) = n := by simp [labelN, tag]
@[simp] theorem labelC_tag (n c a : ℕ) : labelC (tag n c a) = c := by simp [labelC, tag]
@[simp] theorem labelA_tag (n c a : ℕ) : labelA (tag n c a) = a := by simp [labelA, tag]

@[simp] theorem tag_label (q : ℕ) : tag (labelN q) (labelC q) (labelA q) = q := by
  simp [tag, labelN, labelC, labelA]

theorem tag_injective {n c a n' c' a' : ℕ} (h : tag n c a = tag n' c' a') :
    n = n' ∧ c = c' ∧ a = a' := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg labelN h
  · simpa using congrArg labelC h
  · simpa using congrArg labelA h

/-- A label is valid if its local letter is in range for its block. -/
def ValidLabel (q : ℕ) : Prop := labelA q < labelN q

instance : DecidablePred ValidLabel := fun q => inferInstanceAs (Decidable (labelA q < labelN q))

theorem validLabel_tag {n c a : ℕ} : ValidLabel (tag n c a) ↔ a < n := by simp [ValidLabel]

theorem primrec_labelN : Primrec labelN :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
theorem primrec_labelC : Primrec labelC :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
theorem primrec_labelA : Primrec labelA := Primrec.snd.comp Primrec.unpair

theorem primrecPred_validLabel : PrimrecPred ValidLabel :=
  Primrec.nat_lt.comp primrec_labelA primrec_labelN

/-! ### The relator set -/

/-- **The relators of `Ω_R`**: all tagged copies of relators of the blocks `G_(n,c)`, and the
one-letter relators `q` for invalid labels `q`. -/
def omegaRels (R : Set ℕ) : Set (FreeGroup ℕ) :=
  {x | ∃ n c, ∃ r ∈ famRels R n c, FreeGroup.map (fun a : Fin n => tag n c a) r = x} ∪
    {x | ∃ q, ¬ ValidLabel q ∧ FreeGroup.of q = x}

/-- Tagging of a natural-alphabet word for block `(n, c)`, preserving signs. -/
def tagWord (n c : ℕ) (w : RawWord ℕ) : RawWord ℕ := rename (tag n c) w

theorem tagWord_up (n c : ℕ) (v : RawWord (Fin n)) :
    tagWord n c (up n v) = rename (fun a : Fin n => tag n c a) v := by
  simp [tagWord, up, rename, List.map_map, Function.comp_def]

/-- **The concrete enumerator `E_Ω`.**  Parity is tested first.
* `2q`: with `q = ⟪⟪n, c⟫, k⟫`, run `W R n c k` and tag the result for block `(n, c)`;
* `2q+1`: output `[q]` if the label `q` is invalid, and nothing otherwise. -/
noncomputable def omegaEnum (R : Set ℕ) : ℕ →. RawWord ℕ := fun m =>
  bif m.bodd then
    (((if ValidLabel m.div2 then none else some [(m.div2, true)]) : Option (RawWord ℕ)) : Part _)
  else (Wfun R m.div2).map (tagWord (labelN m.div2) (labelC m.div2))

/-! ### The natural-alphabet presentation interface -/

/-- A partial enumerator of natural-alphabet raw words, recursive in `oracle R` with the
structural coding of `RawWord ℕ`. -/
def IsNatEnumerator (R : Set ℕ) (E : ℕ →. RawWord ℕ) : Prop :=
  RecursiveIn (oracle R) fun k => (E k).map encodeRawWordNat

/-- The interpreted relator set `{eval w | ∃ k, w ∈ E k}` in `FreeGroup ℕ`. -/
def enumRelatorsNat (E : ℕ →. RawWord ℕ) : Set (FreeGroup ℕ) :=
  {x | ∃ k, ∃ w ∈ E k, w.eval = x}

/-- **Countably `R`-presented**: a presentation witness on the natural-number alphabet whose
relators are enumerated relative to `R`. -/
def CountablyPresentedIn (R : Set ℕ) (X : Type u) [Group X] : Prop :=
  ∃ E : ℕ →. RawWord ℕ, IsNatEnumerator R E ∧
    Nonempty (PresentedGroup (enumRelatorsNat E) ≃* X)

/-! ### `E_Ω` is an `R`-enumerator -/

theorem primrec_tagWord : Primrec fun p : (ℕ × ℕ) × RawWord ℕ => tagWord p.1.1 p.1.2 p.2 :=
  Primrec.list_map Primrec.snd
    (Primrec.pair
      (Primrec₂.natPair.comp
        (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

/-- **`E_Ω` is recursive in `oracle R`.**  The only program execution is through `W`. -/
theorem isNatEnumerator_omegaEnum : IsNatEnumerator R (omegaEnum R) := by
  -- odd branch: oracle-free
  have hOddP : Primrec fun m : ℕ =>
      ((if ValidLabel m.div2 then none else some [(m.div2, true)]) : Option (RawWord ℕ)).map
        encodeRawWordNat :=
    Primrec.option_map
      (Primrec.ite (primrecPred_validLabel.comp Primrec.nat_div2) (Primrec.const none)
        (Primrec.option_some.comp (Primrec.list_cons.comp
          (Primrec.pair Primrec.nat_div2 (Primrec.const true)) (Primrec.const []))))
      (primrec_encodeRawWordNat.comp Primrec.snd).to₂
  have hOdd : RecursiveIn (oracle R) fun m =>
      ((((if ValidLabel m.div2 then none else some [(m.div2, true)]) :
        Option (RawWord ℕ)).map encodeRawWordNat : Option ℕ) : Part ℕ) :=
    RecursiveIn.of_partrec (Partrec.nat_iff.1 (Computable.ofOption hOddP.to_comp))
  -- even branch: `W`, then tagging
  have hW : RecursiveIn (oracle R) fun m => (Wfun R m.div2).map encodeRawWordNat :=
    RecursiveIn.comp_primrec (f := fun p => (Wfun R p).map encodeRawWordNat) recursiveIn_W
      Primrec.nat_div2
  have hg : Primrec₂ fun (m z : ℕ) => (decodeRawWordNat z).map fun w =>
      encodeRawWordNat (tagWord (labelN m.div2) (labelC m.div2) w) :=
    Primrec.option_map (primrec_decodeRawWordNat.comp Primrec.snd)
      (primrec_encodeRawWordNat.comp (primrec_tagWord.comp (Primrec.pair
        (Primrec.pair (primrec_labelN.comp (Primrec.nat_div2.comp (Primrec.fst.comp Primrec.fst)))
          (primrec_labelC.comp (Primrec.nat_div2.comp (Primrec.fst.comp Primrec.fst))))
        Primrec.snd))).to₂
  have hEven := RecursiveIn.bind_primrec hW hg
  have := RecursiveIn.cond Primrec.nat_bodd hOdd hEven
  unfold IsNatEnumerator
  convert this using 1
  funext m
  unfold omegaEnum
  cases m.bodd
  · simp only [cond_false]
    apply Part.ext; intro x
    simp [Part.mem_bind_iff, Part.mem_map_iff, eq_comm]
  · simp only [cond_true]
    apply Part.ext; intro x
    split_ifs <;> simp

/-! ### The exact relator set -/

theorem Wfun_eq_label (q : ℕ) : Wfun R q = W R (labelN q) (labelC q) (labelA q) := rfl

theorem mem_omegaEnum_iff (w : RawWord ℕ) :
    (∃ m, w ∈ omegaEnum R m) ↔
      (∃ n c k, ∃ v ∈ candEnum R n c k, rename (fun a : Fin n => tag n c a) v = w) ∨
        (∃ q, ¬ ValidLabel q ∧ w = [(q, true)]) := by
  constructor
  · rintro ⟨m, hm⟩
    unfold omegaEnum at hm
    cases hb : m.bodd <;> simp only [hb, cond_true, cond_false] at hm
    · obtain ⟨w', hw', rfl⟩ := (Part.mem_map_iff _).1 hm
      rw [Wfun_eq_label, W_eq] at hw'
      obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).1 hw'
      exact Or.inl ⟨_, _, _, v, hv, (tagWord_up _ _ v).symm⟩
    · right
      split_ifs at hm with hv
      · exact absurd hm (Part.notMem_none _)
      · exact ⟨m.div2, hv, (Part.mem_some_iff.1 hm)⟩
  · rintro (⟨n, c, k, v, hv, rfl⟩ | ⟨q, hq, rfl⟩)
    · refine ⟨Nat.bit false (tag n c k), ?_⟩
      simp only [omegaEnum, Nat.bodd_bit, Nat.div2_bit, cond_false, Wfun, labelN_tag,
        labelC_tag]
      rw [show Nat.unpair (Nat.unpair (tag n c k)).1 = (n, c) by simp [tag],
        show (Nat.unpair (tag n c k)).2 = k by simp [tag], W_eq, ← tagWord_up]
      exact Part.mem_map _ (Part.mem_map _ hv)
    · refine ⟨Nat.bit true q, ?_⟩
      simp only [omegaEnum, Nat.bodd_bit, Nat.div2_bit, cond_true, if_neg hq]
      exact Part.mem_some _

/-- **The interpreted relator set of `E_Ω` is exactly `omegaRels R`.** -/
theorem enumRelatorsNat_omegaEnum (R : Set ℕ) : enumRelatorsNat (omegaEnum R) = omegaRels R := by
  ext x
  constructor
  · rintro ⟨m, w, hw, rfl⟩
    rcases (mem_omegaEnum_iff w).1 ⟨m, hw⟩ with ⟨n, c, k, v, hv, rfl⟩ | ⟨q, hq, rfl⟩
    · exact Or.inl ⟨n, c, _, ⟨k, v, hv, rfl⟩, (eval_rename _ v).symm⟩
    · exact Or.inr ⟨q, hq, rfl⟩
  · rintro (⟨n, c, _, ⟨k, v, hv, rfl⟩, rfl⟩ | ⟨q, hq, rfl⟩)
    · obtain ⟨m, hm⟩ := (mem_omegaEnum_iff _).2 (Or.inl ⟨n, c, k, v, hv, rfl⟩)
      exact ⟨m, _, hm, eval_rename _ v⟩
    · obtain ⟨m, hm⟩ := (mem_omegaEnum_iff (R := R) _).2 (Or.inr ⟨q, hq, rfl⟩)
      exact ⟨m, _, hm, rfl⟩

/-! ### The group `Ω_R` -/

/-- **The group `Ω_R`**, presented on the natural-number alphabet by `omegaRels R`. -/
abbrev Omega (R : Set ℕ) : Type := PresentedGroup (omegaRels R)

/-- **`Ω_R` is countably `R`-presented**, witnessed by the explicit enumerator `E_Ω`. -/
theorem countablyPresentedIn_Omega (R : Set ℕ) : CountablyPresentedIn R (Omega R) := by
  refine ⟨omegaEnum R, isNatEnumerator_omegaEnum, ?_⟩
  rw [enumRelatorsNat_omegaEnum]
  exact ⟨MulEquiv.refl _⟩

end TheoremA.RelPres
