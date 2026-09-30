module

public import RequestProject.TheoremA.Leary.LongRelators
public import RequestProject.TheoremA.RelPres.Oracle

/-!
# The same-oracle presentation of `J(S)`

* `IntEnumerable R S` — `S ⊆ ℤ` is the range of a partial function `ℕ →. ℤ` that is recursive in
  the oracle `{χ_R}` (codes of integers via the standard `Encodable ℤ`).  Membership in `S` is
  *not* assumed decidable.
* `rawZPowC e c` — the raw word `eⁿ` computed from the code `c = encode n` by repetition
  (`c = 2k ↦ e^k`, `c = 2k+1 ↦ e^{-(k+1)}`); `eval_rawZPowC`.
* `jEnum D f` — interleaves the finite table of short relators (even indices) with the long
  relators `a₁ⁿ⋯a_kⁿ` of fundamental cycles (odd indices, `k/2 = ⟨a, j⟩`, `n ∈ f j`).
* `isEnumerator_jEnum` — `jEnum D f` is an `R`-enumerator (the same oracle `R`).
* `enumRelators_jEnum` — its interpreted relator set is exactly `jRels D S`.
* `classCR_JGrp` — **`J(S)` is in `C_R`** whenever `S` is `R`-enumerable.
-/

@[expose] public section

namespace TheoremA.Leary

open TheoremA.RelPres

/-- `S ⊆ ℤ` is enumerable relative to the oracle `R`. -/
def IntEnumerable (R : Set ℕ) (S : Set ℤ) : Prop :=
  ∃ f : ℕ →. ℤ, RelPres.RecursiveIn (oracle R) (fun k => (f k).map Encodable.encode) ∧
    S = {n | ∃ k, n ∈ f k}

theorem encode_int_ofNat (n : ℕ) : Encodable.encode (Int.ofNat n) = 2 * n := by
  change Function.uncurry Nat.bit (false, n) = 2 * n
  simp [Nat.bit]

theorem encode_int_negSucc (n : ℕ) : Encodable.encode (Int.negSucc n) = 2 * n + 1 := by
  change Equiv.intEquivNat (Int.negSucc n) = _
  simp [Equiv.intEquivNat, Equiv.intEquivNatSumNat, Equiv.natSumNatEquivNat]

section Raw

variable {m : ℕ}

/-- The raw word of `eⁿ`, computed from the code `c` of `n` by repetition. -/
def rawZPowC (e : Fin m) (c : ℕ) : RawWord (Fin m) :=
  if c % 2 = 0 then List.replicate (c / 2) (e, true) else List.replicate (c / 2 + 1) (e, false)

theorem eval_replicate (x : Fin m × Bool) (k : ℕ) :
    RawWord.eval (List.replicate k x) = (RawWord.eval [x]) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', RawWord.eval_append, ih, pow_succ]

theorem eval_rawZPowC (e : Fin m) (n : ℤ) :
    RawWord.eval (rawZPowC e (Encodable.encode n)) = FreeGroup.of e ^ n := by
  rcases n with n | n
  · rw [encode_int_ofNat, rawZPowC, if_pos (by omega), eval_replicate, RawWord.eval_pos]
    have : 2 * n / 2 = n := by omega
    rw [this]; simp
  · rw [encode_int_negSucc, rawZPowC, if_neg (by omega), eval_replicate, RawWord.eval_neg]
    have : (2 * n + 1) / 2 + 1 = n + 1 := by omega
    rw [this, zpow_negSucc, inv_pow]

theorem iterate_cons_nil (x : Fin m × Bool) (k : ℕ) :
    (fun l : RawWord (Fin m) => x :: l)^[k] [] = List.replicate k x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, List.replicate_succ]

theorem primrec_rawZPowC : Primrec₂ (rawZPowC : Fin m → ℕ → RawWord (Fin m)) := by
  have hrep : ∀ b : Bool, Primrec₂ fun (e : Fin m) (k : ℕ) => List.replicate k (e, b) := by
    intro b
    have := Primrec.nat_iterate (f := fun p : Fin m × ℕ => p.2) (g := fun _ => ([] : RawWord (Fin m)))
      (h := fun p (l : RawWord (Fin m)) => (p.1, b) :: l) Primrec.snd (Primrec.const _)
      (Primrec.list_cons.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.const b))
        Primrec.snd).to₂
    show Primrec fun p : Fin m × ℕ => List.replicate p.2 (p.1, b)
    exact Primrec.of_eq this (fun p => iterate_cons_nil _ _)
  have hc : PrimrecPred fun p : Fin m × ℕ => p.2 % 2 = 0 :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0)
  have := Primrec.ite hc
    ((hrep true).comp Primrec.fst (Primrec.nat_div.comp Primrec.snd (Primrec.const 2)))
    ((hrep false).comp Primrec.fst
      (Primrec.succ.comp (Primrec.nat_div.comp Primrec.snd (Primrec.const 2))))
  exact this.to₂

end Raw

namespace EdgeData

variable (D : EdgeData) [NeZero D.m]

/-- The finite table of short raw relators. -/
def shortTable : List (RawWord (Fin D.m)) :=
  (List.finRange D.m).map (fun a => [(a, true), (D.rev a, true)]) ++
  D.tri.map (fun t => [(t.1, true), (t.2.1, true), (t.2.2, true)]) ++
  D.tri.map (fun t => [(t.1, false), (t.2.1, false), (t.2.2, false)])

omit [NeZero D.m] in
theorem eval_two (a b : Fin D.m) (x y : Bool) :
    RawWord.eval [(a, x), (b, y)] = RawWord.eval [(a, x)] * RawWord.eval [(b, y)] := by
  rw [← RawWord.eval_append]; rfl

omit [NeZero D.m] in
theorem eval_three (a b c : Fin D.m) (x y z : Bool) :
    RawWord.eval [(a, x), (b, y), (c, z)] =
      RawWord.eval [(a, x)] * RawWord.eval [(b, y)] * RawWord.eval [(c, z)] := by
  rw [← RawWord.eval_append, ← RawWord.eval_append]; rfl

omit [NeZero D.m] in
theorem eval_shortTable : RawWord.eval '' {w | w ∈ D.shortTable} = D.shortRels := by
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, shortTable, List.mem_append, List.mem_map,
    List.mem_finRange, true_and, shortRels, Set.mem_union]
  constructor
  · rintro ⟨w, ((⟨a, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩), rfl⟩
    · left; left; exact ⟨a, by rw [eval_two, RawWord.eval_pos, RawWord.eval_pos]⟩
    · left; right
      exact ⟨t, ht, by rw [eval_three, RawWord.eval_pos, RawWord.eval_pos, RawWord.eval_pos]⟩
    · right
      exact ⟨t, ht, by rw [eval_three, RawWord.eval_neg, RawWord.eval_neg, RawWord.eval_neg]⟩
  · rintro ((⟨a, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩)
    · exact ⟨_, Or.inl (Or.inl ⟨a, rfl⟩), by rw [eval_two, RawWord.eval_pos, RawWord.eval_pos]⟩
    · exact ⟨_, Or.inl (Or.inr ⟨t, ht, rfl⟩),
        by rw [eval_three, RawWord.eval_pos, RawWord.eval_pos, RawWord.eval_pos]⟩
    · exact ⟨_, Or.inr ⟨t, ht, rfl⟩,
        by rw [eval_three, RawWord.eval_neg, RawWord.eval_neg, RawWord.eval_neg]⟩

/-- The raw long relator for the edge with index `a mod m` and exponent code `c`. -/
def rawLongC (a c : ℕ) : RawWord (Fin D.m) :=
  (D.fundCycle (Fin.ofNat D.m a)).flatMap fun e => rawZPowC e c

omit [NeZero D.m] in
theorem eval_flatMap_rawZPowC (w : List (Fin D.m)) (n : ℤ) :
    RawWord.eval (w.flatMap fun e => rawZPowC e (Encodable.encode n)) = D.loopPow w n := by
  induction w with
  | nil => rfl
  | cons e w ih =>
    rw [List.flatMap_cons, RawWord.eval_append, ih, eval_rawZPowC]
    simp [loopPow]

theorem eval_rawLongC (a : ℕ) (n : ℤ) :
    RawWord.eval (D.rawLongC a (Encodable.encode n)) =
      D.loopPow (D.fundCycle (Fin.ofNat D.m a)) n :=
  D.eval_flatMap_rawZPowC _ n

theorem primrec_rawLongC : Primrec₂ D.rawLongC := by
  have h1 : Primrec fun a : ℕ => D.fundCycle (Fin.ofNat D.m a) := by
    have hf : Primrec (D.fundCycle) := Primrec.dom_finite _
    have hl : Primrec fun a : ℕ => ((List.finRange D.m).map D.fundCycle).getD (a % D.m) [] :=
      (Primrec.list_getD []).comp (Primrec.const _)
        (Primrec.nat_mod.comp Primrec.id (Primrec.const _))
    refine Primrec.of_eq hl ?_
    intro a
    have hlt : a % D.m < D.m := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))
    rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
    simp [Fin.ofNat]
  exact (Primrec.list_flatMap (h1.comp Primrec.fst)
    (primrec_rawZPowC.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).to₂

/-- **The enumerator of the relators of `J(S)`**: short table on even indices, long relators on
odd indices. -/
def jEnum (f : ℕ →. ℤ) : ℕ →. RawWord (Fin D.m) := fun k =>
  bif k.bodd then (f k.div2.unpair.2).map (fun n => D.rawLongC k.div2.unpair.1 (Encodable.encode n))
  else (D.shortTable[k.div2]? : Part (RawWord (Fin D.m)))

theorem enumRelators_jEnum (f : ℕ →. ℤ) :
    enumRelators (D.jEnum f) = D.jRels {n | ∃ k, n ∈ f k} := by
  ext x
  constructor
  · rintro ⟨k, w, hw, rfl⟩
    unfold jEnum at hw
    cases hb : k.bodd <;> simp only [hb, cond_true, cond_false] at hw
    · left
      rw [← eval_shortTable]
      have hk' : D.shortTable[k.div2]? = some w := by simpa [Part.mem_ofOption] using hw
      exact ⟨w, List.mem_of_getElem? hk', rfl⟩
    · obtain ⟨n, hn, rfl⟩ := (Part.mem_map_iff _).1 hw
      right
      exact ⟨n, ⟨_, hn⟩, Fin.ofNat D.m k.div2.unpair.1, (D.eval_rawLongC _ n)⟩
  · rintro (hx | ⟨n, ⟨j, hj⟩, a, rfl⟩)
    · rw [← eval_shortTable] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
      refine ⟨Nat.bit false i, D.shortTable[i], ?_, rfl⟩
      simp only [jEnum, Nat.bodd_bit, Nat.div2_bit, cond_false]
      rw [List.getElem?_eq_getElem hi]
      exact Part.mem_some _
    · refine ⟨Nat.bit true (Nat.pair a.val j), D.rawLongC a.val (Encodable.encode n), ?_, ?_⟩
      · simp only [jEnum, Nat.bodd_bit, Nat.div2_bit, cond_true, Nat.unpair_pair]
        exact Part.mem_map _ hj
      · rw [eval_rawLongC]
        congr
        exact Fin.ext (by simp [Fin.ofNat, Nat.mod_eq_of_lt a.isLt])

variable {D}

/-- **`jEnum` is an enumerator relative to the same oracle `R`.** -/
theorem isEnumerator_jEnum {R : Set ℕ} {f : ℕ →. ℤ}
    (hf : RelPres.RecursiveIn (oracle R) (fun k => (f k).map Encodable.encode)) :
    IsEnumerator R (D.jEnum f) := by
  have hT : RelPres.RecursiveIn (oracle R) fun k =>
      ((D.shortTable[k.div2]?).map Encodable.encode : Part ℕ) :=
    RelPres.RecursiveIn.comp_primrec (f := fun k => ((D.shortTable[k]?).map Encodable.encode : Part ℕ))
      (RelPres.RecursiveIn.of_partrec (partrec_table D.shortTable)) Primrec.nat_div2
  -- the pair ⟨a, code of n⟩
  have hA : RelPres.RecursiveIn (oracle R) fun k => (Part.some k.div2.unpair.1 : Part ℕ) :=
    RelPres.RecursiveIn.of_partrec (Partrec.nat_iff.1
      (Computable.partrec (Primrec.to_comp (Primrec.fst.comp
        (Primrec.unpair.comp Primrec.nat_div2)))))
  have hN : RelPres.RecursiveIn (oracle R) fun k => (f k.div2.unpair.2).map Encodable.encode :=
    RelPres.RecursiveIn.comp_primrec (f := fun k => (f k).map Encodable.encode) hf
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.nat_div2))
  have hP := RelPres.RecursiveIn.pair hA hN
  let g' : ℕ →. ℕ := fun p => Part.some (Encodable.encode (D.rawLongC p.unpair.1 p.unpair.2))
  have hg' : Nat.Partrec g' := by
    apply Partrec.nat_iff.1
    exact (Primrec.encode.comp (D.primrec_rawLongC.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair))).to_comp.partrec
  have hE := RelPres.RecursiveIn.comp (RelPres.RecursiveIn.of_partrec hg') hP
  have := RelPres.RecursiveIn.cond Primrec.nat_bodd hE hT
  unfold IsEnumerator
  convert this using 1
  funext k
  unfold jEnum
  cases k.bodd
  · simp only [cond_false]
    apply Part.ext; intro x
    simp
  · simp only [cond_true]
    apply Part.ext; intro x
    simp [g', Part.mem_bind_iff, Part.mem_map_iff, Seq.seq, eq_comm]

/-- **Same-oracle presentation**: if `S` is `R`-enumerable then `J(S) ∈ C_R`. -/
theorem classCR_JGrp {R : Set ℕ} {S : Set ℤ} (hS : IntEnumerable R S) :
    ClassCR R (D.JGrp S) := by
  obtain ⟨f, hf, rfl⟩ := hS
  refine ⟨D.m, D.jEnum f, isEnumerator_jEnum hf, ⟨?_⟩⟩
  exact QuotientGroup.quotientMulEquivOfEq (congrArg Subgroup.normalClosure
    (D.enumRelators_jEnum f))

end EdgeData

end TheoremA.Leary
