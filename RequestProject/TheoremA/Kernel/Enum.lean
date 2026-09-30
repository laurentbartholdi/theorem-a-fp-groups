module

public import RequestProject.TheoremA.Kernel.Assembly
public import RequestProject.TheoremA.RelPres.Universal

/-!
# `S_N` is enumerable relative to the original oracle

Let `e` be an `R`-enumerator of raw relators on `a, b`, and `N` the normal closure of the
enumerated relators.  `S_N = {code w | eval w ∈ N}` is `R`-enumerable (`intEnumerable_codeSet`).

The enumerator `codeEnum` decodes its input as a triple `(L, claims, w)`:
* `L` is **one** finite certificate list (nodes of relative computations, as in `Checker.lean`);
  it must pass the node checker, with the oracle answers for its inputs supplied by `χ_R`;
* each claim `(i, x, r, u, b)` asserts that node `i` of `L` certifies `e(x) = r`; it contributes
  the conjugate `u r^{±1} u⁻¹` (sign `b`);
* `w` is a raw word whose free reduction equals that of the product of the contributed conjugates
  (equality in the **free** group, decided by `FreeGroup.reduce`; this is not a decision procedure
  for the presented quotient).

If everything checks, the output is `code w`.  Soundness uses `good_sound`; completeness uses
`exists_certifies` for each relator computation and concatenation of certificates
(`good_append`).  Membership in `S_N` is not assumed decidable.
-/

@[expose] public section

namespace TheoremA.Kernel

open TheoremA.RelPres TheoremA.Leary

/-- A claim `(i, x, r, u, b)`: node `i` certifies `r ∈ e(x)`; contributes `u r^{±1} u⁻¹`. -/
abbrev Claim : Type := ℕ × ℕ × RawWord (Fin 2) × RawWord (Fin 2) × Bool

/-- Input data `(certificate list, claims, target raw word)`. -/
abbrev KData : Type := List CertNode × List Claim × RawWord (Fin 2)

/-- The raw word `u r^{±1} u⁻¹` of a claim. -/
def claimWord (cl : Claim) : RawWord (Fin 2) :=
  cl.2.2.2.1 ++ (bif cl.2.2.2.2 then cl.2.2.1 else RawWord.inv cl.2.2.1) ++
    RawWord.inv cl.2.2.2.1

/-- The concatenation of the claim words. -/
def prodWord (cls : List Claim) : RawWord (Fin 2) := cls.flatMap claimWord

/-- Node `i` of `L` has head `(p, x, encode r, 0)`. -/
def claimOk (p : ℕ) (L : List CertNode) (cl : Claim) : Bool :=
  decide (cl.1 < L.length) &&
    decide (headOf (L.getD cl.1 dfltNode) = (p, cl.2.1, Encodable.encode cl.2.2.1, 0))

/-- All nodes of `L` pass the checker with oracle answers `A`. -/
def goodB (L : List CertNode) (A : List ℕ) : Bool :=
  (List.range L.length).all fun i => nodeOk (A.getD i 0) L i

/-- The acceptance test. -/
def accept (p : ℕ) (d : KData) (A : List ℕ) : Bool :=
  goodB d.1 A && d.2.1.all (claimOk p d.1) &&
    decide (FreeGroup.reduce d.2.2 = FreeGroup.reduce (prodWord d.2.1))

/-- Decoding of the input. -/
def decData (k : ℕ) : KData := (Encodable.decode k).getD ([], [], [])

/-- **The enumerator of `S_N`** (for the program index `p` of `e`). -/
noncomputable def codeEnum (R : Set ℕ) (p : ℕ) : ℕ →. ℤ := fun k =>
  ((if accept p (decData k) (answers R (decData k).1) = true then
    some ((code (decData k).2.2 : ℕ) : ℤ) else none : Option ℤ) : Part ℤ)

/-! ### Primitive recursiveness -/

theorem primrec_inv : Primrec (RawWord.inv : RawWord (Fin 2) → RawWord (Fin 2)) :=
  Primrec.list_reverse.comp (Primrec.list_map Primrec.id
    (Primrec.dom_finite (fun p : Fin 2 × Bool => (p.1, !p.2)) |>.comp Primrec.snd).to₂)

theorem primrec_claimWord : Primrec claimWord := by
  unfold claimWord
  refine Primrec.list_append.comp (Primrec.list_append.comp ?_ ?_) (primrec_inv.comp ?_)
  · exact Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  · exact Primrec.cond (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (primrec_inv.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  · exact Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem primrec_prodWord : Primrec prodWord :=
  Primrec.list_flatMap Primrec.id (primrec_claimWord.comp Primrec.snd).to₂

/-- The cancellation test of `FreeGroup.reduce`, on pairs of letters. -/
def cancelB (q : (Fin 2 × Bool) × (Fin 2 × Bool)) : Bool :=
  decide (q.1.1 = q.2.1 ∧ q.1.2 = !q.2.2)

/-- One step of free reduction: prepend a letter to a reduced word. -/
def redStep (b : Fin 2 × Bool) : RawWord (Fin 2) → RawWord (Fin 2)
  | [] => [b]
  | hd :: tl => bif cancelB (b, hd) then tl else b :: hd :: tl

/-- Free reduction, written with `redStep`. -/
def reduceP : RawWord (Fin 2) → RawWord (Fin 2)
  | [] => []
  | b :: l => redStep b (reduceP l)

theorem reduceP_eq (L : RawWord (Fin 2)) : reduceP L = FreeGroup.reduce L := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [reduceP, ih, FreeGroup.reduce.cons]
    cases FreeGroup.reduce L with
    | nil => rfl
    | cons hd tl =>
      simp only [redStep, cancelB]
      by_cases h : x.1 = hd.1 ∧ x.2 = !hd.2 <;> simp [h]

theorem primrec_redStep : Primrec₂ redStep := by
  have h := Primrec.list_casesOn (f := fun q : (Fin 2 × Bool) × RawWord (Fin 2) => q.2)
    (g := fun q => [q.1])
    (h := fun q (p : (Fin 2 × Bool) × RawWord (Fin 2)) =>
      bif cancelB (q.1, p.1) then p.2 else q.1 :: p.1 :: p.2) Primrec.snd
    (Primrec.list_cons.comp Primrec.fst (Primrec.const ([] : RawWord (Fin 2))))
    (Primrec.cond ((Primrec.dom_finite cancelB).comp (Primrec.pair
      (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd)))).to₂
  refine h.of_eq fun q => ?_
  obtain ⟨b, M⟩ := q
  cases M <;> rfl

theorem primrec_reduce : Primrec (FreeGroup.reduce : RawWord (Fin 2) → RawWord (Fin 2)) := by
  have h := Primrec.list_rec (f := fun L : RawWord (Fin 2) => L)
    (g := fun _ => ([] : RawWord (Fin 2)))
    (h := fun _ (q : (Fin 2 × Bool) × RawWord (Fin 2) × RawWord (Fin 2)) => redStep q.1 q.2.2)
    Primrec.id (Primrec.const _)
    (primrec_redStep.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
  refine h.of_eq fun L => ?_
  rw [← reduceP_eq]
  induction L with
  | nil => rfl
  | cons x L ih => exact congrArg (redStep x) ih

theorem primrec_headOf : Primrec headOf :=
  Primrec.pair Primrec.fst (Primrec.pair (Primrec.fst.comp Primrec.snd)
    (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

theorem primrec_claimOk : Primrec fun q : (ℕ × List CertNode) × Claim => claimOk q.1.1 q.1.2 q.2 := by
  unfold claimOk
  refine Primrec.and.comp ((PrimrecRel.decide Primrec.nat_lt).comp (Primrec.fst.comp Primrec.snd)
    (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))) ?_
  refine (PrimrecRel.decide Primrec.eq).comp (primrec_headOf.comp ((Primrec.list_getD _).comp
    (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))) ?_
  exact Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.pair
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.pair (Primrec.encode.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      Primrec.snd)))) (Primrec.const 0)))

theorem primrec_goodB : Primrec fun q : List CertNode × List ℕ => goodB q.1 q.2 := by
  unfold goodB
  refine primrec_list_all (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)) ?_
  exact (Primrec.nodeOk_comp ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst)
    Primrec.snd) (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem primrec_accept : Primrec fun q : ℕ × KData × List ℕ => accept q.1 q.2.1 q.2.2 := by
  unfold accept
  refine Primrec.and.comp (Primrec.and.comp ?_ ?_) ?_
  · exact primrec_goodB.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))
  · exact primrec_list_all (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (primrec_claimOk.comp (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))) Primrec.snd)).to₂
  · exact (PrimrecRel.decide Primrec.eq).comp
      (primrec_reduce.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (primrec_reduce.comp (primrec_prodWord.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))))

theorem primrec_decData : Primrec decData :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const _)

/-! ### Recursiveness relative to `R` -/

theorem encode_int_natCast (n : ℕ) : Encodable.encode ((n : ℕ) : ℤ) = 2 * n :=
  encode_int_ofNat n

/-- **`codeEnum` is recursive in `oracle R`.** -/
theorem recursiveIn_codeEnum (R : Set ℕ) (p : ℕ) :
    RelPres.RecursiveIn (oracle R) fun k => (codeEnum R p k).map Encodable.encode := by
  let G : ℕ → Option ℕ := fun m =>
    if accept p (decData (Nat.unpair m).1) (decodeNatList (Nat.unpair m).2) = true then
      some (2 * code (decData (Nat.unpair m).1).2.2) else none
  have hG : Primrec G := by
    refine Primrec.ite ?_ ?_ (Primrec.const none)
    · exact Primrec.eq.comp (primrec_accept.comp (Primrec.pair (Primrec.const p)
        (Primrec.pair (primrec_decData.comp (Primrec.fst.comp Primrec.unpair))
          (primrec_decodeNatList.comp (Primrec.snd.comp Primrec.unpair))))) (Primrec.const true)
    · exact Primrec.option_some.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (primrec_code.comp (Primrec.snd.comp (Primrec.snd.comp
          (primrec_decData.comp (Primrec.fst.comp Primrec.unpair))))))
  have hGp : Nat.Partrec fun m => (G m : Part ℕ) :=
    Partrec.nat_iff.1 (Computable.ofOption hG.to_comp)
  have hg : Primrec fun k => (decData k).1.map fun nd => nd.2.1 :=
    Primrec.list_map (Primrec.fst.comp primrec_decData)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).to₂
  have h2 := RelPres.RecursiveIn.pair (RelPres.RecursiveIn.of_primrec (O := oracle R) Primrec.id)
    (recursiveIn_mapChi (R := R) hg)
  have h3 := RelPres.RecursiveIn.comp (RelPres.RecursiveIn.of_partrec hGp) h2
  convert h3 using 1
  funext k
  simp only [Seq.seq, Part.map_some]
  simp only [codeEnum, G, ← answers_eq]
  split_ifs with h <;> simp [h, encode_int_natCast]

/-! ### Soundness and completeness -/

theorem goodB_answers (R : Set ℕ) (L : List CertNode) : goodB L (answers R L) = true ↔ Good R L := by
  unfold goodB Good
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h i hi; rw [← answers_getD R _ hi]; exact h i hi
  · intro h i hi; rw [answers_getD R _ hi]; exact h i hi

theorem eval_claimWord (cl : Claim) :
    (claimWord cl).eval = cl.2.2.2.1.eval * (cl.2.2.1.eval) ^ (bif cl.2.2.2.2 then 1 else -1 : ℤ) *
      (cl.2.2.2.1.eval)⁻¹ := by
  cases h : cl.2.2.2.2 <;> simp [claimWord, h, RawWord.eval_append, mul_assoc]

theorem eval_prodWord_append (c₁ c₂ : List Claim) :
    (prodWord (c₁ ++ c₂)).eval = (prodWord c₁).eval * (prodWord c₂).eval := by
  simp [prodWord, List.flatMap_append, RawWord.eval_append]

variable {R : Set ℕ} {e : ℕ →. RawWord (Fin 2)} {p : ℕ}

/-- **Soundness.** -/
theorem mem_codeSet_of_mem_codeEnum
    (hp : OracleCode.eval R (OracleCode.decode p) = fun k => (e k).map Encodable.encode)
    {z : ℤ} {k : ℕ} (hz : z ∈ codeEnum R p k) :
    z ∈ codeSet (Subgroup.normalClosure (enumRelators e)) := by
  unfold codeEnum at hz
  split_ifs at hz with hacc
  swap
  · exact absurd hz (Part.notMem_none _)
  obtain rfl := Part.mem_some_iff.1 hz
  set d := decData k
  simp only [accept, Bool.and_eq_true, decide_eq_true_eq] at hacc
  obtain ⟨⟨hgood, hcl⟩, hred⟩ := hacc
  rw [goodB_answers] at hgood
  have hcl' : ∀ cl ∈ d.2.1, (claimWord cl).eval ∈ Subgroup.normalClosure (enumRelators e) := by
    intro cl hmem
    have h := List.all_eq_true.1 hcl cl hmem
    simp only [claimOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hlt, hhead⟩ := h
    have hc := good_sound hgood _ hlt
    rw [hhead, hClaim_zero, hp] at hc
    obtain ⟨r', hr', henc⟩ := (Part.mem_map_iff _).1 hc
    have hr : r' = cl.2.2.1 := Encodable.encode_injective henc
    rw [hr] at hr'
    have hrel : cl.2.2.1.eval ∈ Subgroup.normalClosure (enumRelators e) :=
      Subgroup.subset_normalClosure ⟨_, _, hr', rfl⟩
    rw [eval_claimWord]
    exact (Subgroup.normalClosure_normal).conj_mem _ (zpow_mem hrel _) _
  have hprod : ∀ cls : List Claim, (∀ cl ∈ cls,
      (claimWord cl).eval ∈ Subgroup.normalClosure (enumRelators e)) →
      (prodWord cls).eval ∈ Subgroup.normalClosure (enumRelators e) := by
    intro cls
    induction cls with
    | nil => intro _; exact Subgroup.one_mem _
    | cons cl cls ih =>
      intro h
      have : (prodWord (cl :: cls)).eval = (claimWord cl).eval * (prodWord cls).eval := by
        simp [prodWord, RawWord.eval_append]
      rw [this]
      exact Subgroup.mul_mem _ (h cl (by simp)) (ih fun c hc => h c (by simp [hc]))
  refine ⟨d.2.2, ?_, rfl⟩
  have heq : d.2.2.eval = (prodWord d.2.1).eval := FreeGroup.reduce.exact hred
  rw [heq]
  exact hprod _ hcl'

/-- Shift the certificate index of a claim. -/
def shiftClaim (n : ℕ) (cl : Claim) : Claim := (cl.1 + n, cl.2)

theorem prodWord_map_shift (n : ℕ) (cls : List Claim) :
    prodWord (cls.map (shiftClaim n)) = prodWord cls := by
  simp only [prodWord, List.flatMap_map]
  rfl

/-- Elements of `N` have certified claim lists. -/
def Certified (R : Set ℕ) (p : ℕ) (g : FreeGroup (Fin 2)) : Prop :=
  ∃ (L : List CertNode) (cls : List Claim), Good R L ∧ cls.all (claimOk p L) = true ∧
    (prodWord cls).eval = g

theorem certified_mul {g h : FreeGroup (Fin 2)} (hg : Certified R p g) (hh : Certified R p h) :
    Certified R p (g * h) := by
  obtain ⟨L₁, c₁, g₁, o₁, e₁⟩ := hg
  obtain ⟨L₂, c₂, g₂, o₂, e₂⟩ := hh
  refine ⟨L₁ ++ L₂, c₁ ++ c₂.map (shiftClaim L₁.length), good_append g₁ g₂, ?_, ?_⟩
  · rw [List.all_append, Bool.and_eq_true]
    constructor
    · rw [List.all_eq_true] at o₁ ⊢
      intro cl hcl
      have h := o₁ cl hcl
      simp only [claimOk, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      refine ⟨by rw [List.length_append]; omega, ?_⟩
      rw [List.getD_append _ _ _ _ h.1]; exact h.2
    · rw [List.all_eq_true] at o₂ ⊢
      intro cl' hcl'
      obtain ⟨cl, hcl, rfl⟩ := List.mem_map.1 hcl'
      have h := o₂ cl hcl
      simp only [claimOk, shiftClaim, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      refine ⟨by rw [List.length_append]; omega, ?_⟩
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel]; exact h.2
  · rw [eval_prodWord_append, prodWord_map_shift, e₁, e₂]

theorem certified_one : Certified R p 1 :=
  ⟨[], [], fun i hi => absurd hi (by simp), rfl, rfl⟩

theorem certified_conj
    (hp : OracleCode.eval R (OracleCode.decode p) = fun k => (e k).map Encodable.encode)
    {a : FreeGroup (Fin 2)} (ha : a ∈ enumRelators e) (c : FreeGroup (Fin 2)) (b : Bool) :
    Certified R p (c * a ^ (bif b then 1 else -1 : ℤ) * c⁻¹) := by
  obtain ⟨k, r, hr, rfl⟩ := ha
  have hy : Encodable.encode r ∈ OracleCode.eval R (OracleCode.decode p) k := by
    rw [hp]; exact Part.mem_map _ hr
  obtain ⟨L, hg, hl, hh⟩ := exists_certifies _ _ _ hy
  rw [OracleCode.encode_decode] at hh
  obtain ⟨u, rfl⟩ := RawWord.eval_surjective c
  refine ⟨L, [(L.length - 1, k, r, u, b)], hg, ?_, ?_⟩
  · simp only [List.all_cons, List.all_nil, Bool.and_true, claimOk, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨by omega, hh⟩
  · rw [show prodWord [(L.length - 1, k, r, u, b)] = claimWord (L.length - 1, k, r, u, b) by
      simp [prodWord], eval_claimWord]

theorem certified_of_mem
    (hp : OracleCode.eval R (OracleCode.decode p) = fun k => (e k).map Encodable.encode)
    {g : FreeGroup (Fin 2)} (hg : g ∈ Subgroup.normalClosure (enumRelators e)) :
    Certified R p g := by
  have hg' : g ∈ (Subgroup.closure (Group.conjugatesOfSet (enumRelators e))).toSubmonoid := hg
  rw [Subgroup.closure_toSubmonoid] at hg'
  clear hg
  induction hg' using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.1 hx
      obtain ⟨c, rfl⟩ := isConj_iff.1 hc
      simpa using certified_conj hp ha c true
    · obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.1 (Set.mem_inv.1 hx)
      obtain ⟨c, hc⟩ := isConj_iff.1 hc
      have : x = c * a ^ (bif false then 1 else -1 : ℤ) * c⁻¹ := by
        rw [← inv_inj, ← hc]; simp [mul_assoc]
      rw [this]
      exact certified_conj hp ha c false
  | one => exact certified_one
  | mul x y _ _ hx hy => exact certified_mul hx hy

/-- **Completeness.** -/
theorem exists_mem_codeEnum
    (hp : OracleCode.eval R (OracleCode.decode p) = fun k => (e k).map Encodable.encode)
    {z : ℤ} (hz : z ∈ codeSet (Subgroup.normalClosure (enumRelators e))) :
    ∃ k, z ∈ codeEnum R p k := by
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨L, cls, hg, ho, he⟩ := certified_of_mem hp hw
  refine ⟨Encodable.encode ((L, cls, w) : KData), ?_⟩
  have hd : decData (Encodable.encode ((L, cls, w) : KData)) = (L, cls, w) := by
    simp [decData]
  unfold codeEnum
  rw [hd, if_pos]
  · exact Part.mem_some _
  · simp only [accept, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨(goodB_answers R L).2 hg, ho⟩, FreeGroup.reduce.sound (he.trans rfl).symm⟩

/-- **`S_N` is enumerable relative to the same oracle `R`.** -/
theorem intEnumerable_codeSet (he : IsEnumerator R e) :
    IntEnumerable R (codeSet (Subgroup.normalClosure (enumRelators e))) := by
  obtain ⟨c, hc⟩ := OracleCode.exists_code he
  have hp : OracleCode.eval R (OracleCode.decode (OracleCode.encode c)) =
      fun k => (e k).map Encodable.encode := by rw [OracleCode.decode_encode, hc]
  refine ⟨codeEnum R (OracleCode.encode c), recursiveIn_codeEnum R _, ?_⟩
  ext z
  exact ⟨fun hz => exists_mem_codeEnum hp hz,
    fun ⟨k, hk⟩ => mem_codeSet_of_mem_codeEnum hp hk⟩

end TheoremA.Kernel
