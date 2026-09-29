module

public import RequestProject.TheoremA.RelPres.Code

/-!
# Uniform verification of finite relative computations

A **certificate** is a finite list of computation nodes
`(program, input, output, mode, ref₁, ref₂) : CertNode`.  The *head* of a node is its first
four fields.  A node of mode `0` claims `output ∈ eval R (decode program) input`; a node of
mode `≠ 0` (used only for `rfind`) claims that for every `k < output` the body
`decode (codeArg program)` terminates on `⟨input, k⟩` with a nonzero value.

The references are **relative back-offsets**: the children of node `i` are nodes `i - ref₁`
and `i - ref₂`; every reference must satisfy `ref ≤ i`, and a reference actually used as a child
must be `≥ 1`, so children lie strictly earlier.  Relative references make concatenation of
certificates reference-preserving (`good_append`).

`localCheck` checks the evaluation rule of one node against the heads of its children (and,
for a `query` node, against the value `chiNat R input`).  In particular:
* a `prec` successor node on `⟨a, n+1⟩` references the node for `⟨a, n⟩` (same program) and
  the step node for `⟨a, ⟨n, i⟩⟩`;
* an `rfind` node with output `m` references a mode-`1` node certifying nonzero terminating
  outputs at all `k < m`, and a node certifying output `0` at `m`; mode-`1` nodes are built
  one candidate at a time.

`check R c x y cert` decodes `cert` to a list of nodes and checks every node, with the oracle
answers supplied by the total function `chiNat R`.  It is total, and `recursiveIn_checkFn`
shows that its encoded version is recursive in `oracle R`, uniformly in all four arguments.
Soundness and completeness: `mem_eval_iff_exists_check`.
-/

@[expose] public section

namespace TheoremA.RelPres

open OracleCode

/-! ### The oracle as a total function -/

open Classical in
/-- The characteristic function of `R` as a total function (values `0`, `1`). -/
noncomputable def chiNat (R : Set ℕ) (k : ℕ) : ℕ := if k ∈ R then 1 else 0

theorem chi_eq_some (R : Set ℕ) (k : ℕ) : chi R k = Part.some (chiNat R k) := rfl

/-! ### Nodes -/

/-- A computation node `(program, input, output, mode, ref₁, ref₂)`. -/
abbrev CertNode := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

/-- The head `(program, input, output, mode)` of a node. -/
abbrev NodeHead := ℕ × ℕ × ℕ × ℕ

/-- Default node, returned by out-of-range lookups. -/
def dfltNode : CertNode := (0, 0, 0, 0, 0, 0)

/-- The head of a node. -/
def headOf (nd : CertNode) : NodeHead := (nd.1, nd.2.1, nd.2.2.1, nd.2.2.2.1)

/-- The local evaluation rule for one node `nd`, given the heads `h₁`, `h₂` of its two
referenced children and the oracle answer `a` (meant to be `chiNat R input`). -/
def localCheck (nd : CertNode) (h₁ h₂ : NodeHead) (a : ℕ) : Bool :=
  bif decide (nd.2.2.2.1 = 0) then
    bif decide (codeTag nd.1 = 0) then decide (nd.2.2.1 = 0)
    else bif decide (codeTag nd.1 = 1) then decide (nd.2.2.1 = nd.2.1 + 1)
    else bif decide (codeTag nd.1 = 2) then decide (nd.2.2.1 = (Nat.unpair nd.2.1).1)
    else bif decide (codeTag nd.1 = 3) then decide (nd.2.2.1 = (Nat.unpair nd.2.1).2)
    else bif decide (codeTag nd.1 = 4) then decide (nd.2.2.1 = a)
    else bif decide (codeTag nd.1 = 5) then
      decide (0 < nd.2.2.2.2.1) && decide (0 < nd.2.2.2.2.2) &&
      decide (h₁ = ((Nat.unpair (codeArg nd.1)).1, nd.2.1, h₁.2.2.1, 0)) &&
      decide (h₂ = ((Nat.unpair (codeArg nd.1)).2, nd.2.1, h₂.2.2.1, 0)) &&
      decide (nd.2.2.1 = Nat.pair h₁.2.2.1 h₂.2.2.1)
    else bif decide (codeTag nd.1 = 6) then
      decide (0 < nd.2.2.2.2.1) && decide (0 < nd.2.2.2.2.2) &&
      decide (h₁ = ((Nat.unpair (codeArg nd.1)).2, nd.2.1, h₁.2.2.1, 0)) &&
      decide (h₂ = ((Nat.unpair (codeArg nd.1)).1, h₁.2.2.1, nd.2.2.1, 0))
    else bif decide (codeTag nd.1 = 7) then
      bif decide ((Nat.unpair nd.2.1).2 = 0) then
        decide (0 < nd.2.2.2.2.1) &&
        decide (h₁ = ((Nat.unpair (codeArg nd.1)).1, (Nat.unpair nd.2.1).1, nd.2.2.1, 0))
      else
        decide (0 < nd.2.2.2.2.1) && decide (0 < nd.2.2.2.2.2) &&
        decide (h₁ = (nd.1, Nat.pair (Nat.unpair nd.2.1).1 ((Nat.unpair nd.2.1).2 - 1),
          h₁.2.2.1, 0)) &&
        decide (h₂ = ((Nat.unpair (codeArg nd.1)).2, Nat.pair (Nat.unpair nd.2.1).1
          (Nat.pair ((Nat.unpair nd.2.1).2 - 1) h₁.2.2.1), nd.2.2.1, 0))
    else
      decide (0 < nd.2.2.2.2.1) && decide (0 < nd.2.2.2.2.2) &&
      decide (h₁ = (nd.1, nd.2.1, nd.2.2.1, 1)) &&
      decide (h₂ = (codeArg nd.1, Nat.pair nd.2.1 nd.2.2.1, 0, 0))
  else
    decide (codeTag nd.1 = 8) &&
    (decide (nd.2.2.1 = 0) ||
      (decide (0 < nd.2.2.2.2.1) && decide (0 < nd.2.2.2.2.2) &&
        decide (h₁ = (nd.1, nd.2.1, nd.2.2.1 - 1, 1)) &&
        decide (h₂ = (codeArg nd.1, Nat.pair nd.2.1 (nd.2.2.1 - 1), h₂.2.2.1, 0)) &&
        decide (0 < h₂.2.2.1)))

/-- Check of node `i` of the list `L` with oracle answer `a`: references are back-offsets
`≤ i`, and the local rule holds against the referenced heads. -/
def nodeOk (a : ℕ) (L : List CertNode) (i : ℕ) : Bool :=
  decide ((L.getD i dfltNode).2.2.2.2.1 ≤ i) && decide ((L.getD i dfltNode).2.2.2.2.2 ≤ i) &&
    localCheck (L.getD i dfltNode) (headOf (L.getD (i - (L.getD i dfltNode).2.2.2.2.1) dfltNode))
      (headOf (L.getD (i - (L.getD i dfltNode).2.2.2.2.2) dfltNode)) a

/-- The oracle-free core of the checker; `A` is the list of oracle answers for the inputs of
the nodes of `L`. -/
def checkCore (c x y : ℕ) (L : List CertNode) (A : List ℕ) : Bool :=
  decide (0 < L.length) && decide (headOf (L.getD (L.length - 1) dfltNode) = (c, x, y, 0)) &&
    (List.range L.length).all fun i => nodeOk (A.getD i 0) L i

/-- The oracle answers for the inputs of the nodes of a list. -/
noncomputable def answers (R : Set ℕ) (L : List CertNode) : List ℕ :=
  L.map fun nd => chiNat R nd.2.1

/-- The list of nodes coded by a certificate number (empty if the number codes no list). -/
def nodesOf (cert : ℕ) : List CertNode := ((Encodable.decode cert : Option (List CertNode))).getD []

/-- **The total checker.**  `check R c x y cert = true` iff `cert` codes a nonempty list of
nodes, each satisfying its local evaluation rule (query nodes against `chiNat R`), whose last
node has head `(c, x, y, 0)`. -/
noncomputable def check (R : Set ℕ) (c x y cert : ℕ) : Bool :=
  checkCore c x y (nodesOf cert) (answers R (nodesOf cert))

/-- The checker as a (total) partial function `ℕ →. ℕ` of the code
`⟨c, ⟨x, ⟨y, cert⟩⟩⟩`, with values `1` (accept) and `0` (reject). -/
noncomputable def checkFn (R : Set ℕ) : ℕ →. ℕ := fun n =>
  Part.some (check R (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).1
    (Nat.unpair (Nat.unpair (Nat.unpair n).2).2).1
    (Nat.unpair (Nat.unpair (Nat.unpair n).2).2).2).toNat

/-! ### Primitive recursiveness of the oracle-free part -/

theorem primrec_id' {α : Type*} [Primcodable α] : Primrec fun a : α => a := Primrec.id

/-- One round of syntax-directed decomposition of a `Primrec` goal. -/
macro "prim_round" : tactic => `(tactic| (any_goals (first
  | with_reducible exact primrec_id'
  | with_reducible exact Primrec.fst
  | with_reducible exact Primrec.snd
  | with_reducible exact Primrec.const _
  | with_reducible apply Primrec.fst.comp
  | with_reducible apply Primrec.snd.comp
  | with_reducible apply (PrimrecRel.decide Primrec.eq).comp
  | with_reducible apply (PrimrecRel.decide Primrec.nat_lt).comp
  | with_reducible apply (PrimrecRel.decide Primrec.nat_le).comp
  | with_reducible apply Primrec.and.comp
  | with_reducible apply Primrec.or.comp
  | with_reducible apply Primrec.not.comp
  | with_reducible apply Primrec.cond
  | with_reducible apply Primrec.nat_add.comp
  | with_reducible apply Primrec.nat_sub.comp
  | with_reducible apply Primrec₂.natPair.comp
  | with_reducible apply primrec_codeTag.comp
  | with_reducible apply primrec_codeArg.comp
  | with_reducible apply Primrec.unpair.comp
  | with_reducible apply (Primrec.list_getD _).comp
  | with_reducible apply Primrec.list_length.comp
  | with_reducible apply Primrec.pair)))

theorem primrec_localCheck :
    Primrec fun v : CertNode × NodeHead × NodeHead × ℕ => localCheck v.1 v.2.1 v.2.2.1 v.2.2.2 := by
  unfold localCheck
  iterate 30 (try prim_round)

theorem Primrec.localCheck_comp {α : Type*} [Primcodable α] {f : α → CertNode}
    {g h : α → NodeHead} {k : α → ℕ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec h)
    (hk : Primrec k) : Primrec fun a => localCheck (f a) (g a) (h a) (k a) :=
  primrec_localCheck.comp (hf.pair (hg.pair (hh.pair hk)))

theorem primrec_nodeOk : Primrec fun v : (ℕ × List CertNode) × ℕ => nodeOk v.1.1 v.1.2 v.2 := by
  unfold nodeOk headOf
  apply Primrec.and.comp
  · iterate 30 (try prim_round)
  · apply Primrec.localCheck_comp
    all_goals iterate 20 (try prim_round)

theorem Primrec.nodeOk_comp {α : Type*} [Primcodable α] {f : α → ℕ}
    {g : α → List CertNode} {h : α → ℕ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec fun a => nodeOk (f a) (g a) (h a) :=
  primrec_nodeOk.comp ((hf.pair hg).pair hh)

theorem list_all_eq_foldl {β : Type*} (l : List β) (p : β → Bool) (b : Bool) :
    l.foldl (fun s x => s && p x) b = (b && l.all p) := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih => simp [ih, Bool.and_assoc]

theorem primrec_list_all {α β : Type*} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).all (p a) := by
  have h := Primrec.list_foldl (f := f) (g := fun _ => true)
    (h := fun a (q : Bool × β) => q.1 && p a q.2) hf (Primrec.const true)
    (Primrec.and.comp (Primrec.fst.comp Primrec.snd)
      (hp.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).to₂
  refine h.of_eq fun a => ?_
  rw [list_all_eq_foldl]; simp

theorem primrec_checkCore :
    Primrec fun v : (ℕ × ℕ × ℕ) × List CertNode × List ℕ =>
      checkCore v.1.1 v.1.2.1 v.1.2.2 v.2.1 v.2.2 := by
  unfold checkCore headOf
  apply Primrec.and.comp
  · iterate 30 (try prim_round)
  · refine primrec_list_all (Primrec.list_range.comp (Primrec.list_length.comp
      (Primrec.fst.comp Primrec.snd))) ?_
    apply Primrec.nodeOk_comp
    all_goals iterate 20 (try prim_round)

theorem Primrec.checkCore_comp {α : Type*} [Primcodable α] {c x y : α → ℕ}
    {L : α → List CertNode} {A : α → List ℕ} (hc : Primrec c) (hx : Primrec x) (hy : Primrec y)
    (hL : Primrec L) (hA : Primrec A) :
    Primrec fun a => checkCore (c a) (x a) (y a) (L a) (A a) :=
  primrec_checkCore.comp ((hc.pair (hx.pair hy)).pair (hL.pair hA))

theorem primrec_nodesOf : Primrec nodesOf :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

/-! ### Recursiveness of the checker in `oracle R` -/

/-- Decoding a list of naturals (default `[]`). -/
def decodeNatList (i : ℕ) : List ℕ := ((Encodable.decode i : Option (List ℕ))).getD []

@[simp] theorem decodeNatList_encode (l : List ℕ) : decodeNatList (Encodable.encode l) = l := by
  simp [decodeNatList]

theorem primrec_decodeNatList : Primrec decodeNatList :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

theorem RecursiveIn.of_primrec {O : Set (ℕ →. ℕ)} {g : ℕ → ℕ} (hg : Primrec g) :
    RecursiveIn O fun n => (Part.some (g n)) :=
  RecursiveIn.of_partrec (Partrec.nat_iff.1 hg.to_comp.partrec)

theorem map_getD_range (l : List ℕ) (F : ℕ → ℕ) :
    (List.range l.length).map (fun j => F (l.getD j 0)) = l.map F := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

variable {R : Set ℕ}

/-- Mapping the oracle over a primitive recursively computed list is recursive in `oracle R`
(a bounded loop built with `prec`, one oracle call per entry). -/
theorem recursiveIn_mapChi {g : ℕ → List ℕ} (hg : Primrec g) :
    RecursiveIn (oracle R) fun n => Part.some (Encodable.encode ((g n).map (chiNat R))) := by
  let Q : ℕ → ℕ := fun q => (g (Nat.unpair q).1).getD (Nat.unpair (Nat.unpair q).2).1 0
  have hQ : Primrec Q := (Primrec.list_getD 0).comp (hg.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  let S : ℕ → ℕ := fun r => Encodable.encode
    (decodeNatList (Nat.unpair (Nat.unpair (Nat.unpair r).1).2).2 ++ [(Nat.unpair r).2])
  have hS : Primrec S := Primrec.encode.comp (Primrec.list_append.comp
    (primrec_decodeNatList.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))) (Primrec.list_cons.comp
      (Primrec.snd.comp Primrec.unpair) (Primrec.const [])))
  have hH : RecursiveIn (oracle R) fun q => Part.some (S (Nat.pair q (chiNat R (Q q)))) := by
    have h1 : RecursiveIn (oracle R) fun q => chi R (Q q) :=
      RecursiveIn.comp_primrec (RecursiveIn.oracle (O := oracle R) (chi R) rfl) hQ
    have h2 := RecursiveIn.pair (RecursiveIn.of_primrec (O := oracle R) Primrec.id) h1
    have h3 := RecursiveIn.comp (RecursiveIn.of_primrec (O := oracle R) hS) h2
    convert h3 using 1
    funext q
    simp [chi_eq_some, Seq.seq]
  have hP := RecursiveIn.prec (RecursiveIn.zero (O := oracle R)) hH
  have hpr : Primrec fun n => Nat.pair n (g n).length :=
    Primrec₂.natPair.comp Primrec.id (Primrec.list_length.comp hg)
  have hF := RecursiveIn.comp_primrec hP hpr
  convert hF using 1
  funext n
  simp only [Nat.unpair_pair]
  have key : ∀ k, (Nat.rec (0 : Part ℕ) (fun y IH => IH >>= fun i =>
      Part.some (S (Nat.pair (Nat.pair n (Nat.pair y i))
        (chiNat R (Q (Nat.pair n (Nat.pair y i))))))) k : Part ℕ) =
      Part.some (Encodable.encode ((List.range k).map fun j => chiNat R ((g n).getD j 0))) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.map_append]
      simp only at ih ⊢
      rw [ih]
      simp [S, Q, Nat.unpair_pair]
  rw [← map_getD_range]
  exact (key _).symm

theorem answers_eq (R : Set ℕ) (L : List CertNode) :
    answers R L = (L.map fun nd => nd.2.1).map (chiNat R) := by
  simp [answers]

theorem primrec_toNat : Primrec Bool.toNat :=
  (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).of_eq fun b => by
    cases b <;> rfl

/-- The inputs of the nodes of the certificate component of `⟨c, ⟨x, ⟨y, cert⟩⟩⟩`. -/
def certInputs (n : ℕ) : List ℕ :=
  (nodesOf (Nat.unpair (Nat.unpair (Nat.unpair n).2).2).2).map fun nd => nd.2.1

theorem primrec_certInputs : Primrec certInputs :=
  Primrec.list_map (primrec_nodesOf.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
    (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd) :
      Primrec fun q : ℕ × CertNode => q.2.2.1).to₂

/-- The oracle-free part of the encoded checker, on `⟨⟨c, ⟨x, ⟨y, cert⟩⟩⟩, code of answers⟩`. -/
def checkG (m : ℕ) : ℕ :=
  (checkCore (Nat.unpair (Nat.unpair m).1).1 (Nat.unpair (Nat.unpair (Nat.unpair m).1).2).1
    (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair m).1).2).2).1
    (nodesOf (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair m).1).2).2).2)
    (decodeNatList (Nat.unpair m).2)).toNat

theorem primrec_checkG : Primrec checkG := by
  unfold checkG
  refine primrec_toNat.comp (Primrec.checkCore_comp ?_ ?_ ?_ ?_ ?_)
  · exact Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  · exact Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.fst.comp Primrec.unpair))))
  · exact Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))))
  · exact primrec_nodesOf.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
      (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.fst.comp Primrec.unpair)))))))
  · exact primrec_decodeNatList.comp (Primrec.snd.comp Primrec.unpair)

theorem checkFn_eq (R : Set ℕ) (n : ℕ) :
    checkFn R n = Part.some (checkG (Nat.pair n
      (Encodable.encode ((certInputs n).map (chiNat R))))) := by
  simp only [checkFn, check, checkG, Nat.unpair_pair, decodeNatList_encode, certInputs,
    answers_eq]

/-- **Uniform recursiveness of the checker**: the encoded checker
`⟨c, ⟨x, ⟨y, cert⟩⟩⟩ ↦ (check R c x y cert).toNat` is recursive in `oracle R`. -/
theorem recursiveIn_checkFn : RecursiveIn (oracle R) (checkFn R) := by
  have h2 := RecursiveIn.pair (RecursiveIn.of_primrec (O := oracle R) Primrec.id)
    (recursiveIn_mapChi (R := R) primrec_certInputs)
  have h3 := RecursiveIn.comp (RecursiveIn.of_primrec (O := oracle R) primrec_checkG) h2
  convert h3 using 1
  funext n
  rw [checkFn_eq]
  simp [Seq.seq]

end TheoremA.RelPres
