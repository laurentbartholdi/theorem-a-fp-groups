module

public import RequestProject.TheoremA.Leary.Instance

/-!
# `flagL` is a flag simplicial complex (kernel-checked)

Generic definitions for `EdgeData`:
* `Adj v w` — there is a directed edge `v → w`;
* `triVerts t` — the vertex set of a triangle;
* `IsClique σ`, `IsSimplex σ` (a set of at most one vertex, the two ends of an edge, or the vertex
  set of a listed triangle);
* `IsFlagComplex` — simplicial-structure conditions (no loops, `rev` a fixed-point-free
  involution, at most one directed edge per ordered pair of vertices, triangles with three
  distinct vertices, distinct listed triangles have distinct vertex sets) together with
  **flagness**: every clique of vertices spans a simplex.

`flag_of_checks` proves why a finite certificate implies flagness: if every directed 3-cycle of
edges spans a listed triangle and no vertex outside a triangle is adjacent to all three of its
vertices (no 4-cliques), then every clique is a simplex (cliques of size `≥ 4` would contain a
4-clique).

`flagL_isFlagComplex` checks all conditions for the fixed 61-vertex complex by kernel evaluation,
using an out-edge table `flagOutTab` whose correctness is itself checked.  `flagL_connected`
checks that every root path is a walk from the root (so the 1-skeleton is connected and the
fundamental cycles are closed walks at the root).
-/

@[expose] public section

namespace TheoremA.Leary

namespace EdgeData

variable (D : EdgeData)

/-- There is a directed edge `v → w`. -/
def Adj (v w : Fin D.nv) : Prop := ∃ a, D.src a = v ∧ D.tgt a = w

/-- The vertex set of a triangle. -/
def triVerts (t : Fin D.m × Fin D.m × Fin D.m) : Finset (Fin D.nv) :=
  {D.src t.1, D.src t.2.1, D.src t.2.2}

/-- Pairwise adjacent vertices. -/
def IsClique (σ : Finset (Fin D.nv)) : Prop := ∀ v ∈ σ, ∀ w ∈ σ, v ≠ w → D.Adj v w

/-- The simplices of the 2-complex: at most one vertex, an edge, or a listed triangle. -/
def IsSimplex (σ : Finset (Fin D.nv)) : Prop :=
  σ.card ≤ 1 ∨ (∃ a, σ = {D.src a, D.tgt a}) ∨ ∃ t ∈ D.tri, σ = D.triVerts t

/-- **Flag simplicial complex** (with the simplicial-structure conditions). -/
structure IsFlagComplex : Prop where
  no_loop : ∀ a, D.src a ≠ D.tgt a
  rev_rev : ∀ a, D.rev (D.rev a) = a
  rev_ne : ∀ a, D.rev a ≠ a
  edge_unique : ∀ a b, D.src a = D.src b → D.tgt a = D.tgt b → a = b
  tri_card : ∀ t ∈ D.tri, (D.triVerts t).card = 3
  tri_nodup : (D.tri.map D.triVerts).Nodup
  flag : ∀ σ, D.IsClique σ → D.IsSimplex σ

/-- **Why the certificate implies flagness.** -/
theorem flag_of_checks
    (h3 : ∀ a b c, D.tgt a = D.src b → D.tgt b = D.src c → D.tgt c = D.src a →
      ∃ t ∈ D.tri, D.triVerts t = {D.src a, D.src b, D.src c})
    (h4 : ∀ t ∈ D.tri, ∀ v, v ∉ D.triVerts t →
      ¬ (D.Adj v (D.src t.1) ∧ D.Adj v (D.src t.2.1) ∧ D.Adj v (D.src t.2.2))) :
    ∀ σ, D.IsClique σ → D.IsSimplex σ := by
  have tri3 : ∀ x y z : Fin D.nv, x ≠ y → x ≠ z → y ≠ z → D.IsClique {x, y, z} →
      ∃ t ∈ D.tri, D.triVerts t = {x, y, z} := by
    intro x y z hxy hxz hyz hc
    obtain ⟨a, ha1, ha2⟩ := hc x (by simp) y (by simp) hxy
    obtain ⟨b, hb1, hb2⟩ := hc y (by simp) z (by simp) hyz
    obtain ⟨c, hc1, hc2⟩ := hc z (by simp) x (by simp) (Ne.symm hxz)
    obtain ⟨t, ht, he⟩ := h3 a b c (by rw [ha2, hb1]) (by rw [hb2, hc1]) (by rw [hc2, ha1])
    exact ⟨t, ht, by rw [he, ha1, hb1, hc1]⟩
  intro σ hσ
  rcases (by omega : σ.card ≤ 1 ∨ σ.card = 2 ∨ σ.card = 3 ∨ 4 ≤ σ.card) with h | h | h | h
  · exact Or.inl h
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 h
    obtain ⟨a, rfl, rfl⟩ := hσ x (by simp) y (by simp) hxy
    exact Or.inr (Or.inl ⟨a, rfl⟩)
  · obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 h
    obtain ⟨t, ht, he⟩ := tri3 x y z hxy hxz hyz hσ
    exact Or.inr (Or.inr ⟨t, ht, he.symm⟩)
  · exfalso
    obtain ⟨τ, hτσ, hτ⟩ := Finset.exists_subset_card_eq h
    obtain ⟨u, ρ, hu, rfl, hρ⟩ := Finset.card_eq_succ.1 hτ
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hρ
    have hc : D.IsClique {x, y, z} := fun v hv w hw hvw =>
      hσ v (hτσ (Finset.mem_insert_of_mem hv)) w (hτσ (Finset.mem_insert_of_mem hw)) hvw
    obtain ⟨t, ht, he⟩ := tri3 x y z hxy hxz hyz hc
    have huσ : u ∈ σ := hτσ (Finset.mem_insert_self _ _)
    have hut : u ∉ D.triVerts t := by rw [he]; exact hu
    have hmem : ∀ w ∈ D.triVerts t, D.Adj u w := by
      intro w hw
      refine hσ u huσ w (hτσ (Finset.mem_insert_of_mem (he ▸ hw))) ?_
      rintro rfl; exact hut hw
    exact h4 t ht u hut ⟨hmem _ (by simp [triVerts]), hmem _ (by simp [triVerts]),
      hmem _ (by simp [triVerts])⟩

end EdgeData

/-! ### The certificate for `flagL` -/

/-- Out-edges of each vertex (a certificate table; its correctness is checked below). -/
def flagOutTab : List (List Nat) := [[0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52, 54, 56, 58], [1, 60, 62, 64, 66, 68, 70, 72, 74, 76, 78, 80, 82, 84], [61, 86, 88, 90, 92, 94, 96, 98, 100, 102, 104, 106, 108, 110], [3, 87, 112, 114, 116, 118, 120, 122, 124, 126, 128, 130, 132, 134], [5, 136, 138, 140, 142, 144, 146, 148, 150, 152, 154, 156, 158, 160, 162, 164], [137, 166, 168, 170, 172, 174, 176, 178, 180, 182, 184, 186, 188, 190, 192, 194], [7, 167, 196, 198, 200, 202, 204, 206, 208, 210, 212, 214, 216, 218, 220, 222], [9, 63, 224, 226, 228], [65, 89, 225, 230, 232], [91, 113, 231, 234, 236], [11, 115, 235, 238, 240], [13, 67, 239, 242, 244], [69, 93, 243, 246, 248], [95, 117, 247, 250, 252], [15, 119, 251, 254, 256], [17, 197, 255, 258, 260], [169, 199, 259, 262, 264], [139, 171, 263, 266, 268], [19, 141, 267, 270, 272], [21, 121, 271, 274, 276], [97, 123, 275, 278, 280], [71, 99, 279, 282, 284], [23, 73, 283, 286, 288], [25, 201, 287, 290, 292], [173, 203, 291, 294, 296], [143, 175, 295, 298, 300], [27, 145, 227, 299, 302], [229, 233, 237, 241, 245, 249, 253, 257, 261, 265, 269, 273, 277, 281, 285, 289, 293, 297, 301, 303], [29, 75, 304, 306, 308], [77, 101, 305, 310, 312], [103, 125, 311, 314, 316], [31, 127, 315, 318, 320], [33, 79, 319, 322, 324], [81, 105, 323, 326, 328], [107, 129, 327, 330, 332], [35, 131, 331, 334, 336], [37, 83, 335, 338, 340], [85, 109, 339, 342, 344], [111, 133, 343, 346, 348], [39, 135, 347, 350, 352], [41, 205, 351, 354, 356], [177, 207, 355, 358, 360], [147, 179, 359, 362, 364], [43, 149, 363, 366, 368], [45, 209, 367, 370, 372], [181, 211, 371, 374, 376], [151, 183, 375, 378, 380], [47, 153, 379, 382, 384], [49, 213, 383, 386, 388], [185, 215, 387, 390, 392], [155, 187, 391, 394, 396], [51, 157, 395, 398, 400], [53, 217, 399, 402, 404], [189, 219, 403, 406, 408], [159, 191, 407, 410, 412], [55, 161, 411, 414, 416], [57, 221, 415, 418, 420], [193, 223, 419, 422, 424], [163, 195, 423, 426, 428], [59, 165, 307, 427, 430], [309, 313, 317, 321, 325, 329, 333, 337, 341, 345, 349, 353, 357, 361, 365, 369, 373, 377, 381, 385, 389, 393, 397, 401, 405, 409, 413, 417, 421, 425, 429, 431]]

/-- `a` is a permutation of the triple `b`. -/
abbrev Perm3 {α : Type} (a b : α × α × α) : Prop :=
  (a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2 = b.2.2) ∨ (a.1 = b.1 ∧ a.2.1 = b.2.2 ∧ a.2.2 = b.2.1) ∨
  (a.1 = b.2.1 ∧ a.2.1 = b.1 ∧ a.2.2 = b.2.2) ∨ (a.1 = b.2.1 ∧ a.2.1 = b.2.2 ∧ a.2.2 = b.1) ∨
  (a.1 = b.2.2 ∧ a.2.1 = b.1 ∧ a.2.2 = b.2.1) ∨ (a.1 = b.2.2 ∧ a.2.1 = b.2.1 ∧ a.2.2 = b.1)

theorem finset_eq_of_perm3 {α : Type} [DecidableEq α] {p q r x y z : α}
    (h : Perm3 (p, q, r) (x, y, z)) : ({p, q, r} : Finset α) = {x, y, z} := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    ext a
    simp only [Finset.mem_insert, Finset.mem_singleton]
    try tauto

/-! Nat-level views of the tables (kernel evaluation of Boolean checks is fast on `Nat`). -/

/-- Source of an edge index. -/
def srcN (a : Nat) : Nat := flagSrcT.get a
/-- Target of an edge index. -/
def tgtN (a : Nat) : Nat := flagTgtT.get a
/-- Out-edges of a vertex index. -/
def outN (v : Nat) : List Nat := flagOutTab.getD v []
/-- Adjacency of vertex indices through the table. -/
def adjN (v w : Nat) : Bool := (outN v).any fun e => tgtN e == w

/-- Range bounds of the tables. -/
def boundsB : Bool :=
  ((List.range 432).all fun a => decide (srcN a < 61) && decide (tgtN a < 61)) &&
  (flagTri.all fun t => decide (t.1 < 432) && decide (t.2.1 < 432) && decide (t.2.2 < 432))

theorem boundsB_eq : boundsB = true := by decide +kernel

/-- The table lists every edge at its source. -/
def memB : Bool := (List.range 432).all fun a => (outN (srcN a)).contains a

theorem memB_eq : memB = true := by decide +kernel

/-- At most one directed edge per ordered pair of vertices. -/
def edgeUniqB : Bool :=
  (List.range 432).all fun a => (outN (srcN a)).all fun b => !(tgtN b == tgtN a) || (b == a)

theorem edgeUniqB_eq : edgeUniqB = true := by decide +kernel

/-- Boolean permutation test for vertex triples. -/
def perm3B (p q r x y z : Nat) : Bool :=
  (p == x && q == y && r == z) || (p == x && q == z && r == y) || (p == y && q == x && r == z) ||
  (p == y && q == z && r == x) || (p == z && q == x && r == y) || (p == z && q == y && r == x)

/-- Every directed 3-cycle spans a listed triangle. -/
def check3B : Bool :=
  (List.range 432).all fun a => (outN (tgtN a)).all fun b => (outN (tgtN b)).all fun c =>
    !(tgtN c == srcN a) || flagTri.any fun t =>
      perm3B (srcN t.1) (srcN t.2.1) (srcN t.2.2) (srcN a) (srcN b) (srcN c)

theorem check3B_eq : check3B = true := by decide +kernel

/-- No vertex outside a triangle is adjacent to all three of its vertices. -/
def check4B : Bool :=
  flagTri.all fun t => (outN (srcN t.1)).all fun a =>
    (tgtN a == srcN t.1) || (tgtN a == srcN t.2.1) || (tgtN a == srcN t.2.2) ||
      !(adjN (tgtN a) (srcN t.2.1) && adjN (tgtN a) (srcN t.2.2))

theorem check4B_eq : check4B = true := by decide +kernel

/-! Translation from `Nat` to `flagL`. -/

theorem srcN_lt {a : Nat} (ha : a < 432) : srcN a < 61 := by
  have := boundsB_eq
  simp only [boundsB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at this
  exact (this.1 a ha).1

theorem tgtN_lt {a : Nat} (ha : a < 432) : tgtN a < 61 := by
  have := boundsB_eq
  simp only [boundsB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at this
  exact (this.1 a ha).2

theorem tri_lt {t : Nat × Nat × Nat} (ht : t ∈ flagTri) : t.1 < 432 ∧ t.2.1 < 432 ∧ t.2.2 < 432 := by
  have := boundsB_eq
  simp only [boundsB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at this
  exact ⟨(this.2 t ht).1.1, (this.2 t ht).1.2, (this.2 t ht).2⟩

theorem src_val (a : Fin flagL.m) : (flagL.src a).val = srcN a.val := by
  show (Fin.ofNat 61 (flagSrcT.get a.val)).val = _
  rw [Fin.val_ofNat]; exact Nat.mod_eq_of_lt (srcN_lt a.isLt)

theorem tgt_val (a : Fin flagL.m) : (flagL.tgt a).val = tgtN a.val := by
  show (Fin.ofNat 61 (flagTgtT.get a.val)).val = _
  rw [Fin.val_ofNat]; exact Nat.mod_eq_of_lt (tgtN_lt a.isLt)

theorem mem_outN (a : Fin flagL.m) : a.val ∈ outN (srcN a.val) := by
  have := memB_eq
  simp only [memB, List.all_eq_true, List.mem_range, List.contains_iff_mem] at this
  exact this a.val a.isLt

theorem adjN_of_adj {v w : Fin flagL.nv} (h : flagL.Adj v w) : adjN v.val w.val = true := by
  obtain ⟨e, rfl, rfl⟩ := h
  simp only [adjN, List.any_eq_true, beq_iff_eq]
  exact ⟨e.val, by rw [src_val]; exact mem_outN e, (tgt_val e).symm⟩

theorem mem_tri_iff {t : Fin flagL.m × Fin flagL.m × Fin flagL.m} (ht : t ∈ flagL.tri) :
    ∃ r ∈ flagTri, (flagL.src t.1).val = srcN r.1 ∧ (flagL.src t.2.1).val = srcN r.2.1 ∧
      (flagL.src t.2.2).val = srcN r.2.2 := by
  simp only [flagL, List.mem_map] at ht
  obtain ⟨r, hr, rfl⟩ := ht
  obtain ⟨h1, h2, h3⟩ := tri_lt hr
  refine ⟨r, hr, ?_, ?_, ?_⟩ <;>
  · rw [src_val]; simp only [Fin.val_ofNat]; rw [Nat.mod_eq_of_lt (by assumption)]

theorem perm3_of_perm3B {x y z p q r : Fin flagL.nv}
    (h : perm3B p.val q.val r.val x.val y.val z.val = true) : Perm3 (p, q, r) (x, y, z) := by
  simp only [perm3B, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  unfold Perm3
  simp only [Fin.ext_iff]
  tauto

theorem flagL_check3 (a b c : Fin flagL.m) (hab : flagL.tgt a = flagL.src b)
    (hbc : flagL.tgt b = flagL.src c) (hca : flagL.tgt c = flagL.src a) :
    ∃ t ∈ flagL.tri, flagL.triVerts t = {flagL.src a, flagL.src b, flagL.src c} := by
  have h := check3B_eq
  simp only [check3B, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, List.any_eq_true] at h
  have hab' := congrArg Fin.val hab; have hbc' := congrArg Fin.val hbc
  have hca' := congrArg Fin.val hca
  rw [tgt_val, src_val] at hab' hbc' hca'
  have hb : b.val ∈ outN (tgtN a.val) := by rw [hab']; exact mem_outN b
  have hc : c.val ∈ outN (tgtN b.val) := by rw [hbc']; exact mem_outN c
  rcases h a.val a.isLt b.val hb c.val hc with h' | ⟨r, hr, hp⟩
  · exact absurd hca' h'
  · have hr' : ((Fin.ofNat 432 r.1, Fin.ofNat 432 r.2.1, Fin.ofNat 432 r.2.2) :
        Fin flagL.m × Fin flagL.m × Fin flagL.m) ∈ flagL.tri := by
      simp only [flagL, List.mem_map]; exact ⟨r, hr, rfl⟩
    obtain ⟨r', hr'', e1, e2, e3⟩ := mem_tri_iff hr'
    refine ⟨_, hr', finset_eq_of_perm3 (perm3_of_perm3B ?_)⟩
    obtain ⟨l1, l2, l3⟩ := tri_lt hr
    have f1 : (flagL.src (Fin.ofNat 432 r.1)).val = srcN r.1 := by
      rw [src_val, Fin.val_ofNat, Nat.mod_eq_of_lt l1]
    have f2 : (flagL.src (Fin.ofNat 432 r.2.1)).val = srcN r.2.1 := by
      rw [src_val, Fin.val_ofNat, Nat.mod_eq_of_lt l2]
    have f3 : (flagL.src (Fin.ofNat 432 r.2.2)).val = srcN r.2.2 := by
      rw [src_val, Fin.val_ofNat, Nat.mod_eq_of_lt l3]
    simp only
    rw [f1, f2, f3, src_val, src_val, src_val]
    exact hp

theorem flagL_check4 (t : Fin flagL.m × Fin flagL.m × Fin flagL.m) (ht : t ∈ flagL.tri)
    (v : Fin flagL.nv) (hv : v ∉ flagL.triVerts t) :
    ¬ (flagL.Adj v (flagL.src t.1) ∧ flagL.Adj v (flagL.src t.2.1) ∧
      flagL.Adj v (flagL.src t.2.2)) := by
  rintro ⟨⟨e, he1, he2⟩, h2, h3⟩
  obtain ⟨r, hr, e1, e2, e3⟩ := mem_tri_iff ht
  have h := check4B_eq
  simp only [check4B, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff] at h
  have hmem : (flagL.rev e).val ∈ outN (srcN r.1) := by
    rw [← e1, ← he2, ← flagL_rev_src, src_val]; exact mem_outN _
  have hv' : tgtN (flagL.rev e).val = v.val := by rw [← tgt_val, flagL_rev_tgt, he1]
  simp only [EdgeData.triVerts, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  have n1 : v.val ≠ srcN r.1 := by rw [← e1]; exact fun h => hv.1 (Fin.ext h)
  have n2 : v.val ≠ srcN r.2.1 := by rw [← e2]; exact fun h => hv.2.1 (Fin.ext h)
  have n3 : v.val ≠ srcN r.2.2 := by rw [← e3]; exact fun h => hv.2.2 (Fin.ext h)
  have a2 := adjN_of_adj h2; have a3 := adjN_of_adj h3
  rw [e2] at a2; rw [e3] at a3
  rcases h r hr _ hmem with ((h | h) | h) | h
  · exact n1 (hv' ▸ h)
  · exact n2 (hv' ▸ h)
  · exact n3 (hv' ▸ h)
  · rw [hv'] at h
    rcases h with h | h
    · rw [a2] at h; exact Bool.noConfusion h
    · rw [a3] at h; exact Bool.noConfusion h

theorem flagL_edge_unique (a b : Fin flagL.m) (hs : flagL.src a = flagL.src b)
    (ht : flagL.tgt a = flagL.tgt b) : a = b := by
  have h := edgeUniqB_eq
  simp only [edgeUniqB, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, beq_iff_eq] at h
  have hs' := congrArg Fin.val hs; have ht' := congrArg Fin.val ht
  rw [src_val, src_val] at hs'; rw [tgt_val, tgt_val] at ht'
  have hb : b.val ∈ outN (srcN a.val) := by rw [hs']; exact mem_outN b
  rcases h a.val a.isLt b.val hb with h | h
  · exact absurd ht'.symm h
  · exact (Fin.ext h).symm

theorem flagL_no_loop : ∀ a : Fin flagL.m, flagL.src a ≠ flagL.tgt a := by decide +kernel
theorem flagL_rev_rev : ∀ a : Fin flagL.m, flagL.rev (flagL.rev a) = a := by decide +kernel
theorem flagL_rev_ne : ∀ a : Fin flagL.m, flagL.rev a ≠ a := by decide +kernel

theorem flagL_tri_distinct : ∀ t ∈ flagL.tri, flagL.src t.1 ≠ flagL.src t.2.1 ∧
    flagL.src t.1 ≠ flagL.src t.2.2 ∧ flagL.src t.2.1 ≠ flagL.src t.2.2 :=
  flagL_forall_tri (by decide +kernel)

theorem flagL_tri_pairwise : flagL.tri.Pairwise fun t t' =>
    ¬ Perm3 (flagL.src t.1, flagL.src t.2.1, flagL.src t.2.2)
      (flagL.src t'.1, flagL.src t'.2.1, flagL.src t'.2.2) := by decide +kernel

theorem perm3_of_finset_eq {α : Type} [DecidableEq α] {x y z p q r : α} (hx : x ≠ y) (hy : x ≠ z)
    (hz : y ≠ z) (h : ({p, q, r} : Finset α) = {x, y, z}) : Perm3 (p, q, r) (x, y, z) := by
  have hp : p ∈ ({x, y, z} : Finset α) := h ▸ by simp
  have hq : q ∈ ({x, y, z} : Finset α) := h ▸ by simp
  have hr : r ∈ ({x, y, z} : Finset α) := h ▸ by simp
  have hx' : x ∈ ({p, q, r} : Finset α) := h.symm ▸ by simp
  have hy' : y ∈ ({p, q, r} : Finset α) := h.symm ▸ by simp
  have hz' : z ∈ ({p, q, r} : Finset α) := h.symm ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq hr hx' hy' hz'
  have hx2 := hx.symm; have hy2 := hy.symm; have hz2 := hz.symm
  unfold Perm3
  simp only
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl <;> simp_all

/-- **`flagL` is a flag simplicial complex.** -/
theorem flagL_isFlagComplex : flagL.IsFlagComplex where
  no_loop := flagL_no_loop
  rev_rev := flagL_rev_rev
  rev_ne := flagL_rev_ne
  edge_unique := flagL_edge_unique
  tri_card t ht := by
    obtain ⟨h1, h2, h3⟩ := flagL_tri_distinct t ht
    exact Finset.card_eq_three.2 ⟨_, _, _, h1, h2, h3, rfl⟩
  tri_nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    refine flagL_tri_pairwise.imp_of_mem fun {t t'} _ ht' hne he => hne ?_
    obtain ⟨h1, h2, h3⟩ := flagL_tri_distinct t' ht'
    exact perm3_of_finset_eq h1 h2 h3 he
  flag := EdgeData.flag_of_checks _ flagL_check3 flagL_check4

/-- Boolean walk test. -/
def walkB (D : EdgeData) : Fin D.nv → List (Fin D.m) → Fin D.nv → Bool
  | u, [], v => decide (u = v)
  | u, a :: w, v => decide (D.src a = u) && walkB D (D.tgt a) w v

theorem isWalk_of_walkB (D : EdgeData) : ∀ (u : Fin D.nv) (w : List (Fin D.m)) (v : Fin D.nv),
    walkB D u w v = true → EdgeData.IsWalk D u w v
  | u, [], v, h => by simpa [walkB, EdgeData.IsWalk] using h
  | u, a :: w, v, h => by
    simp only [walkB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, isWalk_of_walkB D _ w v h.2⟩

theorem flagL_walkB : ∀ v : Fin flagL.nv, walkB flagL flagL.root (flagL.path v) v = true := by
  decide +kernel

/-- **Connectedness data**: every root path is a walk from the root. -/
theorem flagL_connected : ∀ v : Fin flagL.nv, EdgeData.IsWalk flagL flagL.root (flagL.path v) v :=
  fun v => isWalk_of_walkB _ _ _ _ (flagL_walkB v)

end TheoremA.Leary
