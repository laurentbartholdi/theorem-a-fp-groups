module

public import RequestProject.TheoremA.Defs
public import RequestProject.FanoTriples

/-!
# Theorem A: statement and reduction to the manuscript's ingredients

We state Theorem A and prove, without `sorry`, that it follows from three ingredients of the
manuscript, each stated here as a `Prop`:

* `Lemma31` — Lemma 3.1 (developability: girth `≥ 12` makes every `ι_v : G → K_Σ(G)` injective);
* `Corollary52` — Corollary 5.2 (diagram criterion: an `FP_m` group, `m ≥ 2`, with endomorphisms
  satisfying the relations of `Σ` and `α_0` injective has an `FP_{m+1}` ascending HNN extension);
  it combines Corollary 4.3 and Proposition 5.1 and uses only the row identity `aW = e_0`;
* `UniversalBases` — the content of Lemmas 6.1, 6.2 and 3.2 used in §7: for a countable `G` there
  is a class `𝒞` of groups (in the manuscript: finitely generated groups with a presentation
  recursively enumerable relative to an oracle `R` encoding `G`) such that some `FP_2` group
  `B ∈ 𝒞` contains `G` and a copy of every member of `𝒞`, and `𝒞` is closed under `K_Σ` and under
  ascending HNN extensions.

The finite input is now Proposition 3.2 of the revised manuscript:
`FanoTriples.exists_tripleSystem`, with 23 indices and 15 triples constructed from the
flags of the Fano plane. Its finite checks are evaluated by Lean's kernel.
The earlier 400-index and 1155-index examples are not imported or used here.
The historical names `Lemma31`, `Corollary52` and `proposition_7_1` are retained for
compatibility; in the revised manuscript these are Lemma 4.1, Corollary 6.1 and
the induction in Theorem 7.3, respectively.
The induction of Proposition 7.1 and the final argument of §7 are `proposition_7_1` and
`theoremA_of_ingredients`.
-/

@[expose] public section

namespace TheoremA

open TripleSystem

universe u

/-- **Theorem A** (statement).  For every finite `n ≥ 2` and every countable group `G` there is an
embedding `G ↪ E` with `E` of type `FP_n`. -/
def TheoremAStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (G : Type u) [Group G] [Countable G],
    ∃ (E : Type u) (_ : Group E), IsFP n E ∧ ∃ f : G →* E, Function.Injective f

/-- **Lemma 3.1** (statement).  If the incidence graph of `Σ` has girth at least twelve, every
`ι_v : G → K_Σ(G)` is injective, for every group `G`. -/
def Lemma31 : Prop :=
  ∀ (r : ℕ) (T : List Triple), WellFormed r T → 12 ≤ (incidenceGraph r T).egirth →
    ∀ (G : Type u) [Group G] (v : Fin r), Function.Injective (diagramGroup.ι r T G v)

/-- **Corollary 5.2** (statement, for any triple system with an integral row identity).
If `B` has type `FP_m` (`m ≥ 2`), its endomorphisms `α_v` satisfy the relations of `Σ`, and `α_0`
is injective, then the ascending HNN extension along `α_0` has type `FP_{m+1}`. -/
def Corollary52 : Prop :=
  ∀ (r : ℕ) (T : List Triple) (a : Fin T.length → ℤ) (hr : 0 < r),
    WellFormed r T → RowIdentity r T a →
    ∀ (m : ℕ), 2 ≤ m → ∀ (B : Type u) [Group B], IsFP m B →
      ∀ α : Fin r → B →* B, DiagramRelations r T α →
        ∀ hinj : Function.Injective (α ⟨0, hr⟩), IsFP (m + 1) (ascHNN (α ⟨0, hr⟩) hinj)

/-- **Universal bases** (the input from §6 and Lemma 3.2).  For every finite triple system and
every countable group `G` there is a class `𝒞` of groups with an `FP_2` member `B` that contains
`G` and a copy of every member of `𝒞`, such that `𝒞` is closed under `K_Σ` and under ascending HNN
extensions. -/
def UniversalBases : Prop :=
  ∀ (r : ℕ) (T : List Triple) (G : Type u) [Group G] [Countable G],
    ∃ 𝒞 : ∀ (X : Type u) [Group X], Prop,
      (∃ (B : Type u) (_ : Group B), 𝒞 B ∧ IsFP 2 B ∧ (∃ f : G →* B, Function.Injective f) ∧
        ∀ (Y : Type u) [Group Y], 𝒞 Y → ∃ f : Y →* B, Function.Injective f) ∧
      (∀ (X : Type u) [Group X], 𝒞 X → 𝒞 (diagramGroup r T X)) ∧
      (∀ (X : Type u) [Group X], 𝒞 X →
        ∀ (φ : X →* X) (hφ : Function.Injective φ), 𝒞 (ascHNN φ hφ))

/-- The maps `α_v = j ∘ ι_v` satisfy the commuting-product relations of `Σ` (eq. (3.1)). -/
theorem diagramRelations_comp (r : ℕ) (T : List Triple) {B : Type*} [Group B]
    (j : diagramGroup r T B →* B) :
    DiagramRelations r T (fun v => j.comp (diagramGroup.ι r T B v)) := by
  intro t ht hi hj hk
  have mem : ∀ x ∈ relators r T B,
      QuotientGroup.mk' (Subgroup.normalClosure (relators r T B)) x = 1 := by
    intro x hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.subset_normalClosure hx
  constructor
  · intro b c
    have h := mem _ ⟨t, ht, hi, hj, hk, Or.inl ⟨b, c, rfl⟩⟩
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at h
    exact h.map j
  · intro b
    have h := mem _ ⟨t, ht, hi, hj, hk, Or.inr ⟨b, rfl⟩⟩
    simp only [map_mul, map_inv] at h
    have : diagramGroup.ι r T B ⟨t.2.2, hk⟩ b =
        diagramGroup.ι r T B ⟨t.1, hi⟩ b * diagramGroup.ι r T B ⟨t.2.1, hj⟩ b := by
      rw [mul_assoc, inv_mul_eq_one] at h
      exact h
    simp only [MonoidHom.comp_apply, this, map_mul]

/-- **Proposition 7.1** (abstract form).  Given the ingredients, for every `m ≥ 2` there is an
`FP_m` group in `𝒞` containing `G` and a copy of every member of `𝒞`. -/
theorem proposition_7_1 (h31 : Lemma31.{u}) (h52 : Corollary52.{u}) (r : ℕ) (T : List Triple)
    (a : Fin T.length → ℤ) (hr : 0 < r) (hw : WellFormed r T)
    (hg : 12 ≤ (incidenceGraph r T).egirth) (ha : RowIdentity r T a)
    (G : Type u) [Group G] (𝒞 : ∀ (X : Type u) [Group X], Prop)
    (hbase : ∃ (B : Type u) (_ : Group B), 𝒞 B ∧ IsFP 2 B ∧ (∃ f : G →* B, Function.Injective f) ∧
        ∀ (Y : Type u) [Group Y], 𝒞 Y → ∃ f : Y →* B, Function.Injective f)
    (hK : ∀ (X : Type u) [Group X], 𝒞 X → 𝒞 (diagramGroup r T X))
    (hH : ∀ (X : Type u) [Group X], 𝒞 X →
        ∀ (φ : X →* X) (hφ : Function.Injective φ), 𝒞 (ascHNN φ hφ))
    (m : ℕ) (hm : 2 ≤ m) :
    ∃ (B : Type u) (_ : Group B), 𝒞 B ∧ IsFP m B ∧ (∃ f : G →* B, Function.Injective f) ∧
        ∀ (Y : Type u) [Group Y], 𝒞 Y → ∃ f : Y →* B, Function.Injective f := by
  induction m, hm using Nat.le_induction with
  | base => exact hbase
  | succ m hm ih =>
    obtain ⟨B, _, hCB, hFP, ⟨f, hf⟩, huniv⟩ := ih
    obtain ⟨j, hj⟩ := huniv _ (hK B hCB)
    set α : Fin r → B →* B := fun v => j.comp (diagramGroup.ι r T B v) with hα
    have hinj : Function.Injective (α ⟨0, hr⟩) :=
      hj.comp (h31 r T hw hg B ⟨0, hr⟩)
    refine ⟨ascHNN (α ⟨0, hr⟩) hinj, inferInstance, hH B hCB _ hinj,
      h52 r T a hr hw ha m hm B hFP α (diagramRelations_comp r T j) hinj,
      ⟨HNNExtension.of.comp f, (ascHNN_of_injective _ hinj).comp hf⟩, ?_⟩
    intro Y _ hY
    obtain ⟨g, hg⟩ := huniv Y hY
    exact ⟨HNNExtension.of.comp g, (ascHNN_of_injective _ hinj).comp hg⟩

/-- **Theorem A from the ingredients.**  Lemma 3.1, Corollary 5.2 and the universal bases,
together with the Fano-plane system of Proposition 3.2, imply Theorem A. -/
theorem theoremA_of_ingredients (h31 : Lemma31.{u}) (h52 : Corollary52.{u})
    (hU : UniversalBases.{u}) : TheoremAStatement.{u} := by
  intro n hn G _ _
  obtain ⟨r, T, hr, hw, hg, a, ha⟩ := FanoTriples.exists_tripleSystem
  obtain ⟨𝒞, hbase, hK, hH⟩ := hU r T G
  obtain ⟨B, _, -, hFP, hGB, -⟩ :=
    proposition_7_1 h31 h52 r T a hr hw hg ha G 𝒞 hbase hK hH n hn
  exact ⟨B, inferInstance, hFP, hGB⟩

end TheoremA
