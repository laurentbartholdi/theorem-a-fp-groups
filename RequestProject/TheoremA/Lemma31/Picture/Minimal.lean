module

public import RequestProject.TheoremA.Lemma31.Picture.Extract

/-!
# Least-edge raw pictures for local letters, and the adjacent-marked-edges digon lemma

* `ConeComplex.LocalPicture` : a raw picture whose marked word is a single **nonidentity** letter
  `⟨k, g⟩` of **any** local group — an index group `A v` (`k = inl v`) or a triple group `B t`
  (`k = inr t`).
* `ConeComplex.LocalPicture.IsLeast` : least number of edges among **all** local pictures (over
  all local factors); `exists_isLeast` : a least one exists as soon as some local picture exists;
  `nonempty_of_ι_eq_one` : the existing raw-existence result gives one from any nonidentity
  `a : A v` with `ι_v a = 1`.
* `LocalPicture.IsLeast.sameFace_split` : in a least local picture, every same-face split of an
  interior vertex has `Q ≠ 1` and leaves at most one edge in the marked component (both
  configurations of `RawPicture.sameFace_extract` are ruled out).
* `LocalPicture.IsLeast.adjacent_marked_digon` : **adjacent marked edges with the same ordinary
  endpoint bound a digon**: if `d ≠ e` are consecutive darts at the marked vertex (`σ d = e`),
  and `u = α d`, `v = α e` lie at the same vertex, then `σ v = u`, and `(u, e)` is a face cycle
  of length two.
* `euler_le_one_of_exceptional_counts` : a counting observation only (see its docstring).

Nothing here uses `NPC`, girth, or injectivity into the colimit, and nothing here is a statement
about digon consolidation, merging distinct endpoints, removing identity edges, or complete
marked-word normalization.
-/

@[expose] public section

namespace TheoremA

universe u w

namespace ConeComplex

open Picture Equiv Function

variable {V T : Type w} (C : ConeComplex.{u, w} V T)

/-- A raw picture whose marked word is a single nonidentity letter of some local group (an index
group `A v` or a triple group `B t`). -/
structure LocalPicture where
  /-- The local factor (index or triple). -/
  k : V ⊕ T
  /-- The letter. -/
  g : C.loc k
  ne_one : g ≠ 1
  /-- The raw picture. -/
  R : C.RawPicture (C.letterWord ⟨k, g⟩)

variable {C}

namespace RawPicture

/-- The digon lemma for any raw picture in which every same-face split of an interior vertex
leaves at most one edge in the marked component (the conclusion of
`LocalPicture.IsLeast.sameFace_split`). -/
theorem adjacent_marked_digon_of_small {x : Monoid.CoprodI C.loc} (R : C.RawPicture x)
    (hsmall : ∀ a b : R.M.D, a ≠ b → R.M.σ.SameCycle a b → R.M.φ.SameCycle a b →
      ¬ R.M.σ.SameCycle R.base a → ((R.M.split a b).component R.base).numEdges < 2)
    {d e : R.M.D} (hd : R.M.σ.SameCycle R.base d) (hde : R.M.σ d = e) (hne : d ≠ e)
    (hX : R.M.σ.SameCycle (R.M.α d) (R.M.α e)) :
    R.M.σ (R.M.α e) = R.M.α d ∧ R.M.φ (R.M.α d) = e ∧
      R.M.φ e = R.M.α d ∧ R.M.α d ≠ e := by
  have he : R.M.σ.SameCycle R.base e := hd.trans ⟨1, by simpa using hde⟩
  have hu : ¬ R.M.σ.SameCycle R.base (R.M.α d) := (R.edge_boundary d hd).1
  have hue : R.M.α d ≠ e := fun h => hu (h ▸ he)
  have hφu : R.M.φ (R.M.α d) = e := by
    change R.M.σ (R.M.α (R.M.α d)) = e
    rw [R.M.α_α, hde]
  have hφe : R.M.φ e = R.M.σ (R.M.α e) := rfl
  have key : R.M.σ (R.M.α e) = R.M.α d := by
    by_contra hne'
    have hab : R.M.α d ≠ R.M.σ (R.M.α e) := fun h => hne' h.symm
    have hσ : R.M.σ.SameCycle (R.M.α d) (R.M.σ (R.M.α e)) := hX.trans ⟨1, by simp⟩
    have hφ : R.M.φ.SameCycle (R.M.α d) (R.M.σ (R.M.α e)) :=
      ⟨2, by rw [zpow_two, Perm.mul_apply, hφu, hφe]⟩
    have h2 := hsmall _ _ hab hσ hφ hu
    apply absurd h2
    push_neg
    have hconn : ∀ y, R.M.σ.SameCycle R.base y →
        Relation.EqvGen (R.M.split (R.M.α d) (R.M.σ (R.M.α e))).Step R.base y := fun y hy =>
      (R.M.split _ _).eqvGen_of_sameCycle
        ((RawPicture.split_sameCycle_base_iff (fun h => hu h) hσ).2 hy)
    classical
    refine two_le_numOrbits _ (d := ⟨d, hconn d hd⟩) (e := ⟨e, hconn e he⟩) fun h => ?_
    have h' := (CombMap.restrict_α_sameCycle_iff _ _ _).1 h
    rcases (sameCycle_involution_iff R.M.α_α).1 h' with h1 | h1
    · exact hne h1.symm
    · exact hue h1.symm
  exact ⟨key, hφu, by rw [hφe, key], hue⟩

end RawPicture

namespace LocalPicture

/-- `L` has the least number of edges among all local pictures, over all local factors. -/
def IsLeast (L : C.LocalPicture) : Prop := ∀ L' : C.LocalPicture, L.R.M.numEdges ≤ L'.R.M.numEdges

/-- If some local picture exists, a least-edge one exists. -/
theorem exists_isLeast (h : Nonempty C.LocalPicture) : ∃ L : C.LocalPicture, L.IsLeast := by
  classical
  have hex : ∃ n, ∃ L : C.LocalPicture, L.R.M.numEdges = n := ⟨_, h.some, rfl⟩
  obtain ⟨L, hL⟩ := Nat.find_spec hex
  exact ⟨L, fun L' => hL ▸ Nat.find_min' hex ⟨L', rfl⟩⟩

/-- A nonidentity element of an index group that dies in the colimit gives a local picture (the
existing raw-existence result, without `NPC` or girth). -/
theorem nonempty_of_ι_eq_one {v : V} {a : C.A v} (ha : a ≠ 1) (h : C.ι (Sum.inl v) a = 1) :
    Nonempty C.LocalPicture :=
  ⟨⟨Sum.inl v, a, ha, (exists_rawPicture_of_ι_eq_one h).some⟩⟩

/-- Hence under the original counterexample assumption the least-edge class is nonempty. -/
theorem exists_isLeast_of_ι_eq_one {v : V} {a : C.A v} (ha : a ≠ 1) (h : C.ι (Sum.inl v) a = 1) :
    ∃ L : C.LocalPicture, L.IsLeast :=
  exists_isLeast (nonempty_of_ι_eq_one ha h)

variable {L : C.LocalPicture}

/-- **Minimality rules out both extraction cases.**  In a least local picture, a split of an
interior vertex at distinct darts `a`, `b` of the same vertex and of the same face has `Q ≠ 1`
(`Q = splitQ`, the product at the piece outside the marked component) and leaves at most one
edge in the component of the mark. -/
theorem IsLeast.sameFace_split (hL : L.IsLeast) {a b : L.R.M.D} (hab : a ≠ b)
    (hσ : L.R.M.σ.SameCycle a b) (hφ : L.R.M.φ.SameCycle a b)
    (hint : ¬ L.R.M.σ.SameCycle L.R.base a) :
    L.R.splitQ a b ≠ 1 ∧ ((L.R.M.split a b).component L.R.base).numEdges < 2 := by
  have hQ : L.R.splitQ a b ≠ 1 := by
    intro hQ
    have h1 : L.R.M.numEdges ≤ (L.R.splitRetain hab hσ hφ hint hQ).M.numEdges :=
      hL ⟨L.k, L.g, L.ne_one, L.R.splitRetain hab hσ hφ hint hQ⟩
    have := L.R.splitRetain_numEdges_lt hab hσ hφ hint hQ
    omega
  refine ⟨hQ, ?_⟩
  by_contra hMo
  push_neg at hMo
  have h1 : L.R.M.numEdges ≤ (L.R.splitDefect hab hσ hφ hint).cap.M.numEdges :=
    hL ⟨_, _, hQ, (L.R.splitDefect hab hσ hφ hint).cap⟩
  have := L.R.splitDefect_cap_numEdges_add_one_le hab hσ hφ hint hMo
  omega

/-- **Adjacent marked edges with the same ordinary endpoint bound a digon.**  In a least local
picture, let `d ≠ e` be consecutive darts at the marked vertex (`σ d = e`), and suppose
`u = α d` and `v = α e` lie at the same vertex `X` (necessarily ordinary).  Then `σ v = u`;
moreover `φ u = e` and `φ e = u` with `u ≠ e`, i.e. the two edges bound a face of length two.

The proof splits `X` at `u` and `σ v` (not at `u`, `v`): these lie in the same face because
`φ u = e` and `φ e = σ v`. -/
theorem IsLeast.adjacent_marked_digon (hL : L.IsLeast) {d e : L.R.M.D}
    (hd : L.R.M.σ.SameCycle L.R.base d) (hde : L.R.M.σ d = e) (hne : d ≠ e)
    (hX : L.R.M.σ.SameCycle (L.R.M.α d) (L.R.M.α e)) :
    L.R.M.σ (L.R.M.α e) = L.R.M.α d ∧ L.R.M.φ (L.R.M.α d) = e ∧
      L.R.M.φ e = L.R.M.α d ∧ L.R.M.α d ≠ e :=
  RawPicture.adjacent_marked_digon_of_small L.R
    (fun _ _ hab hσ hφ hint => (hL.sameFace_split hab hσ hφ hint).2) hd hde hne hX

end LocalPicture

end ConeComplex

/-- **A counting observation (not a witness theorem).**  If `ε_I + ε_T = 1` and
`2 (V_I - ε_I) ≤ E`, `3 (V_T - ε_T) ≤ E`, `12 F ≤ 2 E`, then `V_I + V_T - E + F ≤ 1`.  This only
shows that one exceptional vertex of either kind does not spoil the Euler estimate; producing a
typed exceptional vertex with these degree bounds and face bounds is **not** established here. -/
theorem euler_le_one_of_exceptional_counts {VI VT E F εI εT : ℤ} (hε : εI + εT = 1)
    (hI : 2 * (VI - εI) ≤ E) (hT : 3 * (VT - εT) ≤ E) (hF : 12 * F ≤ 2 * E) :
    VI + VT - E + F ≤ 1 := by
  linarith

end TheoremA
