module

public import RequestProject.TheoremA.Lemma31.Picture.Raw
public import RequestProject.TheoremA.Lemma31.Picture.Split

/-!
# Labels under a vertex split

Splitting the vertex `(a, x₁, …, x_r, b, y₁, …, y_s)` into `(a, x₁, …, x_r)` and
`(b, y₁, …, y_s)` factors the old vertex word as `P * Q` (`CombMap.split_cycleWord`), where `P`
and `Q` are the words of the two new vertices read from `a` and `b`.

* `split_cycleWord_eq_inv` : at an ordinary vertex (`P * Q = 1`) only `Q = P⁻¹` follows;
* `split_cycleWord_right_eq_one` : if `P * Q = 1` and `P = 1` then `Q = 1`;
* `split_cycleWord_right_eq` : at a marked vertex with product `x`, if `P = 1` then `Q = x`;
* `split_labels_obstruction` : **the label obstruction** — an explicit map with labels in
  `Multiplicative (ZMod 2)` where the old vertex word is `g * g = 1` but both new words are
  `g ≠ 1`.  A label-preserving vertex split is therefore not automatically a picture move;
* `RawPicture.splitInterior` : **the conditional labelled move.**  Splitting an *interior*
  vertex of a raw picture between two *different faces*, under the explicit assumption that the
  new word `P` read from `a` is `1`, gives a raw picture for the same element (the other new word
  is then `1` as well).

Nothing here uses `NPC`, the girth, or reducedness.  The same-face split is not a raw picture
move: the split map is disconnected (`CombMap.split_sameFace_spherical`).
-/

@[expose] public section

namespace TheoremA

namespace Picture

open Equiv Function

section Words

variable {D G : Type*} [Finite D]

/-- A cycle word is trivial from one dart iff from any dart of the same cycle. -/
theorem cycleWord_eq_one_of_sameCycle [Group G] {π : Perm D} (f : D → G) {x y : D}
    (hxy : π.SameCycle x y) (h : cycleWord π f x = 1) : cycleWord π f y = 1 := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => simpa using h
  | succ n ih => rw [pow_succ', Perm.mul_apply, cycleWord_apply, ih]; group

/-- The word of a fixed point. -/
theorem cycleWord_of_fixed [Monoid G] {π : Perm D} (f : D → G) {x : D} (hx : π x = x) :
    cycleWord π f x = f x := by
  have : minimalPeriod π x = 1 :=
    minimalPeriod_eq_of (by norm_num) (by simpa using hx) (fun k hk hk' => by omega)
  simp [cycleWord, this]

end Words

namespace CombMap

variable {M : CombMap} {a b : M.D} {G : Type*}

/-- The old vertex word is the product `P * Q` of the two new vertex words. -/
theorem split_cycleWord [Monoid G] (f : M.D → G) (hab : a ≠ b) (hσ : M.σ.SameCycle a b) :
    cycleWord M.σ f a = cycleWord (M.split a b).σ f a * cycleWord (M.split a b).σ f b :=
  cycleWord_swap_mul_split f hab hσ

/-- At an ordinary vertex (`P * Q = 1`) one only gets `Q = P⁻¹`. -/
theorem split_cycleWord_eq_inv [Group G] (f : M.D → G) (hab : a ≠ b) (hσ : M.σ.SameCycle a b)
    (h : cycleWord M.σ f a = 1) :
    cycleWord (M.split a b).σ f b = (cycleWord (M.split a b).σ f a)⁻¹ := by
  rw [split_cycleWord f hab hσ] at h
  exact eq_inv_of_mul_eq_one_right h

/-- If `P * Q = 1` and `P = 1`, then `Q = 1`. -/
theorem split_cycleWord_right_eq_one [Group G] (f : M.D → G) (hab : a ≠ b)
    (hσ : M.σ.SameCycle a b) (h : cycleWord M.σ f a = 1)
    (hP : cycleWord (M.split a b).σ f a = 1) : cycleWord (M.split a b).σ f b = 1 := by
  rw [split_cycleWord_eq_inv f hab hσ h, hP, inv_one]

/-- At a marked vertex with product `x` (read from `a`), if `P = 1` then `Q = x`. -/
theorem split_cycleWord_right_eq [Monoid G] (f : M.D → G) (hab : a ≠ b)
    (hσ : M.σ.SameCycle a b) {x : G} (h : cycleWord M.σ f a = x)
    (hP : cycleWord (M.split a b).σ f a = 1) : cycleWord (M.split a b).σ f b = x := by
  rw [split_cycleWord f hab hσ, hP, one_mul] at h
  exact h

/-- **The label obstruction.**  On the digon, splitting the vertex `{0, 3}` with both darts
labelled by the involution `g = ofAdd 1` of `Multiplicative (ZMod 2)`: the old vertex word is
`g * g = 1`, but each of the two new vertex words is `g ≠ 1`. -/
theorem split_labels_obstruction :
    ∃ (M : CombMap) (a b : M.D) (f : M.D → Multiplicative (ZMod 2)),
      a ≠ b ∧ M.σ.SameCycle a b ∧ cycleWord M.σ f a = 1 ∧
      cycleWord (M.split a b).σ f a ≠ 1 ∧ cycleWord (M.split a b).σ f b ≠ 1 := by
  refine ⟨digon, (0 : Fin 4), (3 : Fin 4), fun _ => Multiplicative.ofAdd 1, show (0 : Fin 4) ≠ 3 by decide,
    ⟨1, by decide⟩, ?_, ?_, ?_⟩
  · rw [cycleWord_of_apply_apply _ _ _ (by decide) (by decide)]
    decide
  · rw [cycleWord_of_fixed _ (by decide)]
    decide
  · rw [cycleWord_of_fixed _ (by decide)]
    decide

end CombMap

end Picture

universe u w

namespace ConeComplex

open Picture Equiv Function

variable {V T : Type w} {C : ConeComplex.{u, w} V T} {x : Monoid.CoprodI C.loc}

section SplitInterior

variable (P : C.RawPicture x) {a b : P.M.D}

/-- Letter types are constant around an interior vertex. -/
theorem RawPicture.type_pow {d : P.M.D} (hd : ¬ P.M.σ.SameCycle P.base d) (n : ℕ) :
    (P.lab ((P.M.σ ^ n) d)).1 = (P.lab d).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, P.type_σ _ (fun h => hd (h.trans
      (sameCycle_of_pow_eq n rfl).symm)), ih]

theorem RawPicture.type_eq_of_sameCycle {d e : P.M.D} (hd : ¬ P.M.σ.SameCycle P.base d)
    (hde : P.M.σ.SameCycle d e) : (P.lab e).1 = (P.lab d).1 := by
  obtain ⟨n, rfl⟩ := hde.exists_nat_pow_eq
  exact P.type_pow hd n

variable {P}

/-- Away from the split vertex, the split rotation has the same iterates. -/
theorem RawPicture.split_pow_of_not {d : P.M.D} (hda : ¬ P.M.σ.SameCycle a d)
    (hdb : ¬ P.M.σ.SameCycle b d) (n : ℕ) :
    (((P.M.split a b).σ) ^ n) d = (P.M.σ ^ n) d :=
  swap_mul_pow_apply_of_not_sameCycle hda hdb n

/-- If the split vertex is interior, the marked vertex is unchanged. -/
theorem RawPicture.split_sameCycle_base_iff (hint : ¬ P.M.σ.SameCycle P.base a)
    (hσ : P.M.σ.SameCycle a b) {d : P.M.D} :
    (P.M.split a b).σ.SameCycle P.base d ↔ P.M.σ.SameCycle P.base d := by
  have ha : ¬ P.M.σ.SameCycle a P.base := fun h => hint h.symm
  have hb : ¬ P.M.σ.SameCycle b P.base := fun h => hint (h.symm.trans hσ.symm)
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    rw [RawPicture.split_pow_of_not ha hb n]
    exact sameCycle_of_pow_eq n rfl
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    rw [← RawPicture.split_pow_of_not ha hb n]
    exact sameCycle_of_pow_eq n rfl

/-- **Splitting an interior vertex of a raw picture (conditional labelled move).**  Let `a ≠ b` be
darts of the same interior vertex, lying in **different faces**, and assume explicitly that the
word `P` of the new vertex through `a` is `1`.  Then the split map with the same letters and the
same base dart is a raw picture for the same element `x`.  (The word `Q` of the new vertex
through `b` is then `P⁻¹ = 1`.) -/
def RawPicture.splitInterior (hab : a ≠ b) (hσ : P.M.σ.SameCycle a b)
    (hint : ¬ P.M.σ.SameCycle P.base a) (hφ : ¬ P.M.φ.SameCycle a b)
    (hP : cycleWord (P.M.split a b).σ (C.letterWord ∘ P.lab) a = 1) : C.RawPicture x where
  M := P.M.split a b
  lab := P.lab
  base := P.base
  connected := CombMap.split_connected P.connected hφ
  spherical := by rw [CombMap.split_euler_of_not_sameCycle_face hab hσ hφ, P.spherical]
  type_σ := by
    intro d hd
    rw [RawPicture.split_sameCycle_base_iff hint hσ] at hd
    show (P.lab (swap a b (P.M.σ d))).1 = (P.lab d).1
    have hd1 : ∀ e, P.M.σ d = e → P.M.σ.SameCycle d e := fun e he => ⟨1, by simpa using he⟩
    by_cases ha : P.M.σ d = a
    · rw [ha, swap_apply_left]
      exact P.type_eq_of_sameCycle hd ((hd1 a ha).trans hσ)
    · by_cases hb : P.M.σ d = b
      · rw [hb, swap_apply_right]
        exact P.type_eq_of_sameCycle hd ((hd1 b hb).trans hσ.symm)
      · rw [swap_apply_of_ne_of_ne ha hb]
        exact P.type_σ d hd
  local_eq := by
    intro d hd
    have hQ := CombMap.split_cycleWord_right_eq_one (C.letterWord ∘ P.lab) hab hσ
      (P.local_eq a hint) hP
    by_cases hda : (P.M.split a b).σ.SameCycle a d
    · exact cycleWord_eq_one_of_sameCycle _ hda hP
    by_cases hdb : (P.M.split a b).σ.SameCycle b d
    · exact cycleWord_eq_one_of_sameCycle _ hdb hQ
    rw [RawPicture.split_sameCycle_base_iff hint hσ] at hd
    have hpow : ∀ n : ℕ, (P.M.σ ^ n) d = ((P.M.split a b).σ ^ n) d := by
      intro n
      have := swap_mul_pow_apply_of_not_sameCycle hda hdb n
      rwa [CombMap.split_σ, swap_mul_swap_mul] at this
    rw [cycleWord_congr _ (fun n => (hpow n).symm)]
    exact P.local_eq d hd
  edge_interior := by
    intro d hd hd'
    rw [RawPicture.split_sameCycle_base_iff hint hσ] at hd hd'
    exact P.edge_interior d hd hd'
  edge_boundary := by
    intro d hd
    rw [RawPicture.split_sameCycle_base_iff hint hσ] at hd
    have := P.edge_boundary d hd
    rwa [RawPicture.split_sameCycle_base_iff hint hσ]
  boundary_word := by
    exact (cycleWord_congr _ (RawPicture.split_pow_of_not (fun h => hint h.symm)
      (fun h => hint (h.symm.trans hσ.symm)))).trans P.boundary_word

end SplitInterior

end ConeComplex

end TheoremA
