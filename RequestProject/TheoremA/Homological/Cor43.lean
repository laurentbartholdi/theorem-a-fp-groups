module

public import RequestProject.TheoremA.Homological.Comparison

/-!
# Corollary 4.3 from Lemma 4.2

`Lemma42` is the statement of Lemma 4.2 (commuting products); `cor43_of_lemma42` derives
Corollary 4.3 from it using the integral row identity `aW = e_0`.
-/

@[expose] public section

namespace TheoremA

open TripleSystem

universe u

/-- **Lemma 4.2 (commuting products)** (statement).  If `α, β` have commuting images and
`δ(b) = α(b) β(b)`, then for any chain lifts `Φ_α, Φ_β, Φ_δ` there is a finitely generated
submodule `N ⊆ S` with `(Φ_δ - Φ_α - Φ_β)(S) ⊆ N`. -/
def Lemma42 : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (B : Type u) [Group B] (R : Res B k) (α β δ : B →* B),
    (∀ b c, Commute (α b) (β c)) → (∀ b, δ b = α b * β b) →
    ∀ Φα Φβ Φδ, IsChainLift R α Φα → IsChainLift R β Φβ → IsChainLift R δ Φδ →
      ∃ N : Submodule (ZG B) (FreeMod B (R.c (k + 1))), N.FG ∧ N ≤ R.S ∧
        ∀ s ∈ R.S, Φδ (k + 1) s - Φα (k + 1) s - Φβ (k + 1) s ∈ N

theorem row_sum_eq {r : ℕ} {M : Type*} [AddCommGroup M] (t : Triple) (hi : t.1 < r)
    (hj : t.2.1 < r) (hk : t.2.2 < r) (F : Fin r → M) :
    ∑ v : Fin r, row t v • F v = F ⟨t.1, hi⟩ + F ⟨t.2.1, hj⟩ - F ⟨t.2.2, hk⟩ := by
  have key : ∀ (n : ℕ) (hn : n < r), ∑ v : Fin r, (if (v : ℕ) = n then (1 : ℤ) else 0) • F v =
      F ⟨n, hn⟩ := by
    intro n hn
    rw [Finset.sum_eq_single ⟨n, hn⟩]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ n := fun h => hb (Fin.ext h)
      simp [this]
    · simp
  simp only [row, add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [key _ hi, key _ hj, key _ hk]

/-- **Corollary 4.3** follows from Lemma 4.2. -/
theorem cor43_of_lemma42 (h42 : Lemma42.{u}) : Cor43.{u} := by
  intro r T a hr hw ha k hk B _ R α hα
  choose Φ hΦ using fun v : Fin r => exists_chainLift R (α v)
  -- the finitely generated submodule for each triple
  have hN : ∀ l : Fin T.length, ∃ N : Submodule (ZG B) (FreeMod B (R.c (k + 1))),
      N.FG ∧ N ≤ R.S ∧ ∀ s ∈ R.S,
        (∑ v : Fin r, row T[l] v • Φ v (k + 1) s) ∈ N := by
    intro l
    obtain ⟨hi, hj, hk', -, -, -⟩ := hw T[l] (List.getElem_mem _)
    have hrel := hα T[l] (List.getElem_mem _) hi hj hk'
    obtain ⟨N, hNfg, hNS, hsN⟩ := h42 k hk B R _ _ _ hrel.1 hrel.2 _ _ _
      (hΦ ⟨_, hi⟩) (hΦ ⟨_, hj⟩) (hΦ ⟨_, hk'⟩)
    refine ⟨N, hNfg, hNS, fun s hs => ?_⟩
    rw [row_sum_eq T[l] hi hj hk' (fun v => Φ v (k + 1) s)]
    have := N.neg_mem (hsN s hs)
    convert this using 1
    abel
  choose N hNfg hNS hsN using hN
  refine ⟨Φ ⟨0, hr⟩, hΦ _, ⨆ l, N l, ?_, iSup_le hNS, fun s hs => ?_⟩
  · exact Submodule.fg_iSup _ fun l => hNfg l
  · have hsum : Φ ⟨0, hr⟩ (k + 1) s =
        ∑ l : Fin T.length, a l • ∑ v : Fin r, row T[l] v • Φ v (k + 1) s := by
      have ha' : ∀ v : Fin r, ∑ l : Fin T.length, a l * row T[l] v =
          if (v : ℕ) = 0 then 1 else 0 := ha
      simp_rw [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, ha']
      rw [Finset.sum_eq_single ⟨0, hr⟩]
      · simp
      · intro b _ hb
        have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
        simp [this]
      · simp
    rw [hsum]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_of_tower_mem _ _ ?_
    exact Submodule.mem_iSup_of_mem l (hsN l s hs)

end TheoremA
