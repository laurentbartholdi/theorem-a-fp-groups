module

public import RequestProject.TheoremA.RelPres.CheckerComplete

/-!
# Universal evaluation relative to `χ_R`

`U R c x` searches (with `Nat.rfind`) for the least code `k = ⟨y, cert⟩` accepted by the total
checker `check R c x y cert`, and returns `y`.

* `U_eq` — `U R c x = eval R (decode c) x` (including divergence).
* `recursiveIn_U` — **uniformly** in the program: `p ↦ U R p.1 p.2` is recursive in `oracle R`.
* `exists_index` — every function recursive in `oracle R` is `U R c` for some index `c`
  (programs that never produce output are allowed).
-/

@[expose] public section

namespace TheoremA.RelPres

open OracleCode

variable {R : Set ℕ}

/-- **The universal relative evaluator**: search over pairs `⟨output, certificate⟩`. -/
noncomputable def U (R : Set ℕ) (c x : ℕ) : Part ℕ :=
  (Nat.rfind fun k => Part.some (check R c x (Nat.unpair k).1 (Nat.unpair k).2)).map
    fun k => (Nat.unpair k).1

/-- The universal evaluator agrees with evaluation of the decoded program. -/
theorem U_eq (R : Set ℕ) (c x : ℕ) : U R c x = eval R (decode c) x := by
  apply Part.ext
  intro w
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := (Part.mem_map_iff _).1 h
    have hs := Nat.rfind_spec hk
    exact mem_eval_of_check (Part.mem_some_iff.1 hs).symm
  · intro h
    obtain ⟨cert, hc⟩ := mem_eval_iff_exists_check.1 h
    obtain ⟨n, hn, -⟩ := Nat.rfind_min'
      (p := fun k => check R c x (Nat.unpair k).1 (Nat.unpair k).2) (m := Nat.pair w cert)
      (by simpa using hc)
    have hs := Nat.rfind_spec hn
    have hmem := mem_eval_of_check (Part.mem_some_iff.1 hs).symm
    have hw : (Nat.unpair n).1 = w := Part.mem_unique hmem h
    exact (Part.mem_map_iff _).2 ⟨n, hn, hw⟩

/-- **Uniform recursiveness of the universal evaluator.** -/
theorem recursiveIn_U :
    RecursiveIn (oracle R) fun p => U R (Nat.unpair p).1 (Nat.unpair p).2 := by
  let h : ℕ → ℕ := fun q => Nat.pair (Nat.unpair (Nat.unpair q).1).1
    (Nat.pair (Nat.unpair (Nat.unpair q).1).2
      (Nat.pair (Nat.unpair (Nat.unpair q).2).1 (Nat.unpair (Nat.unpair q).2).2))
  have hh : Primrec h := by
    refine Primrec₂.natPair.comp ?_ (Primrec₂.natPair.comp ?_ (Primrec₂.natPair.comp ?_ ?_))
    · exact Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
    · exact Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
    · exact Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
    · exact Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have h1 := RecursiveIn.comp_primrec (recursiveIn_checkFn (R := R)) hh
  have h2 := RecursiveIn.comp (RecursiveIn.of_primrec (O := oracle R)
    (Primrec.nat_sub.comp (Primrec.const 1) Primrec.id)) h1
  have h3 := RecursiveIn.rfind h2
  have h4 := RecursiveIn.comp (RecursiveIn.of_primrec (O := oracle R)
    (Primrec.fst.comp Primrec.unpair)) h3
  convert h4 using 1
  funext p
  simp only [U, checkFn, h, Nat.unpair_pair]
  rw [← Part.bind_some_eq_map]
  congr 2
  funext n
  cases check R (Nat.unpair p).1 (Nat.unpair p).2 (Nat.unpair n).1 (Nat.unpair n).2 <;> simp

/-- **Every function recursive in `oracle R` has an index for `U R`.** -/
theorem exists_index {f : ℕ →. ℕ} (hf : RecursiveIn (oracle R) f) :
    ∃ c, ∀ x, U R c x = f x := by
  obtain ⟨c, rfl⟩ := exists_code hf
  exact ⟨encode c, fun x => by rw [U_eq, decode_encode]⟩

end TheoremA.RelPres
