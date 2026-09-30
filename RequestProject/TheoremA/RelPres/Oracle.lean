module

public import Mathlib

/-!
# Closure facts for Mathlib's `RecursiveIn`

The encoded relative presentations use Mathlib's natural-number relation `Nat.RecursiveIn O`
(on `ℕ →. ℕ`), kept under the local name `RecursiveIn`. We derive the closure properties
needed for relative presentations from its constructors:

* `RecursiveIn.of_partrec` — every oracle-free partial recursive function is recursive in `O`;
* `RecursiveIn.comp_primrec` — precomposition with a primitive recursive function;
* `RecursiveIn.guard` — the guarded call `pair a 0 ↦ 0`, `pair a 1 ↦ f a`, which does not
  evaluate `f` on the `0` branch (built from `prec`);
* `RecursiveIn.cond` — branching on a primitive recursive Boolean test **before** evaluating
  either branch, so that divergence of the unused branch is irrelevant.
-/

@[expose] public section

namespace TheoremA.RelPres

/-- The natural-number oracle relation used by the encoded relative presentations. -/
abbrev RecursiveIn (O : Set (ℕ →. ℕ)) (f : ℕ →. ℕ) : Prop := Nat.RecursiveIn O f

namespace RecursiveIn
export Nat.RecursiveIn (zero succ left right oracle pair comp prec rfind)
end RecursiveIn

open Nat.Partrec

variable {O : Set (ℕ →. ℕ)}

/-- Every partial recursive function is recursive relative to any set of oracles. -/
theorem RecursiveIn.of_partrec {f : ℕ →. ℕ} (hf : Nat.Partrec f) : RecursiveIn O f := by
  induction hf with
  | zero => exact RecursiveIn.zero
  | succ => exact RecursiveIn.succ
  | left => exact RecursiveIn.left
  | right => exact RecursiveIn.right
  | pair _ _ ih₁ ih₂ => exact RecursiveIn.pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact RecursiveIn.comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact RecursiveIn.prec ih₁ ih₂
  | rfind _ ih => exact RecursiveIn.rfind ih

/-- Precomposition with a primitive recursive function. -/
theorem RecursiveIn.comp_primrec {f : ℕ →. ℕ} (hf : RecursiveIn O f) {g : ℕ → ℕ}
    (hg : Primrec g) : RecursiveIn O fun n => f (g n) := by
  have hg' : RecursiveIn O (fun n => (g n : Part ℕ)) :=
    RecursiveIn.of_partrec (Partrec.nat_iff.1 hg.to_comp.partrec)
  have := RecursiveIn.comp hf hg'
  simpa using this

/-- The guarded call: on `pair a 0` it returns `0` without calling `f`; on `pair a 1` it
returns `f a`. -/
theorem RecursiveIn.guard {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
    ∃ G : ℕ →. ℕ, RecursiveIn O G ∧ (∀ a, G (Nat.pair a 0) = Part.some 0) ∧
      ∀ a, G (Nat.pair a 1) = f a := by
  have hH : RecursiveIn O fun q => f (Nat.unpair q).1 :=
    RecursiveIn.comp_primrec hf (Primrec.fst.comp Primrec.unpair)
  refine ⟨_, RecursiveIn.prec (RecursiveIn.zero (O := O)) hH, ?_, ?_⟩
  · intro a; simp; rfl
  · intro a; simp; exact Part.bind_some 0 _

/-- **Conditional closure.**  Branching on a primitive recursive test, decided *before*
either branch is evaluated: on inputs with `c m = true` the result is `f m`, even if `g m`
diverges, and symmetrically. -/
theorem RecursiveIn.cond {c : ℕ → Bool} (hc : Primrec c) {f g : ℕ →. ℕ}
    (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    RecursiveIn O fun m => bif c m then f m else g m := by
  obtain ⟨Gf, hGf, hGf0, hGf1⟩ := RecursiveIn.guard hf
  obtain ⟨Gg, hGg, hGg0, hGg1⟩ := RecursiveIn.guard hg
  have hFf : RecursiveIn O fun m => Gf (Nat.pair m (bif c m then 1 else 0)) :=
    RecursiveIn.comp_primrec hGf
      (Primrec₂.natPair.comp Primrec.id (Primrec.cond hc (Primrec.const 1) (Primrec.const 0)))
  have hFg : RecursiveIn O fun m => Gg (Nat.pair m (bif c m then 0 else 1)) :=
    RecursiveIn.comp_primrec hGg
      (Primrec₂.natPair.comp Primrec.id (Primrec.cond hc (Primrec.const 0) (Primrec.const 1)))
  have hId : RecursiveIn O fun n => Part.some n := RecursiveIn.of_partrec Nat.Partrec.some
  have hP := RecursiveIn.pair hId (RecursiveIn.pair hFf hFg)
  have hsel : Primrec fun q : ℕ =>
      bif c (Nat.unpair q).1 then (Nat.unpair (Nat.unpair q).2).1
        else (Nat.unpair (Nat.unpair q).2).2 :=
    Primrec.cond (hc.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hS : RecursiveIn O fun q : ℕ => (Part.some (bif c (Nat.unpair q).1 then
      (Nat.unpair (Nat.unpair q).2).1 else (Nat.unpair (Nat.unpair q).2).2)) :=
    RecursiveIn.of_partrec (Partrec.nat_iff.1 hsel.to_comp.partrec)
  have := RecursiveIn.comp hS hP
  convert this using 1
  funext m
  cases h : c m
  · simp only [cond_false, hGf0, hGg1]
    apply Part.ext; intro x; simp [Seq.seq, h]
  · simp only [cond_true, hGf1, hGg0]
    apply Part.ext; intro x; simp [Seq.seq, h]

end TheoremA.RelPres
