module

public import Mathlib

/-!
# Power substitutions of free groups are injective

For `k : α → ℕ` with `k a ≥ 1` for every `a`, the endomorphism `powSubst k` of `FreeGroup α`
sending each generator `a` to `a ^ k a` is injective (`powSubst_injective`).

Proof: on raw words, `powSubst k` is the substitution `powFlat k` replacing each letter `p` by
`k p.1` copies of `p`.  It maps reduced words to reduced words, and it is injective on lists.
-/

@[expose] public section

namespace TheoremA.Kernel

open FreeGroup

variable {α : Type*}

/-- Replace every letter `p` by `k p.1` copies of it. -/
def powFlat (k : α → ℕ) (L : List (α × Bool)) : List (α × Bool) :=
  L.flatMap fun p => List.replicate (k p.1) p

/-- The power substitution `a ↦ a ^ k a`. -/
def powSubst (k : α → ℕ) : FreeGroup α →* FreeGroup α := FreeGroup.lift fun a => of a ^ k a

theorem mk_replicate (p : α × Bool) (n : ℕ) : mk (List.replicate n p) = mk [p] ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ', ← FreeGroup.mul_mk, ih, pow_succ]

theorem mk_single_false (a : α) : (mk [(a, false)] : FreeGroup α) = (of a)⁻¹ := by
  simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]

theorem powSubst_mk_single (k : α → ℕ) (p : α × Bool) :
    powSubst k (mk [p]) = mk [p] ^ k p.1 := by
  obtain ⟨a, b⟩ := p
  cases b
  · rw [mk_single_false, _root_.map_inv]
    simp [powSubst, inv_pow]
  · show powSubst k (of a) = of a ^ k a
    simp [powSubst]

theorem powSubst_mk (k : α → ℕ) (L : List (α × Bool)) :
    powSubst k (mk L) = mk (powFlat k L) := by
  induction L with
  | nil => simp [powFlat]; rfl
  | cons p L ih =>
    rw [show (p :: L) = [p] ++ L from rfl, ← FreeGroup.mul_mk, _root_.map_mul, ih,
      show powFlat k ([p] ++ L) = List.replicate (k p.1) p ++ powFlat k L by simp [powFlat],
      ← FreeGroup.mul_mk, mk_replicate, powSubst_mk_single]

theorem powFlat_cons (k : α → ℕ) (p : α × Bool) (L : List (α × Bool)) :
    powFlat k (p :: L) = List.replicate (k p.1) p ++ powFlat k L := by
  simp [powFlat]

theorem head?_powFlat_cons (k : α → ℕ) (hk : ∀ a, 0 < k a) (p : α × Bool)
    (L : List (α × Bool)) : (powFlat k (p :: L)).head? = some p := by
  rw [powFlat_cons]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (hk p.1).ne'
  rw [hn, List.replicate_succ]
  rfl

theorem isReduced_powFlat (k : α → ℕ) (hk : ∀ a, 0 < k a) :
    ∀ L : List (α × Bool), FreeGroup.IsReduced L → FreeGroup.IsReduced (powFlat k L)
  | [], _ => by simp [powFlat]
  | [p], _ => by
    rw [powFlat_cons]
    simp only [powFlat, List.flatMap_nil, List.append_nil]
    unfold FreeGroup.IsReduced
    exact List.isChain_replicate_of_rel _ (fun _ => rfl)
  | p :: q :: L, h => by
    rw [FreeGroup.isReduced_cons_cons] at h
    have ih := isReduced_powFlat k hk (q :: L) h.2
    rw [powFlat_cons]
    unfold FreeGroup.IsReduced
    rw [List.isChain_append]
    refine ⟨List.isChain_replicate_of_rel _ (fun _ => rfl), ih, ?_⟩
    intro x hx y hy
    rw [head?_powFlat_cons k hk] at hy
    have hx' : x = p := by
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (hk p.1).ne'
      rw [hn, List.getLast?_replicate] at hx
      simpa using hx.symm
    simp only [Option.mem_def, Option.some.injEq] at hy
    subst hx' hy
    exact h.1

theorem powFlat_injective (k : α → ℕ) (hk : ∀ a, 0 < k a) :
    ∀ L L' : List (α × Bool), powFlat k L = powFlat k L' → L = L'
  | [], [], _ => rfl
  | [], q :: L', h => by
    have := head?_powFlat_cons k hk q L'
    rw [← h] at this; simp [powFlat] at this
  | p :: L, [], h => by
    have := head?_powFlat_cons k hk p L
    rw [h] at this; simp [powFlat] at this
  | p :: L, q :: L', h => by
    have hpq : p = q := by
      have h1 := head?_powFlat_cons k hk p L
      rw [h, head?_powFlat_cons k hk q L'] at h1
      exact (Option.some.inj h1).symm
    subst hpq
    rw [powFlat_cons, powFlat_cons] at h
    rw [powFlat_injective k hk L L' (List.append_cancel_left h)]

/-- **Power substitutions are injective.** -/
theorem powSubst_injective (k : α → ℕ) (hk : ∀ a, 0 < k a) :
    Function.Injective (powSubst k) := by
  classical
  intro x y hxy
  rw [← FreeGroup.mk_toWord (x := x), ← FreeGroup.mk_toWord (x := y), powSubst_mk,
    powSubst_mk] at hxy
  have h := congrArg FreeGroup.toWord hxy
  rw [FreeGroup.toWord_mk, FreeGroup.toWord_mk,
    (isReduced_powFlat k hk _ FreeGroup.isReduced_toWord).reduce_eq,
    (isReduced_powFlat k hk _ FreeGroup.isReduced_toWord).reduce_eq] at h
  exact FreeGroup.toWord_injective (powFlat_injective k hk _ _ h)

end TheoremA.Kernel
