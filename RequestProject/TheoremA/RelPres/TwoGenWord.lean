module

public import RequestProject.TheoremA.RelPres.TwoGenHNN
public import RequestProject.TheoremA.RelPres.OmegaPres

/-!
# Two-generator embedding: raw-word substitution into a two-letter alphabet

The alphabet `Fin 2` has the letters `B = 0` and `T = 1`.

* `rwPow w m` — `m`-fold concatenation of the raw word `w` (no free reduction).
* `aWord = T B T⁻¹` and, for `m = n+1`,
  `wWord n = T aWord^(-m) B aWord^m T⁻¹ B^(-m) aWord⁻¹ B^m` (negative powers are powers of the
  formal inverse).  `eval_wWord`: its value is `wVal (of B) (of T) (n+1)`.
* `subst : RawWord ℕ → RawWord (Fin 2)` replaces the letter `n` by `wWord n` and `n⁻¹` by the
  formal inverse of `wWord n`; `eval_subst : eval (subst w) = thetaWord (eval w)`, where
  `thetaWord = FreeGroup.lift (n ↦ eval (wWord n))`.
* `primrec_wWord`, `primrec_subst` — computability for the structural word codes.
* `twoGenEnum e k = subst <$> e k`; `IsNatEnumerator.twoGenEnum` (same oracle `R`) and the exact
  relator-set identity `enumRelators_twoGenEnum`.
-/

@[expose] public section

namespace TheoremA.RelPres

open RawWord

namespace RawWord

variable {A : Type*}

/-- `m`-fold concatenation of a raw word. -/
def rwPow (w : RawWord A) (m : ℕ) : RawWord A := (fun v => w ++ v)^[m] []

@[simp] theorem eval_rwPow (w : RawWord A) (m : ℕ) : eval (rwPow w m) = eval w ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [rwPow, Function.iterate_succ_apply', ← rwPow, eval_append, ih, pow_succ']

theorem primrec_inv [Primcodable A] : Primrec (inv : RawWord A → RawWord A) :=
  Primrec.list_reverse.comp (Primrec.list_map Primrec.id
    (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.not.comp (Primrec.snd.comp Primrec.snd))).to₂)

theorem primrec_rwPow [Primcodable A] : Primrec₂ (rwPow : RawWord A → ℕ → RawWord A) :=
  (Primrec.nat_iterate (h := fun (p : RawWord A × ℕ) v => p.1 ++ v) Primrec.snd
    (Primrec.const []) (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂

end RawWord

/-- The letter `B`. -/
def letB : RawWord (Fin 2) := [(0, true)]
/-- The letter `T`. -/
def letT : RawWord (Fin 2) := [(1, true)]

/-- The raw word `A = T B T⁻¹`. -/
def aWord : RawWord (Fin 2) := [(1, true), (0, true), (1, false)]

/-- The raw word `W_n = T A^(-m) B A^m T⁻¹ B^(-m) A⁻¹ B^m`, `m = n+1`. -/
def wWord (n : ℕ) : RawWord (Fin 2) :=
  letT ++ rwPow (inv aWord) (n + 1) ++ letB ++ rwPow aWord (n + 1) ++ inv letT ++
    rwPow (inv letB) (n + 1) ++ inv aWord ++ rwPow letB (n + 1)

@[simp] theorem eval_letB : eval letB = FreeGroup.of 0 := rfl
@[simp] theorem eval_letT : eval letT = FreeGroup.of 1 := rfl

theorem eval_aWord :
    eval aWord = FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of (1 : Fin 2))⁻¹ := by
  rw [show aWord = letT ++ letB ++ inv letT from rfl]
  simp only [eval_append, eval_inv, eval_letB, eval_letT]

/-- **The value of `W_n`** is the group expression `wVal B T (n+1)`. -/
theorem eval_wWord (n : ℕ) : eval (wWord n) = wVal (FreeGroup.of 0) (FreeGroup.of 1) (n + 1) := by
  simp only [wWord, eval_append, eval_rwPow, eval_inv, eval_aWord, eval_letB, eval_letT, wVal,
    inv_pow, mul_assoc]

/-- Substitution of one signed letter. -/
def substLetter (p : ℕ × Bool) : RawWord (Fin 2) := bif p.2 then wWord p.1 else inv (wWord p.1)

/-- **Substitution** `n ↦ W_n`, `n⁻¹ ↦ W_n⁻¹` (formal inverse), then concatenation. -/
def subst (w : RawWord ℕ) : RawWord (Fin 2) := w.flatMap substLetter

/-- The free-group homomorphism `n ↦ eval W_n`. -/
def thetaWord : FreeGroup ℕ →* FreeGroup (Fin 2) := FreeGroup.lift fun n => eval (wWord n)

/-- **Evaluation rule for substitution.** -/
theorem eval_subst (w : RawWord ℕ) : eval (subst w) = thetaWord (eval w) := by
  induction w with
  | nil => simp [subst]
  | cons p w ih =>
    rw [subst, List.flatMap_cons, eval_append, ← subst, ih,
      show p :: w = [p] ++ w from rfl, eval_append, map_mul]
    congr 1
    obtain ⟨a, s⟩ := p
    cases s <;> simp [substLetter, thetaWord]

theorem primrec_wWord : Primrec wWord := by
  have hc : ∀ w : RawWord (Fin 2), Primrec fun n : ℕ => rwPow w (n + 1) := fun w =>
    primrec_rwPow.comp (Primrec.const w) Primrec.succ
  unfold wWord
  refine Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp
    (Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp
    (Primrec.list_append.comp (Primrec.const _) (hc _)) (Primrec.const _)) (hc _))
    (Primrec.const _)) (hc _)) (Primrec.const _)) (hc _)

theorem primrec_substLetter : Primrec substLetter :=
  Primrec.cond Primrec.snd (primrec_wWord.comp Primrec.fst)
    (primrec_inv.comp (primrec_wWord.comp Primrec.fst))

/-- **Substitution is primitive recursive** on the structural word codes. -/
theorem primrec_subst : Primrec subst :=
  Primrec.list_flatMap Primrec.id (primrec_substLetter.comp Primrec.snd).to₂

/-! ### The two-letter enumerator -/

/-- The two-letter enumerator `e₂(k) = subst <$> e(k)`; undefined inputs stay undefined. -/
def twoGenEnum (E : ℕ →. RawWord ℕ) : ℕ →. RawWord (Fin 2) := fun k => (E k).map subst

variable {R : Set ℕ}

/-- **`e₂` is an `R`-enumerator** on `Fin 2`, with the same oracle. -/
theorem IsNatEnumerator.twoGenEnum {E : ℕ →. RawWord ℕ} (hE : IsNatEnumerator R E) :
    IsEnumerator R (TheoremA.RelPres.twoGenEnum E) := by
  have := RecursiveIn.bind_primrec hE
    (g := fun _ z => (decodeRawWordNat z).map fun w => Encodable.encode (subst w))
    (Primrec.option_map (primrec_decodeRawWordNat.comp Primrec.snd)
      (Primrec.encode.comp (primrec_subst.comp Primrec.snd)).to₂)
  unfold IsEnumerator
  convert this using 1
  funext k
  apply Part.ext; intro x
  simp [TheoremA.RelPres.twoGenEnum, Part.mem_bind_iff, Part.mem_map_iff, eq_comm]

/-- **The exact relator set of `e₂`**: the image of `S = enumRelatorsNat E` under `thetaWord`. -/
theorem enumRelators_twoGenEnum (E : ℕ →. RawWord ℕ) :
    enumRelators (twoGenEnum E) = thetaWord '' enumRelatorsNat E := by
  ext y
  constructor
  · rintro ⟨k, w', hw', rfl⟩
    obtain ⟨w, hw, rfl⟩ := (Part.mem_map_iff _).1 hw'
    exact ⟨_, ⟨k, w, hw, rfl⟩, (eval_subst w).symm⟩
  · rintro ⟨_, ⟨k, w, hw, rfl⟩, rfl⟩
    exact ⟨k, subst w, Part.mem_map _ hw, eval_subst w⟩

end TheoremA.RelPres
