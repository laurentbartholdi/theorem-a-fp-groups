module

public import RequestProject.TheoremA.RelPres.Bridge
public import RequestProject.TheoremA.RelPres.Universal

/-!
# The family of all finite-alphabet `R`-presentations

* `candEnum R n c` — the candidate enumerator `e_(n,c)(k) = U R c k >>= decode >>= down_n`
  (decoding/restriction failures are undefined values); `isEnumerator_candEnum`.
* `W R n c k` — the natural-alphabet version; `recursiveIn_W` (jointly in `n, c, k`, input
  `⟪⟪n, c⟫, k⟫`) and `W_eq : W R n c k = up_n <$> candEnum R n c k`.
* coverage: `exists_candEnum_eq : IsEnumerator R e → ∃ c, candEnum R n c = e`.
* `famRels R n c = enumRelators (candEnum R n c)`, `famGroup R n c = PresentedGroup (famRels R n c)`;
  `classCR_famGroup` and `ClassCR.exists_famGroup_equiv`.
-/

@[expose] public section

namespace TheoremA.RelPres

open RawWord

variable {R : Set ℕ} {O : Set (ℕ →. ℕ)}

/-- Postcomposition of a relatively recursive function with a primitive recursive partial step
that may also look at the input. -/
theorem RecursiveIn.bind_primrec {f : ℕ →. ℕ} (hf : RecursiveIn O f) {g : ℕ → ℕ → Option ℕ}
    (hg : Primrec₂ g) : RecursiveIn O fun p => (f p).bind fun z => (g p z : Part ℕ) := by
  have hP := RecursiveIn.pair (RecursiveIn.of_primrec (O := O) Primrec.id) hf
  have hg' : Nat.Partrec fun q => (g (Nat.unpair q).1 (Nat.unpair q).2 : Part ℕ) := by
    apply Partrec.nat_iff.1
    exact Computable.ofOption (hg.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)).to_comp
  have := RecursiveIn.comp (RecursiveIn.of_partrec hg') hP
  convert this using 1
  funext p
  apply Part.ext; intro x
  simp [Seq.seq]

/-- `k ↦ U R c k` for a fixed program `c`. -/
theorem recursiveIn_U_fixed (c : ℕ) : RecursiveIn (oracle R) fun k => U R c k := by
  have := RecursiveIn.comp_primrec (recursiveIn_U (R := R))
    (Primrec₂.natPair.comp (Primrec.const c) Primrec.id)
  simpa using this

/-! ### The candidate enumerators -/

/-- **The candidate enumerator** `e_(n,c)(k) = do z ← U R c k; w ← decode z; down_n w`. -/
noncomputable def candEnum (R : Set ℕ) (n c : ℕ) : ℕ →. RawWord (Fin n) := fun k =>
  (U R c k).bind fun z => (((decodeRawWordNat z).bind (down n) : Option _) : Part _)

/-- **Every candidate is an `R`-enumerator.** -/
theorem isEnumerator_candEnum (n c : ℕ) : IsEnumerator R (candEnum R n c) := by
  have := RecursiveIn.bind_primrec (recursiveIn_U_fixed (R := R) c)
    (g := fun _ z => finCodeOfNatCode n z) ((primrec_finCodeOfNatCode n).comp Primrec.snd).to₂
  unfold IsEnumerator
  convert this using 1
  funext k
  apply Part.ext; intro x
  simp only [candEnum, finCodeOfNatCode, Part.mem_bind_iff, Part.mem_map_iff, Part.mem_ofOption,
    Option.mem_def]
  constructor
  · rintro ⟨v, ⟨a, ha, hv⟩, rfl⟩
    exact ⟨a, ha, by rw [hv]; rfl⟩
  · rintro ⟨a, ha, h⟩
    rw [Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    exact ⟨v, ⟨a, ha, hv⟩, rfl⟩

/-- **The natural-alphabet version** `W R n c k`: bounded outputs are kept as natural words. -/
noncomputable def W (R : Set ℕ) (n c k : ℕ) : Part (RawWord ℕ) :=
  (U R c k).bind fun z => (restrictCode n z : Part _)

/-- `W` on the single input `p = ⟪⟪n, c⟫, k⟫`. -/
noncomputable def Wfun (R : Set ℕ) (p : ℕ) : Part (RawWord ℕ) :=
  W R (Nat.unpair (Nat.unpair p).1).1 (Nat.unpair (Nat.unpair p).1).2 (Nat.unpair p).2

@[simp] theorem Wfun_pair (n c k : ℕ) : Wfun R (Nat.pair (Nat.pair n c) k) = W R n c k := by
  simp [Wfun]

/-- **Uniform recursiveness of `W`**, jointly in `n`, `c` and `k`. -/
theorem recursiveIn_W : RecursiveIn (oracle R) fun p => (Wfun R p).map encodeRawWordNat := by
  have hU : RecursiveIn (oracle R) fun p =>
      U R (Nat.unpair (Nat.unpair p).1).2 (Nat.unpair p).2 := by
    have := RecursiveIn.comp_primrec (recursiveIn_U (R := R))
      (Primrec₂.natPair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.snd.comp Primrec.unpair))
    simpa using this
  have hg : Primrec₂ fun p z : ℕ =>
      (restrictCode (Nat.unpair (Nat.unpair p).1).1 z).map encodeRawWordNat :=
    Primrec.option_map
      (primrec_restrictCode.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp
          (Primrec.unpair.comp Primrec.fst))))
        Primrec.snd)
      (primrec_encodeRawWordNat.comp Primrec.snd).to₂
  have := RecursiveIn.bind_primrec hU hg
  convert this using 1
  funext p
  apply Part.ext; intro x
  simp [Wfun, W, Part.mem_bind_iff, Part.mem_map_iff]

theorem W_eq (R : Set ℕ) (n c k : ℕ) : W R n c k = (candEnum R n c k).map (up n) := by
  apply Part.ext; intro w
  simp only [W, candEnum, restrictCode_eq, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨z, hz, hw⟩
    rw [Part.mem_ofOption, Option.mem_def, Option.map_eq_some_iff] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨v, ⟨z, hz, by simpa using hv⟩, rfl⟩
  · rintro ⟨v, ⟨z, hz, hv⟩, rfl⟩
    refine ⟨z, hz, ?_⟩
    rw [Part.mem_ofOption, Option.mem_def] at hv ⊢
    rw [hv]; rfl

/-! ### Coverage of the existing class -/

/-- The numeric function `f(k) = encode (up_n w)` when `e k` returns `w`. -/
theorem recursiveIn_natCodes {n : ℕ} {e : ℕ →. RawWord (Fin n)} (he : IsEnumerator R e) :
    RecursiveIn (oracle R) fun k => (e k).map fun w => encodeRawWordNat (up n w) := by
  have := RecursiveIn.bind_primrec he (g := fun _ z => natCodeOfFinCode n z)
    ((primrec_natCodeOfFinCode n).comp Primrec.snd).to₂
  convert this using 1
  funext k
  apply Part.ext; intro x
  simp [Part.mem_bind_iff, Part.mem_map_iff, eq_comm]

/-- If `U R c` computes the natural codes of `e`, then `e_(n,c) = e` (as partial functions). -/
theorem candEnum_eq_of_index {n c : ℕ} {e : ℕ →. RawWord (Fin n)}
    (hc : ∀ k, U R c k = (e k).map fun w => encodeRawWordNat (up n w)) :
    candEnum R n c = e := by
  funext k
  apply Part.ext; intro w
  simp only [candEnum, hc, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, hw⟩
    simp only [decodeRawWordNat_encode, Option.bind_some, down_up, Part.mem_ofOption,
      Option.mem_def, Option.some.injEq] at hw
    exact hw ▸ hv
  · intro hw
    exact ⟨_, ⟨w, hw, rfl⟩, by simp⟩

/-- **Coverage**: every `R`-enumerator on `Fin n` is one of the candidates `e_(n,c)`. -/
theorem exists_candEnum_eq {n : ℕ} {e : ℕ →. RawWord (Fin n)} (he : IsEnumerator R e) :
    ∃ c, candEnum R n c = e := by
  obtain ⟨c, hc⟩ := exists_index (recursiveIn_natCodes he)
  exact ⟨c, candEnum_eq_of_index hc⟩

/-! ### The groups `G_(n,c)` -/

/-- The relator set `S_(n,c) = enumRelators e_(n,c)`. -/
def famRels (R : Set ℕ) (n c : ℕ) : Set (FreeGroup (Fin n)) := enumRelators (candEnum R n c)

/-- The group `G_(n,c) = PresentedGroup S_(n,c)`. -/
abbrev famGroup (R : Set ℕ) (n c : ℕ) : Type := PresentedGroup (famRels R n c)

/-- Every `G_(n,c)` belongs to `C_R`. -/
theorem classCR_famGroup (n c : ℕ) : ClassCR R (famGroup R n c) :=
  ⟨n, candEnum R n c, isEnumerator_candEnum n c, ⟨MulEquiv.refl _⟩⟩

universe u

/-- **Every member of `C_R` is some `G_(n,c)`.** -/
theorem ClassCR.exists_famGroup_equiv {X : Type u} [Group X] (h : ClassCR R X) :
    ∃ n c, Nonempty (famGroup R n c ≃* X) := by
  obtain ⟨n, e, he, ⟨ψ⟩⟩ := h
  obtain ⟨c, hc⟩ := exists_candEnum_eq he
  refine ⟨n, c, ⟨?_⟩⟩
  unfold famGroup famRels
  rw [hc]
  exact ψ

/-- A zero-generator factor is trivial. -/
instance (n c : ℕ) [h : Fact (n = 0)] : Subsingleton (famGroup R n c) := by
  obtain rfl := h.out
  have htop := PresentedGroup.closure_range_of (famRels R 0 c)
  rw [Set.range_eq_empty, Subgroup.closure_empty] at htop
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ (⊥ : Subgroup _) := htop ▸ Subgroup.mem_top x
  have hy : y ∈ (⊥ : Subgroup _) := htop ▸ Subgroup.mem_top y
  rw [Subgroup.mem_bot] at hx hy
  rw [hx, hy]

end TheoremA.RelPres
