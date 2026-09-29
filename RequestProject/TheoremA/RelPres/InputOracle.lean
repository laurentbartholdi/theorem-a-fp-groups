module

public import RequestProject.TheoremA.RelPres.TwoGen

/-!
# An oracle presentation for every countable group

For an arbitrary countable group `G` (no computability, decidability or finite-generation
hypothesis) we choose, classically, a surjection `x : ℕ → G` and let
`inputHom x : FreeGroup ℕ →* G` send the `n`-th free generator to `x n`.

* `kernelOracle x` — the set of structural raw-word codes `q` whose word evaluates to `1`
  under `inputHom x` (invalid codes are excluded).  It is defined noncomputably from `G` and `x`
  and is **not** asserted to be recursive; it is only used as an oracle.
* `oracleWordEnum R` — for an arbitrary `R`: query `χ_R q`; if the answer is `1`, decode `q`
  structurally, otherwise produce no output.  `isNatEnumerator_oracleWordEnum` shows it is an
  `R`-enumerator.  It never evaluates a word in any group.
* `enumRelatorsNat_oracleWordEnum` — the relator set of `oracleWordEnum (kernelOracle x)` is
  exactly the kernel of `inputHom x`.
* `inputPresentationEquiv` — `PresentedGroup (…) ≃* G`, sending `of n` to `x n`.
* `exists_countablyPresentedIn` — every countable group is countably `R`-presented for some `R`.
* `CountablyPresentedIn.exists_injective_hom_VR` and `exists_oracle_injective_hom_VR` — the
  input group embeds in `V_R` for its chosen oracle `R`.  The oracle depends on `G`; no single
  `V_R` is claimed to contain every countable group, and no `FP₂` property is claimed.
-/

@[expose] public section

namespace TheoremA.RelPres

open RawWord

universe u

/-! ### The oracle enumerator -/

open Classical in
/-- The oracle-free post-processing step on a pair code `⟪q, b⟫`: if `b = 1`, decode `q`
structurally (and re-encode it); otherwise no output. -/
noncomputable def oracleWordStep (p : ℕ) : Option ℕ :=
  if (Nat.unpair p).2 = 1 then (decodeRawWordNat (Nat.unpair p).1).map encodeRawWordNat
  else none

theorem primrec_oracleWordStep : Primrec oracleWordStep := by
  unfold oracleWordStep
  exact Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1))
    (Primrec.option_map (primrec_decodeRawWordNat.comp (Primrec.fst.comp Primrec.unpair))
      (primrec_encodeRawWordNat.comp Primrec.snd).to₂)
    (Primrec.const none)

/-- **The oracle word enumerator.**  On input `q`, one call to `χ_R q`; on answer `1` output
the structurally decoded word (undefined if `q` is not a valid code), otherwise no output. -/
noncomputable def oracleWordEnum (R : Set ℕ) : ℕ →. RawWord ℕ := fun q =>
  (chi R q).bind fun b => if b = 1 then ((decodeRawWordNat q : Option (RawWord ℕ)) : Part _)
    else Part.none

theorem mem_oracleWordEnum {R : Set ℕ} {q : ℕ} {w : RawWord ℕ} :
    w ∈ oracleWordEnum R q ↔ q ∈ R ∧ decodeRawWordNat q = some w := by
  classical
  unfold oracleWordEnum chi
  by_cases hq : q ∈ R <;> simp [hq, Part.mem_ofOption]

/-- **`oracleWordEnum R` is an `R`-enumerator**, for every `R`. -/
theorem isNatEnumerator_oracleWordEnum (R : Set ℕ) : IsNatEnumerator R (oracleWordEnum R) := by
  have hId : RecursiveIn (oracle R) fun n => Part.some n := RecursiveIn.of_partrec Nat.Partrec.some
  have hChi : RecursiveIn (oracle R) (chi R) := RecursiveIn.oracle _ rfl
  have hP := RecursiveIn.pair hId hChi
  have hStep : RecursiveIn (oracle R) fun p => (oracleWordStep p : Part ℕ) :=
    RecursiveIn.of_partrec (Partrec.nat_iff.1 (Computable.ofOption primrec_oracleWordStep.to_comp))
  have := RecursiveIn.comp hStep hP
  unfold IsNatEnumerator
  convert this using 1
  funext q
  apply Part.ext
  intro c
  classical
  rcases hd : decodeRawWordNat q with _ | w <;> by_cases hq : q ∈ R <;>
    simp [oracleWordEnum, chi, hq, hd, oracleWordStep, Seq.seq]

/-! ### The kernel oracle of a countable group -/

variable {G : Type u} [Group G]

/-- The homomorphism `FreeGroup ℕ →* G` sending the `n`-th free generator to `x n`. -/
def inputHom (x : ℕ → G) : FreeGroup ℕ →* G := FreeGroup.lift x

@[simp] theorem inputHom_of (x : ℕ → G) (n : ℕ) : inputHom x (FreeGroup.of n) = x n :=
  FreeGroup.lift_apply_of

theorem inputHom_surjective {x : ℕ → G} (hx : Function.Surjective x) :
    Function.Surjective (inputHom x) := by
  intro g
  obtain ⟨n, rfl⟩ := hx g
  exact ⟨FreeGroup.of n, inputHom_of x n⟩

/-- **The kernel oracle** `R_x`: codes of raw words evaluating to `1` under `inputHom x`.
Defined classically; not asserted to be recursive. -/
def kernelOracle (x : ℕ → G) : Set ℕ :=
  {q | ∃ w, decodeRawWordNat q = some w ∧ inputHom x (RawWord.eval w) = 1}

/-- **Exact relator set**: the words enumerated by `oracleWordEnum (kernelOracle x)` evaluate
to exactly the kernel of `inputHom x`. -/
theorem enumRelatorsNat_oracleWordEnum (x : ℕ → G) :
    enumRelatorsNat (oracleWordEnum (kernelOracle x)) = ((inputHom x).ker : Set (FreeGroup ℕ)) := by
  ext f
  constructor
  · rintro ⟨q, w, hw, rfl⟩
    obtain ⟨⟨w', hw', h1⟩, hdec⟩ := mem_oracleWordEnum.1 hw
    rw [hdec] at hw'
    cases hw'
    exact h1
  · intro hf
    obtain ⟨w, rfl⟩ := RawWord.eval_surjective f
    refine ⟨encodeRawWordNat w, w, mem_oracleWordEnum.2 ⟨⟨w, ?_, hf⟩, ?_⟩, rfl⟩
    · exact decodeRawWordNat_encode w
    · exact decodeRawWordNat_encode w

/-- **Recovering `G`**: the presented group of the oracle enumerator is isomorphic to `G`. -/
noncomputable def inputPresentationEquiv (x : ℕ → G) (hx : Function.Surjective x) :
    PresentedGroup (enumRelatorsNat (oracleWordEnum (kernelOracle x))) ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [enumRelatorsNat_oracleWordEnum, Subgroup.normalClosure_eq_self])).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (inputHom_surjective hx))

@[simp] theorem inputPresentationEquiv_of (x : ℕ → G) (hx : Function.Surjective x) (n : ℕ) :
    inputPresentationEquiv x hx (PresentedGroup.of n) = x n := by
  change inputHom x (FreeGroup.of n) = x n
  exact inputHom_of x n

/-- The oracle presentation of `G` from a surjective sequence. -/
theorem countablyPresentedIn_kernelOracle (x : ℕ → G) (hx : Function.Surjective x) :
    CountablyPresentedIn (kernelOracle x) G :=
  ⟨oracleWordEnum (kernelOracle x), isNatEnumerator_oracleWordEnum _,
    ⟨inputPresentationEquiv x hx⟩⟩

/-- **Checkpoint I.**  Every countable group has a presentation enumerated relative to some
oracle `R ⊆ ℕ`. -/
theorem exists_countablyPresentedIn (G : Type u) [Group G] [Countable G] :
    ∃ R : Set ℕ, CountablyPresentedIn R G := by
  obtain ⟨x, hx⟩ := exists_surjective_nat G
  exact ⟨kernelOracle x, countablyPresentedIn_kernelOracle x hx⟩

/-! ### Embedding the input in `V_R` -/

/-- A countably `R`-presented group embeds in `V_R`. -/
theorem CountablyPresentedIn.exists_injective_hom_VR {R : Set ℕ} {X : Type u} [Group X]
    (h : CountablyPresentedIn R X) : ∃ f : X →* VR R, Function.Injective f := by
  obtain ⟨Y, _, -, hY, -, g, hg⟩ := h.exists_twoGen_classCR
  obtain ⟨f, hf⟩ := hY.exists_injective_hom_VR
  exact ⟨f.comp g, hf.comp hg⟩

/-- **Every countable group embeds in `V_R` for a suitable oracle `R`** (depending on the
group). -/
theorem exists_oracle_injective_hom_VR (G : Type u) [Group G] [Countable G] :
    ∃ R : Set ℕ, ∃ f : G →* VR R, Function.Injective f := by
  obtain ⟨R, hR⟩ := exists_countablyPresentedIn G
  exact ⟨R, hR.exists_injective_hom_VR⟩

end TheoremA.RelPres
