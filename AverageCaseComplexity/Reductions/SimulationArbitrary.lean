module

public import AverageCaseComplexity.Reductions.SimulationQuantitative

@[expose] public section


namespace AverageCaseComplexity

open Turing.MultiTapeTM

private theorem poly_pow {α : Type} {size f : α → ℕ} (h : PolyBounded size f) (d : ℕ) :
    PolyBounded size (fun a => f a ^ d) := by
  induction d with
  | zero => simpa using (PolyBounded.const (size := size) 1)
  | succ d ih => simpa [Nat.pow_succ] using ih.mul h

/-- An arbitrary source-dependent cost, plus polynomial local work. Both terms
are backed by the same actual tidy machine certificate. -/
def WithPolyCost {α β : Type} (f : α → β) (input : α ↪ Word) (output : β ↪ Word)
    (H : α → ℕ) : Prop :=
  ∃ P, PolyBounded (fun a => (input a).length) P ∧
    ComputableTidilyInO f input output (fun a => H a + P a) (fun a => H a + P a)

private theorem polyCost_comp {α β γ : Type} {input : α ↪ Word} {middle : β ↪ Word}
    {output : γ ↪ Word} {f : β → γ} {g : α → β} {H : β → ℕ}
    (hf : WithPolyCost f middle output H) (hg : ComputableTidilyInPolyTime g input middle) :
    WithPolyCost (f ∘ g) input output (H ∘ g) := by
  obtain ⟨P, hP, hf⟩ := hf
  obtain ⟨d, hd⟩ := polytime_inO hg
  let Q := fun a => ((input a).length + 1) ^ d + P (g a)
  have hQ : PolyBounded (fun a => (input a).length) Q :=
    (poly_pow (PolyBounded.self.add (.const 1)) d).add (hP.comp hg.polyBounded_length)
  refine ⟨Q, hQ, ?_⟩
  simpa only [Q, Function.comp_apply, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf.comp hd

namespace PolyTimeOracleScheme

/-- A single finite instruction has only additive polynomial overhead beyond
its source-dependent target cost. -/
theorem runtimeMachineStep_withPolyCost (T : PolyTimeOracleScheme)
    {answer : Word × Accuracy → Word → Answer} {H : Word × Accuracy → ℕ} {d : ℕ}
    (hanswer : ComputableTidilyInO (fun p : (Word × Accuracy) × Word => answer p.1 p.2)
      (encPair schemeInputEncoding encBits) answerEncoding
      (fun p => ((encPair schemeInputEncoding encBits p).length + 1) ^ d + H p.1)
      (fun p => ((encPair schemeInputEncoding encBits p).length + 1) ^ d + H p.1)) :
    WithPolyCost (fun p : (Word × Accuracy) × T.RuntimeConfig =>
      T.runtimeMachineStep answer p.1 p.2)
      (encPair schemeInputEncoding encFiniteConfig) (encOption encFiniteConfig) (fun p => H p.1) := by
  obtain ⟨D, hd⟩ := T.runtimeMachineStep_inO_of_handler hanswer
  let size := fun p : (Word × Accuracy) × T.RuntimeConfig =>
    (encPair schemeInputEncoding encFiniteConfig p).length
  let P := fun p : (Word × Accuracy) × T.RuntimeConfig => (size p + 1) ^ D +
    ((encPair schemeInputEncoding encBits (p.1, (p.2.channels ()).1)).length + 1) ^ d
  have hP : PolyBounded size P :=
    (poly_pow (PolyBounded.self.add (.const 1)) D).add
      (poly_pow (T.runtimeRequest_efficient.polyBounded_length.add (.const 1)) d)
  exact ⟨P, hP, by simpa only [P, size, Nat.add_assoc] using hd⟩

/-- The optional abort flag and captured source parameter add only polynomial
work; they do not raise the target cost to a power. -/
theorem runtimePairedStep_withPolyCost (T : PolyTimeOracleScheme)
    {answer : Word × Accuracy → Word → Answer} {H : Word × Accuracy → ℕ} {d : ℕ}
    (hanswer : ComputableTidilyInO (fun p : (Word × Accuracy) × Word => answer p.1 p.2)
      (encPair schemeInputEncoding encBits) answerEncoding
      (fun p => ((encPair schemeInputEncoding encBits p).length + 1) ^ d + H p.1)
      (fun p => ((encPair schemeInputEncoding encBits p).length + 1) ^ d + H p.1)) :
    WithPolyCost (fun p : (Word × Accuracy) × Option T.RuntimeConfig =>
      (p.1, T.runtimeLoopStep answer p.1 p.2))
      (encPair schemeInputEncoding (encOption encFiniteConfig))
      (encPair schemeInputEncoding (encOption encFiniteConfig)) (fun p => H p.1) := by
  let input := encPair schemeInputEncoding (encOption (encFiniteConfig : T.RuntimeConfig ↪ Word))
  have hparam : ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Option T.RuntimeConfig => p.1) input schemeInputEncoding := .fst _ _
  have hstate : ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Option T.RuntimeConfig => p.2) input (encOption encFiniteConfig) := .snd _ _
  have hget : ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Option T.RuntimeConfig =>
        p.2.getD (T.runtimeInitial ([], ⟨1, by decide⟩))) input encFiniteConfig :=
    ComputableTidilyInPolyTime.optionGetDWithInput hstate (.const _)
  have hprepare := hparam.prod hget
  obtain ⟨P, hP, hcall⟩ := polyCost_comp (T.runtimeMachineStep_withPolyCost hanswer) hprepare
  obtain ⟨dg, hg⟩ := polytime_inO (ComputableTidilyInPolyTime.optionIsSome hstate)
  have hnPoly : ComputableTidilyInPolyTime (fun _ : (Word × Accuracy) × Option T.RuntimeConfig =>
      (none : Option T.RuntimeConfig)) input (encOption encFiniteConfig) := .const none
  obtain ⟨dn, hn⟩ := polytime_inO hnPoly
  let Q := fun p : (Word × Accuracy) × Option T.RuntimeConfig =>
    ((input p).length + 1) ^ dg + P p + ((input p).length + 1) ^ dn
  have hQ : PolyBounded (fun p => (input p).length) Q :=
    ((poly_pow (PolyBounded.self.add (.const 1)) dg).add hP).add
      (poly_pow (PolyBounded.self.add (.const 1)) dn)
  have hh := (hg.ite hcall hn).mono_le
    (T' := fun p => H p.1 + Q p) (S' := fun p => H p.1 + Q p)
    (fun p => by dsimp [Q]; split_ifs <;> omega)
    (fun p => by dsimp [Q]; split_ifs <;> omega)
  have hloop : ComputableTidilyInO
      (fun p : (Word × Accuracy) × Option T.RuntimeConfig => T.runtimeLoopStep answer p.1 p.2)
      input (encOption encFiniteConfig) (fun p => H p.1 + Q p) (fun p => H p.1 + Q p) :=
    hh.of_enc_eq (fun ⟨a, state⟩ => by cases state <;> rfl)
  obtain ⟨df, hf⟩ := polytime_inO hparam
  refine ⟨fun p => ((input p).length + 1) ^ df + Q p,
    (poly_pow (PolyBounded.self.add (.const 1)) df).add hQ, ?_⟩
  apply (hf.prod hloop).mono_le
  · intro p; dsimp only; omega
  · intro p; dsimp only; omega

/-- General quantitative substitution. The target cost occurs linearly, times
a source-size polynomial, even when that target cost is nonpolynomial. -/
theorem simulate_arbitrary_inO (T : PolyTimeOracleScheme)
    {answer : Word × Accuracy → Word → Answer} {H : Word × Accuracy → ℕ} {d : ℕ}
    (hanswer : ComputableTidilyInO (fun p : (Word × Accuracy) × Word => answer p.1 p.2)
      (encPair schemeInputEncoding encBits) answerEncoding
      (fun p => ((encPair schemeInputEncoding encBits p).length + 1) ^ d + H p.1)
      (fun p => ((encPair schemeInputEncoding encBits p).length + 1) ^ d + H p.1)) :
    ∃ D, ComputableTidilyInO (T.simulate answer) schemeInputEncoding answerEncoding
      (fun a => ((schemeInputEncoding a).length + 1) ^ D * (H a + 1))
      (fun a => ((schemeInputEncoding a).length + 1) ^ D * (H a + 1)) := by
  let : Inhabited Accuracy := ⟨⟨1, by decide⟩⟩
  let stateEnc := encPair schemeInputEncoding (encOption (encFiniteConfig : T.RuntimeConfig ↪ Word))
  let step := fun p : (Word × Accuracy) × Option T.RuntimeConfig =>
    (p.1, T.runtimeLoopStep answer p.1 p.2)
  let init := fun a : Word × Accuracy => (a, some (T.runtimeInitial a))
  let N := fun a : Word × Accuracy => T.clock a.1 a.2
  let size := fun a : Word × Accuracy => (schemeInputEncoding a).length
  have hsize : ComputableTidilyInPolyTime size schemeInputEncoding encUnary := .encoding_length _
  have hclock : ComputableTidilyInPolyTime N schemeInputEncoding encUnary := by
    change ComputableTidilyInPolyTime
      (fun a : Word × Accuracy => T.coefficient * ((schemeInputEncoding a).length + 1) ^ T.degree)
      schemeInputEncoding encUnary
    fun_prop
  have hnBinary := ComputableTidilyInPolyTime.unary_to_binary.comp hclock
  have hinitCfg : ComputableTidilyInPolyTime T.runtimeInitial schemeInputEncoding encFiniteConfig :=
    ComputableTidilyInPolyTime.finiteConfig_init (Oracle := Unit) schemeInput_bits_efficient T.machine.initial
  have hiPoly : ComputableTidilyInPolyTime init schemeInputEncoding stateEnc :=
    ComputableTidilyInPolyTime.id'.prod ((ComputableTidilyInPolyTime.optionSome encFiniteConfig).comp hinitCfg)
  obtain ⟨dn, hn⟩ := polytime_inO hnBinary
  obtain ⟨di, hi⟩ := polytime_inO hiPoly
  obtain ⟨P, hP, hs⟩ := T.runtimePairedStep_withPolyCost hanswer
  have htrace : ∀ a i, step^[i] (init a) =
      (a, (T.runtimeLoopStep answer a)^[i] (some (T.runtimeInitial a))) := by
    intro a i
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
  have hinv : ∀ a i, T.runtimeSpaceInvariant a i
      ((T.runtimeLoopStep answer a)^[i] (some (T.runtimeInitial a))) := by
    intro a i
    induction i with
    | zero => intro cfg heq; cases heq; exact T.runtimeInitial_spaceBound a
    | succ i ih => simpa only [Function.iterate_succ_apply'] using
        T.runtimeLoopStep_invariant answer a i _ ih
  obtain ⟨cspace, hspace⟩ := Turing.MultiTapeTM.length_encFiniteConfig_le
    (k := T.workTapes) (State := Fin T.stateCount) (Oracle := Unit)
  let B := fun a => 2 * size a + 2 + cspace * (size a + N a + 2)
  have hB : ∀ a i, i ≤ N a → (stateEnc (step^[i] (init a))).length ≤ B a := by
    intro a i hi
    rw [htrace]
    simp only [stateEnc, length_encPair]
    cases heq : (T.runtimeLoopStep answer a)^[i] (some (T.runtimeInitial a)) with
    | none =>
      simp only [encOption_none, List.length_nil]
      dsimp [B, size]
      omega
    | some cfg =>
      have hc := hspace (size a) i 1 cfg (hinv a i cfg heq)
      have hc' := hc.trans (Nat.mul_le_mul_left cspace (by omega : size a + i + 1 + 1 ≤ size a + N a + 2))
      simp only [encOption_some, List.length_cons]
      dsimp [B, size] at *
      omega
  have hNpoly : PolyBounded size N := by simpa using hclock.polyBounded_length
  have hBpoly : PolyBounded size B :=
    (((PolyBounded.const 2).mul PolyBounded.self).add (.const 2)).add
      ((PolyBounded.const cspace).mul ((PolyBounded.self.add hNpoly).add (.const 2)))
  obtain ⟨cp, dp, hp⟩ := hP
  let PB := fun a => cp * (B a + 1) ^ dp
  have hPB : PolyBounded size PB := (PolyBounded.const cp).mul (poly_pow (hBpoly.add (.const 1)) dp)
  have hround : ∀ a i, i ≤ N a → H (step^[i] (init a)).1 + P (step^[i] (init a)) ≤ H a + PB a := by
    intro a i hi
    have hpi := (hp (step^[i] (init a))).trans
      (Nat.mul_le_mul_left cp (Nat.pow_le_pow_left (Nat.add_le_add_right (hB a i hi) 1) dp))
    rw [htrace] at hpi ⊢
    exact Nat.add_le_add_left hpi _
  have hiter := ComputableTidilyInO.iterate hn hi hs hround hround hB
  have hpostPoly : ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Option T.RuntimeConfig => T.runtimeResult p.2)
      stateEnc answerEncoding := T.runtimeResult_efficient.comp (ComputableTidilyInPolyTime.snd _ _)
  obtain ⟨dd, hpost⟩ := polytime_inO hpostPoly
  have hfinal := (hpost.comp hiter).of_enc_eq (g := T.simulate answer) (fun a => by
    change answerEncoding (T.simulate answer a) =
      answerEncoding (T.runtimeResult (step^[N a] (init a)).2)
    rw [htrace]
    exact congrArg answerEncoding (T.runtimeResult_eq_simulate answer a).symm)
  let L := fun a => (encNat (N a)).length
  let G := fun a => (size a + 1) ^ dn + (size a + 1) ^ di +
    (N a + 1) * (PB a + B a + (L a + 1) ^ 2) + PB a + B a + L a + (B a + 1) ^ dd
  have hLpoly : PolyBounded size L := hnBinary.polyBounded_length
  have hGpoly : PolyBounded size G := by
    exact ((((((poly_pow (PolyBounded.self.add (.const 1)) dn).add
      (poly_pow (PolyBounded.self.add (.const 1)) di)).add
      ((hNpoly.add (.const 1)).mul ((hPB.add hBpoly).add
        (poly_pow (hLpoly.add (.const 1)) 2)))).add hPB).add hBpoly).add hLpoly).add
      (poly_pow (hBpoly.add (.const 1)) dd)
  have htime : ∀ a : Word × Accuracy,
      (size a + 1) ^ dn + (size a + 1) ^ di +
      (N a + 1) * (H a + PB a + B a + (L a + 1) ^ 2) +
      ((stateEnc (step^[N a] (init a))).length + 1) ^ dd ≤ (N a + 1) * H a + G a := by
    intro a
    have hlast := Nat.pow_le_pow_left (Nat.add_le_add_right (hB a (N a) le_rfl) 1) dd
    show (size a + 1) ^ dn + (size a + 1) ^ di +
      (N a + 1) * (H a + PB a + B a + (L a + 1) ^ 2) +
      ((stateEnc (step^[N a] (init a))).length + 1) ^ dd ≤ (N a + 1) * H a + G a
    dsimp [G]
    simp only [Nat.mul_add]
    omega
  have hspaceBound : ∀ a : Word × Accuracy,
      (size a + 1) ^ dn + (size a + 1) ^ di + (H a + PB a) + B a + L a +
      ((stateEnc (step^[N a] (init a))).length + 1) ^ dd ≤ (N a + 1) * H a + G a := by
    intro a
    have hlast := Nat.pow_le_pow_left (Nat.add_le_add_right (hB a (N a) le_rfl) 1) dd
    have hH : H a ≤ (N a + 1) * H a := Nat.le_mul_of_pos_left _ (by omega)
    show (size a + 1) ^ dn + (size a + 1) ^ di + (H a + PB a) + B a + L a +
      ((stateEnc (step^[N a] (init a))).length + 1) ^ dd ≤ (N a + 1) * H a + G a
    dsimp [G]
    omega
  have hbounded := hfinal.mono_le htime hspaceBound
  obtain ⟨cn, en, hnp⟩ := hNpoly.add (.const 1)
  obtain ⟨cg, eg, hgp⟩ := hGpoly
  let D := max en eg
  have hb : ∀ a, (N a + 1) * H a + G a ≤
      (cn + cg + 1) * ((size a + 1) ^ D * (H a + 1) + 1) := by
    intro a
    have hn' := (hnp a).trans (Nat.mul_le_mul_left cn
      (Nat.pow_le_pow_right (by omega : 0 < size a + 1) (le_max_left en eg)))
    have hg' := (hgp a).trans (Nat.mul_le_mul_left cg
      (Nat.pow_le_pow_right (by omega : 0 < size a + 1) (le_max_right en eg)))
    calc
      _ ≤ (cn * (size a + 1) ^ D) * H a + cg * (size a + 1) ^ D :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hn') hg'
      _ ≤ (cn + cg) * ((size a + 1) ^ D * (H a + 1)) := by
        nlinarith [Nat.zero_le (cg * (size a + 1) ^ D * H a), Nat.zero_le (cn * (size a + 1) ^ D)]
      _ ≤ _ := Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
  exact ⟨D, hbounded.mono (cn + cg + 1) hb hb⟩

end PolyTimeOracleScheme
end AverageCaseComplexity
