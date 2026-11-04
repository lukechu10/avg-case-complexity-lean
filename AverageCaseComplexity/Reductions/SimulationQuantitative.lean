module

public import AverageCaseComplexity.Reductions.SimulationRuntime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary

@[expose] public section

namespace AverageCaseComplexity

namespace PolyTimeOracleScheme

open Turing.MultiTapeTM

/-- Whether the unchanged finite transition table requests an oracle answer at this
configuration. The default input supplied to `runtimeMachineStep` is immaterial: this handler
always aborts, so precisely a live query instruction yields `none`. -/
def runtimeQueryFlag (T : PolyTimeOracleScheme) (cfg : T.RuntimeConfig) : Bool :=
  (T.runtimeMachineStep (fun _ _ => none) ([], ⟨1, by decide⟩) cfg).isNone

/-- One of the two native (answer-independent) next-configuration routines. -/
def runtimeNativeStep (T : PolyTimeOracleScheme) (bit : Bool)
    (a : Word × Accuracy) (cfg : T.RuntimeConfig) : Option T.RuntimeConfig :=
  T.runtimeMachineStep (fun _ _ => some bit) a cfg

/-- Dispatch an instruction after separating the finite query flag from the potentially
expensive answer computation. -/
def runtimeFactoredStep (T : PolyTimeOracleScheme)
    (answer : Word × Accuracy → Word → Answer) (a : Word × Accuracy)
    (cfg : T.RuntimeConfig) : Option T.RuntimeConfig :=
  if T.runtimeQueryFlag cfg then
    match answer a (cfg.channels ()).1 with
    | none => none
    | some bit => T.runtimeNativeStep bit a cfg
  else
    T.runtimeNativeStep false a cfg

/-- The factorization changes no transition semantics: the answer routine is evaluated only
at a query instruction, and its cost can therefore be separated from native finite control. -/
theorem runtimeMachineStep_eq_factoredStep (T : PolyTimeOracleScheme)
    (answer : Word × Accuracy → Word → Answer) (a : Word × Accuracy)
    (cfg : T.RuntimeConfig) :
    T.runtimeMachineStep answer a cfg = T.runtimeFactoredStep answer a cfg := by
  cases hs : cfg.tapes.state with
  | none => simp [runtimeFactoredStep, runtimeQueryFlag, runtimeNativeStep,
      runtimeMachineStep, hs]
  | some state =>
    cases ht : T.machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols
        cfg.answerSymbols with
    | step action querySymbol answerMove =>
      simp [runtimeFactoredStep, runtimeQueryFlag, runtimeNativeStep,
        runtimeMachineStep, runtimeActionStep, hs, ht]
    | query oracle next =>
      cases oracle
      simp [runtimeFactoredStep, runtimeQueryFlag, runtimeNativeStep,
        runtimeMachineStep, runtimeActionStep, hs, ht]
      rfl

/-- Native finite-control transitions, with a fixed reply convention, are polynomial time on
an input paired with their source parameter. This certificate contains no answer-handler cost. -/
theorem runtimeNativeStep_efficient (T : PolyTimeOracleScheme) (bit : Bool) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × T.RuntimeConfig =>
        T.runtimeNativeStep bit p.1 p.2)
      (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encFiniteConfig)
      (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig) := by
  have hcfg : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × T.RuntimeConfig => p.2)
      (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encFiniteConfig)
      Turing.MultiTapeTM.encFiniteConfig := by
    fun_prop
  have hstep := T.runtimeMachineStep_efficient
    (answer := fun _ _ => some bit) (param := fun p => p.1) hcfg (.const (some bit))
  exact hstep.of_enc_eq fun p => by simp [runtimeNativeStep]

/-- Query-flag dispatch is polynomial time independently of the answer routine. -/
theorem runtimeQueryFlag_efficient (T : PolyTimeOracleScheme) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime T.runtimeQueryFlag
      Turing.MultiTapeTM.encFiniteConfig Turing.MultiTapeTM.encBool := by
  have hcfg : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun cfg : T.RuntimeConfig => cfg) Turing.MultiTapeTM.encFiniteConfig
      Turing.MultiTapeTM.encFiniteConfig := .of_eq fun _ => rfl
  have hstep := T.runtimeMachineStep_efficient
    (answer := fun _ _ => (none : Answer))
    (param := fun _ : T.RuntimeConfig => ([], ⟨1, by decide⟩)) hcfg (.const none)
  have hsome := Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionIsSome hstep
  have hnot := Turing.MultiTapeTM.ComputableTidilyInPolyTime.bool_not.comp hsome
  exact hnot.of_enc_eq fun cfg => by
    cases h : T.runtimeMachineStep (fun _ _ => none) ([], ⟨1, by decide⟩) cfg <;>
      simp [runtimeQueryFlag]

/-- A tidy polynomial-time certificate is a quantitative `O` certificate in the length
of its own encoded input. This conversion keeps the actual time-and-space witness. -/
theorem ComputableTidilyInPolyTime.inO_encodingLength
    {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} (h : ComputableTidilyInPolyTime f encIn encOut) :
    ∃ d, ComputableTidilyInO f encIn encOut
      (fun a => ((encIn a).length + 1) ^ d)
      (fun a => ((encIn a).length + 1) ^ d) := by
  obtain ⟨t, s, ht, hs, hrun⟩ := h
  obtain ⟨ct, dt, htb⟩ := ht
  obtain ⟨cs, ds, hsb⟩ := hs
  refine ⟨max dt ds, ?_⟩
  apply ComputableTidilyInO.of_bounds hrun (ct + cs + 1)
  · intro a
    have hpow : ((encIn a).length + 1) ^ dt ≤
        ((encIn a).length + 1) ^ max dt ds :=
      Nat.pow_le_pow_right (by omega) (le_max_left dt ds)
    have hbase := htb a
    have hplus : t a ≤ ct * ((encIn a).length + 1) ^ max dt ds := by
      exact hbase.trans (Nat.mul_le_mul_left ct hpow)
    nlinarith [Nat.zero_le (((encIn a).length + 1) ^ max dt ds)]
  · intro a
    have hpow : ((encIn a).length + 1) ^ ds ≤
        ((encIn a).length + 1) ^ max dt ds :=
      Nat.pow_le_pow_right (by omega) (le_max_right dt ds)
    have hbase := hsb a
    have hplus : s a ≤ cs * ((encIn a).length + 1) ^ max dt ds := by
      exact hbase.trans (Nat.mul_le_mul_left cs hpow)
    nlinarith [Nat.zero_le (((encIn a).length + 1) ^ max dt ds)]
  · intro a
    have hpow : ((encIn a).length + 1) ^ dt ≤
        ((encIn a).length + 1) ^ max dt ds :=
      Nat.pow_le_pow_right (by omega) (le_max_left dt ds)
    have hbase := htb a
    have hlen := hrun.length_le a
    have hplus : t a ≤ ct * ((encIn a).length + 1) ^ max dt ds := by
      exact hbase.trans (Nat.mul_le_mul_left ct hpow)
    have hout : (encOut (f a)).length ≤ ct * ((encIn a).length + 1) ^ max dt ds :=
      hlen.trans hplus
    nlinarith [Nat.zero_le (((encIn a).length + 1) ^ max dt ds)]

/-- The native step certificate, converted to a bound polynomial in the joint input encoding. -/
theorem runtimeNativeStep_inO (T : PolyTimeOracleScheme) (bit : Bool) :
    ∃ d, ComputableTidilyInO
      (fun p : (Word × Accuracy) × T.RuntimeConfig => T.runtimeNativeStep bit p.1 p.2)
      (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encFiniteConfig)
      (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig)
      (fun p => ((Turing.MultiTapeTM.encPair schemeInputEncoding
        Turing.MultiTapeTM.encFiniteConfig p).length + 1) ^ d)
      (fun p => ((Turing.MultiTapeTM.encPair schemeInputEncoding
        Turing.MultiTapeTM.encFiniteConfig p).length + 1) ^ d) := by
  obtain ⟨d, hd⟩ :=
    ComputableTidilyInPolyTime.inO_encodingLength (T.runtimeNativeStep_efficient bit)
  exact ⟨d, hd⟩

/-- Extract the current oracle request from a finite configuration in polynomial time. -/
theorem runtimeRequest_efficient (T : PolyTimeOracleScheme) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × T.RuntimeConfig => (p.1, (p.2.channels ()).1))
      (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encFiniteConfig)
      (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits) := by
  fun_prop

/-- Query-flag dispatch has a polynomial cost in the finite configuration encoding. -/
theorem runtimeQueryFlag_inO (T : PolyTimeOracleScheme) :
    ∃ d, ComputableTidilyInO T.runtimeQueryFlag Turing.MultiTapeTM.encFiniteConfig
      Turing.MultiTapeTM.encBool
      (fun cfg => ((Turing.MultiTapeTM.encFiniteConfig cfg).length + 1) ^ d)
      (fun cfg => ((Turing.MultiTapeTM.encFiniteConfig cfg).length + 1) ^ d) := by
  obtain ⟨d, hd⟩ :=
    ComputableTidilyInPolyTime.inO_encodingLength T.runtimeQueryFlag_efficient
  exact ⟨d, hd⟩

/-- A handler's source-only envelope survives projection of the current request out of the
finite interpreter configuration. The request-projection overhead is polynomial in the joint
encoded input, while the handler envelope remains exactly `H p.1`. -/
theorem runtimeQueryAnswer_inO (T : PolyTimeOracleScheme)
    {answer : Word × Accuracy → Word → Answer} {H : Word × Accuracy → ℕ} {d : ℕ}
    (hanswer : ComputableTidilyInO
      (fun p : (Word × Accuracy) × Word => answer p.1 p.2)
      (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits)
      answerEncoding
      (fun p => ((Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits p).length + 1) ^ d + H p.1)
      (fun p => ((Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits p).length + 1) ^ d + H p.1)) :
    ∃ e, ComputableTidilyInO
      (fun p : (Word × Accuracy) × T.RuntimeConfig => answer p.1 (p.2.channels ()).1)
      (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encFiniteConfig)
      answerEncoding
      (fun p => ((Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encFiniteConfig p).length + 1) ^ e +
        ((Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits
          (p.1, (p.2.channels ()).1)).length + 1) ^ d + H p.1)
      (fun p => ((Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encFiniteConfig p).length + 1) ^ e +
        ((Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits
          (p.1, (p.2.channels ()).1)).length + 1) ^ d + H p.1) := by
  obtain ⟨e, hrequest⟩ :=
    ComputableTidilyInPolyTime.inO_encodingLength T.runtimeRequest_efficient
  refine ⟨e, ?_⟩
  have hcomp := hanswer.comp hrequest
  simpa [Function.comp_def, Nat.add_assoc] using hcomp

/-- One actual finite-machine instruction has cost equal to the handler envelope plus a
polynomial of the original input and current query/configuration lengths. The finite query flag
is dispatched before the handler, and both answer branches use native constant-reply transitions. -/
theorem runtimeMachineStep_inO_of_handler (T : PolyTimeOracleScheme)
    {answer : Word × Accuracy → Word → Answer} {H : Word × Accuracy → ℕ} {d : ℕ}
    (hanswer : ComputableTidilyInO
      (fun p : (Word × Accuracy) × Word => answer p.1 p.2)
      (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits)
      answerEncoding
      (fun p => ((Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits p).length + 1) ^ d + H p.1)
      (fun p => ((Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits p).length + 1) ^ d + H p.1)) :
    ∃ D, ComputableTidilyInO
      (fun p : (Word × Accuracy) × T.RuntimeConfig => T.runtimeMachineStep answer p.1 p.2)
      (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encFiniteConfig)
      (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig)
      (fun p => H p.1 + ((Turing.MultiTapeTM.encPair schemeInputEncoding
          Turing.MultiTapeTM.encFiniteConfig p).length + 1) ^ D +
        ((Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits
          (p.1, (p.2.channels ()).1)).length + 1) ^ d)
      (fun p => H p.1 + ((Turing.MultiTapeTM.encPair schemeInputEncoding
          Turing.MultiTapeTM.encFiniteConfig p).length + 1) ^ D +
        ((Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits
          (p.1, (p.2.channels ()).1)).length + 1) ^ d) := by
  have hcfg : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × T.RuntimeConfig => p.2)
      (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encFiniteConfig)
      Turing.MultiTapeTM.encFiniteConfig := by
    fun_prop
  have hflagPoly := T.runtimeQueryFlag_efficient.comp hcfg
  obtain ⟨eflag, hflag⟩ :=
    ComputableTidilyInPolyTime.inO_encodingLength hflagPoly
  obtain ⟨eanswer, hanswerQ⟩ := T.runtimeQueryAnswer_inO hanswer
  obtain ⟨efalse, hfalse⟩ := T.runtimeNativeStep_inO false
  obtain ⟨etrue, htrue⟩ := T.runtimeNativeStep_inO true
  have hsomeBase : ComputableTidilyInO (fun a : Answer => a.isSome)
      answerEncoding Turing.MultiTapeTM.encBool
      (fun a => (answerEncoding a).length) (fun a => (answerEncoding a).length) :=
    (Turing.MultiTapeTM.ComputableTidilyInDegree.of_finite
      (encIn := answerEncoding) (encMid := Turing.MultiTapeTM.encBool)
      (fun a : Answer => a.isSome)).inO_one
  have hgetBase : ComputableTidilyInO (fun a : Answer => a.getD false)
      answerEncoding Turing.MultiTapeTM.encBool
      (fun a => (answerEncoding a).length) (fun a => (answerEncoding a).length) :=
    (Turing.MultiTapeTM.ComputableTidilyInDegree.of_finite
      (encIn := answerEncoding) (encMid := Turing.MultiTapeTM.encBool)
      (fun a : Answer => a.getD false)).inO_one
  have hsome := hsomeBase.comp_linear hanswerQ
  have hget := hgetBase.comp_linear hanswerQ
  let jointLen : ((Word × Accuracy) × T.RuntimeConfig) → ℕ := fun p =>
    (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encFiniteConfig p).length + 1
  let queryLen : ((Word × Accuracy) × T.RuntimeConfig) → ℕ := fun p =>
    (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits
      (p.1, (p.2.channels ()).1)).length + 1
  let D := max 1 (max eflag (max eanswer (max efalse etrue)))
  let target : ((Word × Accuracy) × T.RuntimeConfig) → ℕ := fun p =>
    H p.1 + jointLen p ^ D + queryLen p ^ d
  have hraw := hflag.ite
    (hsome.ite (hget.ite htrue hfalse)
      (Turing.MultiTapeTM.ComputableTidilyInO.const none)) hfalse
  refine ⟨D, ?_⟩
  have hbounded := hraw.mono (T' := target) (S' := target) 32
    (fun p => ?_) (fun p => ?_)
  have hfactored := hbounded.of_enc_eq
    (encOut := Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig)
    (g := fun p => T.runtimeMachineStep answer p.1 p.2)
    (fun p => by
      apply congrArg (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig)
      rw [T.runtimeMachineStep_eq_factoredStep answer p.1 p.2]
      by_cases hq : T.runtimeQueryFlag p.2
      · cases ha : answer p.1 (p.2.channels ()).1 with
        | none => simp [runtimeFactoredStep, hq, ha]
        | some bit => cases bit <;> simp [runtimeFactoredStep, hq, ha]
      · simp [runtimeFactoredStep, hq])
  simpa [target, jointLen, queryLen, Function.comp_def, Nat.add_assoc] using hfactored
  · have hflagPow : jointLen p ^ eflag ≤ jointLen p ^ D :=
      Nat.pow_le_pow_right (by dsimp [jointLen]; omega) (by dsimp [D]; omega)
    have hanswerPow : jointLen p ^ eanswer ≤ jointLen p ^ D :=
      Nat.pow_le_pow_right (by dsimp [jointLen]; omega) (by dsimp [D]; omega)
    have hfalsePow : jointLen p ^ efalse ≤ jointLen p ^ D :=
      Nat.pow_le_pow_right (by dsimp [jointLen]; omega) (by dsimp [D]; omega)
    have htruePow : jointLen p ^ etrue ≤ jointLen p ^ D :=
      Nat.pow_le_pow_right (by dsimp [jointLen]; omega) (by dsimp [D]; omega)
    have hL : jointLen p ≤ jointLen p ^ D := by
      calc
        jointLen p = jointLen p ^ 1 := by simp
        _ ≤ jointLen p ^ D := Nat.pow_le_pow_right (by dsimp [jointLen]; omega)
          (by dsimp [D]; omega)
    have htarget : jointLen p ^ D + queryLen p ^ d + H p.1 ≤ target p := by
      dsimp [target]; omega
    have hflagBound : jointLen p ^ eflag ≤ target p := by omega
    have hanswerBound : jointLen p ^ eanswer + queryLen p ^ d + H p.1 ≤
        3 * target p := by nlinarith
    have hfalseBound : jointLen p ^ efalse ≤ target p := by omega
    have htrueBound : jointLen p ^ etrue ≤ target p := by omega
    have hnoneBound : (Turing.MultiTapeTM.encPair schemeInputEncoding
        Turing.MultiTapeTM.encFiniteConfig p).length ≤ target p := by
      dsimp [jointLen] at hL
      dsimp [target, jointLen]
      omega
    have hflagBound' : jointLen p ^ eflag ≤ target p := hflagBound
    have hanswerBound' : jointLen p ^ eanswer + queryLen p ^ d + H p.1 ≤
        3 * target p := hanswerBound
    have hfalseBound' : jointLen p ^ efalse ≤ target p := hfalseBound
    have htrueBound' : jointLen p ^ etrue ≤ target p := htrueBound
    have hnoneBound' : (Turing.MultiTapeTM.encPair schemeInputEncoding
        Turing.MultiTapeTM.encFiniteConfig p).length ≤ target p := hnoneBound
    change (((Turing.MultiTapeTM.encPair schemeInputEncoding
      Turing.MultiTapeTM.encFiniteConfig p).length + 1) ^ eflag) ≤ target p at hflagBound'
    change (((Turing.MultiTapeTM.encPair schemeInputEncoding
      Turing.MultiTapeTM.encFiniteConfig p).length + 1) ^ eanswer +
      ((Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits
        (p.1, (p.2.channels ()).1)).length + 1) ^ d + H p.1) ≤ 3 * target p at hanswerBound'
    change (((Turing.MultiTapeTM.encPair schemeInputEncoding
      Turing.MultiTapeTM.encFiniteConfig p).length + 1) ^ efalse) ≤ target p at hfalseBound'
    change (((Turing.MultiTapeTM.encPair schemeInputEncoding
      Turing.MultiTapeTM.encFiniteConfig p).length + 1) ^ etrue) ≤ target p at htrueBound'
    split_ifs <;> omega
  · have hflagPow : jointLen p ^ eflag ≤ jointLen p ^ D :=
      Nat.pow_le_pow_right (by dsimp [jointLen]; omega) (by dsimp [D]; omega)
    have hanswerPow : jointLen p ^ eanswer ≤ jointLen p ^ D :=
      Nat.pow_le_pow_right (by dsimp [jointLen]; omega) (by dsimp [D]; omega)
    have hfalsePow : jointLen p ^ efalse ≤ jointLen p ^ D :=
      Nat.pow_le_pow_right (by dsimp [jointLen]; omega) (by dsimp [D]; omega)
    have htruePow : jointLen p ^ etrue ≤ jointLen p ^ D :=
      Nat.pow_le_pow_right (by dsimp [jointLen]; omega) (by dsimp [D]; omega)
    have hL : jointLen p ≤ jointLen p ^ D := by
      calc
        jointLen p = jointLen p ^ 1 := by simp
        _ ≤ jointLen p ^ D := Nat.pow_le_pow_right (by dsimp [jointLen]; omega)
          (by dsimp [D]; omega)
    have htarget : jointLen p ^ D + queryLen p ^ d + H p.1 ≤ target p := by
      dsimp [target]; omega
    have hflagBound : jointLen p ^ eflag ≤ target p := by omega
    have hanswerBound : jointLen p ^ eanswer + queryLen p ^ d + H p.1 ≤
        3 * target p := by nlinarith
    have hfalseBound : jointLen p ^ efalse ≤ target p := by omega
    have htrueBound : jointLen p ^ etrue ≤ target p := by omega
    have hnoneBound : (Turing.MultiTapeTM.encPair schemeInputEncoding
        Turing.MultiTapeTM.encFiniteConfig p).length ≤ target p := by
      dsimp [jointLen] at hL
      dsimp [target, jointLen]
      omega
    have hflagBound' : jointLen p ^ eflag ≤ target p := hflagBound
    have hanswerBound' : jointLen p ^ eanswer + queryLen p ^ d + H p.1 ≤
        3 * target p := hanswerBound
    have hfalseBound' : jointLen p ^ efalse ≤ target p := hfalseBound
    have htrueBound' : jointLen p ^ etrue ≤ target p := htrueBound
    have hnoneBound' : (Turing.MultiTapeTM.encPair schemeInputEncoding
        Turing.MultiTapeTM.encFiniteConfig p).length ≤ target p := hnoneBound
    change (((Turing.MultiTapeTM.encPair schemeInputEncoding
      Turing.MultiTapeTM.encFiniteConfig p).length + 1) ^ eflag) ≤ target p at hflagBound'
    change (((Turing.MultiTapeTM.encPair schemeInputEncoding
      Turing.MultiTapeTM.encFiniteConfig p).length + 1) ^ eanswer +
      ((Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits
        (p.1, (p.2.channels ()).1)).length + 1) ^ d + H p.1) ≤ 3 * target p at hanswerBound'
    change (((Turing.MultiTapeTM.encPair schemeInputEncoding
      Turing.MultiTapeTM.encFiniteConfig p).length + 1) ^ efalse) ≤ target p at hfalseBound'
    change (((Turing.MultiTapeTM.encPair schemeInputEncoding
      Turing.MultiTapeTM.encFiniteConfig p).length + 1) ^ etrue) ≤ target p at htrueBound'
    split_ifs <;> omega

/-- Quantitative post-processing bridge for the actual finite interpreter. If its completed
finite loop has an `O` certificate, decoding that real machine state yields an `O` certificate
for semantic oracle substitution. The decoding overhead is polynomial in the encoded final
configuration; it is not charged as an arbitrary polynomial in the source answer bound. -/
theorem simulate_of_runtimeLoop_inO (T : PolyTimeOracleScheme)
    {answer : Word × Accuracy → Word → Answer}
    {time space : Word × Accuracy → ℕ}
    (hrun : ComputableTidilyInO
      (fun a : Word × Accuracy =>
        (T.runtimeLoopStep answer a)^[T.clock a.1 a.2] (some (T.runtimeInitial a)))
      schemeInputEncoding (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig)
      time space) :
    ∃ d, ComputableTidilyInO (T.simulate answer) schemeInputEncoding answerEncoding
      (fun a => time a +
        ((Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig
          ((T.runtimeLoopStep answer a)^[T.clock a.1 a.2]
            (some (T.runtimeInitial a)))).length + 1) ^ d)
      (fun a => space a +
        ((Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig
          ((T.runtimeLoopStep answer a)^[T.clock a.1 a.2]
            (some (T.runtimeInitial a)))).length + 1) ^ d) := by
  let finalState : Word × Accuracy → Option T.RuntimeConfig := fun a =>
    (T.runtimeLoopStep answer a)^[T.clock a.1 a.2] (some (T.runtimeInitial a))
  have hdecodePoly := T.runtimeResult_efficient
  obtain ⟨d, hdecode⟩ :=
    ComputableTidilyInPolyTime.inO_encodingLength hdecodePoly
  have hcomp := hdecode.comp hrun
  refine ⟨d, ?_⟩
  have hfinal := hcomp.of_enc_eq (fun a => by
    change answerEncoding (T.simulate answer a) =
      answerEncoding (T.runtimeResult (finalState a))
    exact congrArg answerEncoding (T.runtimeResult_eq_simulate answer a).symm)
  simpa only [finalState, Function.comp_apply] using hfinal

/-- The actual bounded interpreter loop preserves the finite configuration space invariant,
independently of any efficiency assumption on its answer routine. -/
theorem runtimeLoop_final_spaceInvariant (T : PolyTimeOracleScheme)
    (answer : Word × Accuracy → Word → Answer) (a : Word × Accuracy) :
    T.runtimeSpaceInvariant a (T.clock a.1 a.2)
      ((T.runtimeLoopStep answer a)^[T.clock a.1 a.2] (some (T.runtimeInitial a))) := by
  let loop := T.runtimeLoopStep answer a
  have hbase : T.runtimeSpaceInvariant a 0 (some (T.runtimeInitial a)) := by
    intro cfg hcfg
    simp only [Option.some.injEq] at hcfg
    subst cfg
    exact T.runtimeInitial_spaceBound a
  have htrace : ∀ i, T.runtimeSpaceInvariant a i (loop^[i] (some (T.runtimeInitial a))) := by
    intro i
    induction i with
    | zero => exact hbase
    | succ i ih =>
      simpa only [Function.iterate_succ_apply'] using
        T.runtimeLoopStep_invariant answer a i _ ih
  simpa only [loop] using htrace (T.clock a.1 a.2)


end PolyTimeOracleScheme

/-- Convert a tidy polynomial-time certificate to a quantitative `O` certificate whose
bounds are a power of the encoded input length. All multiplicative constants are absorbed by
`ComputableTidilyInO`'s constant-factor convention. This is useful when composing a polynomial
post-processing routine with a separately quantified computation. -/
theorem polytime_inO {α β : Type} {encin : α ↪ List Bool} {encout : β ↪ List Bool}
    {f : α → β} (h : Turing.MultiTapeTM.ComputableTidilyInPolyTime f encin encout) :
    ∃ d, Turing.MultiTapeTM.ComputableTidilyInO f encin encout
      (fun a => ((encin a).length + 1) ^ d)
      (fun a => ((encin a).length + 1) ^ d) := by
  obtain ⟨d, hd⟩ :=
    PolyTimeOracleScheme.ComputableTidilyInPolyTime.inO_encodingLength h
  exact ⟨d, hd⟩

end AverageCaseComplexity
