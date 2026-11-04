module

public import AverageCaseComplexity.Reductions.Simulation
public import AverageCaseComplexity.Reductions.Accuracy
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Finite

@[expose] public section

namespace AverageCaseComplexity

namespace PolyTimeOracleScheme

/-- The finite configuration type used to execute the scheme's unchanged machine table. -/
abbrev RuntimeConfig (T : PolyTimeOracleScheme) :=
  Turing.MultiTapeMachine.FiniteConfig T.workTapes Bool (Fin T.stateCount) Unit

/-- Execute one already-selected instruction on finite storage, consulting the captured
partial-answer routine only at a query instruction. An unavailable answer aborts this step. -/
def runtimeActionStep (T : PolyTimeOracleScheme)
    (answer : Word × Accuracy → Word → Answer) (a : Word × Accuracy)
    (action : Turing.MultiTapeMachine.Action T.workTapes Bool (Fin T.stateCount) Unit)
    (cfg : T.RuntimeConfig) : Option T.RuntimeConfig :=
  match action with
  | .step action querySymbol answerMove =>
      some (cfg.step action querySymbol answerMove)
  | .query () next =>
      match answer a (cfg.channels ()).1 with
      | none => none
      | some b => some (cfg.receive () next [b])

/-- The configuration-level ordinary transition is a tidy polynomial-time operation. -/
theorem runtime_localStep_efficient (T : PolyTimeOracleScheme)
    (action : Turing.Action T.workTapes Bool (Fin T.stateCount)) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun cfg : T.RuntimeConfig => cfg.step action (fun _ => none) (fun _ => .zero))
      Turing.MultiTapeTM.encFiniteConfig Turing.MultiTapeTM.encFiniteConfig := by
  exact Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_step action
    (fun _ => none) (fun _ => .zero)

/-- Installing a fixed reply after a query is a tidy polynomial-time configuration operation. -/
theorem runtime_receive_efficient (T : PolyTimeOracleScheme)
    (next : Fin T.stateCount) (reply : List Bool) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun cfg : T.RuntimeConfig => cfg.receive () next reply)
      Turing.MultiTapeTM.encFiniteConfig Turing.MultiTapeTM.encFiniteConfig := by
  exact Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_receive
    (cfg := fun cfg : T.RuntimeConfig => cfg)
    (answer := fun _ : T.RuntimeConfig => reply)
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_eq fun _ => rfl)
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.const reply) () next

/-- One selected query instruction is efficiently executed when its answer is computed from the
original input and the current request. This is the runtime handler's aborting step certificate. -/
theorem runtime_queryStep_efficient
    {α : Type} {input : α ↪ List Bool} (T : PolyTimeOracleScheme)
    {param : α → Word × Accuracy} {cfg : α → T.RuntimeConfig}
    {answer : Word × Accuracy → Word → Answer}
    (hcfg : Turing.MultiTapeTM.ComputableTidilyInPolyTime cfg input
      Turing.MultiTapeTM.encFiniteConfig)
    (hanswer : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun x => answer (param x) ((cfg x).channels ()).1) input answerEncoding)
    (next : Fin T.stateCount) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun x => T.runtimeActionStep answer (param x) (.query () next) (cfg x))
      input (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig) := by
  have hbranch : ∀ reply : Answer,
      Turing.MultiTapeTM.ComputableTidilyInPolyTime
        (fun x => match reply with
          | none => (none : Option T.RuntimeConfig)
          | some b => some ((cfg x).receive () next [b]))
        input (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig) := by
    intro reply
    cases reply with
    | none => exact Turing.MultiTapeTM.ComputableTidilyInPolyTime.const none
    | some b =>
      have hreceive := Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_receive
        hcfg (Turing.MultiTapeTM.ComputableTidilyInPolyTime.const [b]) () next
      exact (Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionSome
        Turing.MultiTapeTM.encFiniteConfig).comp hreceive
  have h := Turing.MultiTapeTM.ComputableTidilyInPolyTime.finite_cases
    (tagEncoding := answerEncoding) hanswer hbranch
  exact h.of_enc_eq fun x => by
    rfl

/-- One already-selected instruction, including the cost of obtaining its answer, is a tidy
polynomial-time transformation on finite configurations. -/
theorem runtimeActionStep_efficient
    {α : Type} {input : α ↪ List Bool} (T : PolyTimeOracleScheme)
    {param : α → Word × Accuracy} {cfg : α → T.RuntimeConfig}
    {answer : Word × Accuracy → Word → Answer}
    (hcfg : Turing.MultiTapeTM.ComputableTidilyInPolyTime cfg input
      Turing.MultiTapeTM.encFiniteConfig)
    (hanswer : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun x => answer (param x) ((cfg x).channels ()).1) input answerEncoding)
    (action : Turing.MultiTapeMachine.Action T.workTapes Bool (Fin T.stateCount) Unit) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun x => T.runtimeActionStep answer (param x) action (cfg x))
      input (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig) := by
  cases action with
  | step localAction querySymbol answerMove =>
    have hstep := (Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_step
      localAction querySymbol answerMove).comp hcfg
    exact (Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionSome
      Turing.MultiTapeTM.encFiniteConfig).comp hstep
  | query oracle next =>
    cases oracle
    exact T.runtime_queryStep_efficient hcfg hanswer next

/-- The finite tuple observed by the transition table. -/
abbrev RuntimeObservation (T : PolyTimeOracleScheme) :=
  Option (Fin T.stateCount) ×
    (Option Bool × ((Fin T.workTapes → Option Bool) × (Unit → Option Bool)))

def runtimeObservation {T : PolyTimeOracleScheme} (cfg : T.RuntimeConfig) :
    T.RuntimeObservation :=
  (cfg.tapes.state, (cfg.tapes.inputSymbol,
    (cfg.tapes.workTapeSymbols, cfg.answerSymbols)))

/-- One actual finite-control machine instruction, with halted configurations retained. -/
def runtimeMachineStep (T : PolyTimeOracleScheme)
    (answer : Word × Accuracy → Word → Answer) (a : Word × Accuracy)
    (cfg : T.RuntimeConfig) : Option T.RuntimeConfig :=
  match cfg.tapes.state with
  | none => some cfg
  | some state =>
    T.runtimeActionStep answer a
      (T.machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols) cfg

/-- The unchanged finite transition table can be dispatched in tidy polynomial time. This is a
real one-instruction runtime certificate, parameterized by the efficient request-answer map. -/
theorem runtimeMachineStep_efficient
    {α : Type} {input : α ↪ List Bool} (T : PolyTimeOracleScheme)
    {param : α → Word × Accuracy} {cfg : α → T.RuntimeConfig}
    {answer : Word × Accuracy → Word → Answer}
    (hcfg : Turing.MultiTapeTM.ComputableTidilyInPolyTime cfg input
      Turing.MultiTapeTM.encFiniteConfig)
    (hanswer : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun x => answer (param x) ((cfg x).channels ()).1) input answerEncoding) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun x => T.runtimeMachineStep answer (param x) (cfg x))
      input (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig) := by
  let hstate := Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteCfg_state.comp
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_tapes.comp hcfg)
  let hinput := Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteCfg_inputSymbol.comp
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_tapes.comp hcfg)
  let hwork := Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteCfg_workTapeSymbols.comp
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_tapes.comp hcfg)
  let hsymbols := Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_answerSymbols.comp hcfg
  have htag : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun x => T.runtimeObservation (cfg x)) input (Turing.MultiTapeTM.encFinite
        T.RuntimeObservation) := by
    exact (Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_finite id).comp
      (hstate.prod (hinput.prod (hwork.prod hsymbols)) )
  have hbranch : ∀ tag : T.RuntimeObservation,
      Turing.MultiTapeTM.ComputableTidilyInPolyTime
        (fun x => match tag.1 with
          | none => some (cfg x)
          | some state => T.runtimeActionStep answer (param x)
              (T.machine.tr state tag.2.1 tag.2.2.1 tag.2.2.2) (cfg x))
        input (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig) := by
    intro tag
    cases hs : tag.1 with
    | none =>
      simpa only [hs, Function.comp_def] using
        (Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionSome
          Turing.MultiTapeTM.encFiniteConfig).comp hcfg
    | some state =>
      simpa only [hs] using T.runtimeActionStep_efficient hcfg hanswer
        (T.machine.tr state tag.2.1 tag.2.2.1 tag.2.2.2)
  have hdispatch := Turing.MultiTapeTM.ComputableTidilyInPolyTime.finite_cases
    (tagEncoding := Turing.MultiTapeTM.encFinite T.RuntimeObservation) htag hbranch
  exact hdispatch.of_enc_eq fun x => by
    simp [runtimeMachineStep, runtimeObservation]

/-- The state of the bounded deterministic interpreter. `none` is an absorbing abort. -/
def runtimeLoopStep (T : PolyTimeOracleScheme)
    (answer : Word × Accuracy → Word → Answer) (a : Word × Accuracy) :
    Option T.RuntimeConfig → Option T.RuntimeConfig
  | none => none
  | some cfg => T.runtimeMachineStep answer a cfg

/-- The initial finite configuration for the encoded machine input. -/
def runtimeInitial (T : PolyTimeOracleScheme) (a : Word × Accuracy) : T.RuntimeConfig :=
  Turing.MultiTapeMachine.FiniteConfig.init T.machine.initial (schemeInputEncoding a)

/-- Every successful deterministic instruction respects the library's real tape-space bound.
Oracle replies are either absent (aborting) or a singleton Boolean word. -/
theorem runtimeMachineStep_spaceBound (T : PolyTimeOracleScheme)
    (answer : Word × Accuracy → Word → Answer) (a : Word × Accuracy)
    {inputSize steps : ℕ} {cfg next : T.RuntimeConfig}
    (hspace : Turing.MultiTapeMachine.FiniteConfig.SpaceBound inputSize steps 1 cfg)
    (hnext : T.runtimeMachineStep answer a cfg = some next) :
    Turing.MultiTapeMachine.FiniteConfig.SpaceBound inputSize (steps + 1) 1 next := by
  cases hs : cfg.tapes.state with
  | none =>
    simp [runtimeMachineStep, hs] at hnext
    cases hnext
    exact hspace.mono le_rfl (by omega) le_rfl
  | some state =>
    simp only [runtimeMachineStep, hs] at hnext
    cases ht : T.machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
    | step localAction querySymbol answerMove =>
      simp only [runtimeActionStep, ht, Option.some.injEq] at hnext
      cases hnext
      exact Turing.MultiTapeMachine.FiniteConfig.SpaceBound.step hspace
        localAction querySymbol answerMove
    | query oracle nextState =>
      cases oracle
      cases ha : answer a (cfg.channels ()).1 with
      | none => simp [runtimeActionStep, ht, ha] at hnext
      | some bit =>
        simp only [runtimeActionStep, ht, ha, Option.some.injEq] at hnext
        cases hnext
        apply Turing.MultiTapeMachine.FiniteConfig.SpaceBound.receive hspace () nextState [bit]
        simp

/-- The clock-indexed invariant for the actual finite interpreter loop. -/
def runtimeSpaceInvariant (T : PolyTimeOracleScheme) (a : Word × Accuracy)
    (i : ℕ) (state : Option T.RuntimeConfig) : Prop :=
  ∀ cfg, state = some cfg →
    Turing.MultiTapeMachine.FiniteConfig.SpaceBound
      (schemeInputEncoding a).length i 1 cfg

theorem runtimeLoopStep_invariant (T : PolyTimeOracleScheme)
    (answer : Word × Accuracy → Word → Answer) (a : Word × Accuracy)
    (i : ℕ) (state : Option T.RuntimeConfig)
    (hinv : T.runtimeSpaceInvariant a i state) :
    T.runtimeSpaceInvariant a (i + 1) (T.runtimeLoopStep answer a state) := by
  cases state with
  | none => intro cfg hcfg; simp [runtimeLoopStep] at hcfg
  | some cfg =>
    intro next hnext
    simp only [runtimeLoopStep] at hnext
    exact T.runtimeMachineStep_spaceBound answer a (hinv cfg rfl) hnext

theorem runtimeInitial_spaceBound (T : PolyTimeOracleScheme) (a : Word × Accuracy) :
    Turing.MultiTapeMachine.FiniteConfig.SpaceBound
      (schemeInputEncoding a).length 0 1 (T.runtimeInitial a) := by
  exact Turing.MultiTapeMachine.FiniteConfig.spaceBound_init
    T.machine.initial (schemeInputEncoding a) 1

/-- The captured runtime loop instruction is tidy on the joint original input and state.
The handler certificate is used on the original input paired with the current query buffer. -/
theorem runtimeLoopStep_efficient (T : PolyTimeOracleScheme)
    {answer : Word × Accuracy → Word → Answer}
    (hanswer : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Word => answer p.1 p.2)
      (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits) answerEncoding) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Option T.RuntimeConfig =>
        T.runtimeLoopStep answer p.1 p.2)
      (Turing.MultiTapeTM.encPair schemeInputEncoding (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig))
      (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig) := by
  have hword : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun a : Word × Accuracy => schemeInputEncoding a) schemeInputEncoding Turing.MultiTapeTM.encBits :=
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_eq fun _ => rfl
  have hinit : Turing.MultiTapeTM.ComputableTidilyInPolyTime T.runtimeInitial
      schemeInputEncoding Turing.MultiTapeTM.encFiniteConfig := by
    exact Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_init
      (Oracle := Unit) hword T.machine.initial
  have hstate : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Option T.RuntimeConfig => p.2)
      (Turing.MultiTapeTM.encPair schemeInputEncoding (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig))
      (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig) := by
    fun_prop
  have hparam : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Option T.RuntimeConfig => p.1)
      (Turing.MultiTapeTM.encPair schemeInputEncoding (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig))
      schemeInputEncoding := by
    fun_prop
  have hget : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Option T.RuntimeConfig => p.2.getD (T.runtimeInitial p.1))
      (Turing.MultiTapeTM.encPair schemeInputEncoding (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig))
      Turing.MultiTapeTM.encFiniteConfig :=
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionGetDWithInput hstate
      (hinit.comp hparam)
  have hrequest : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Option T.RuntimeConfig =>
        ((p.2.getD (T.runtimeInitial p.1)).channels ()).1)
      (Turing.MultiTapeTM.encPair schemeInputEncoding (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig))
      Turing.MultiTapeTM.encBits := by
    fun_prop
  have hanswerState := hanswer.comp (hparam.prod hrequest)
  have hmachine := T.runtimeMachineStep_efficient hget hanswerState
  have hactive := Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionIsSome hstate
  have hstep := hactive.cond hmachine
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.const none)
  exact hstep.of_enc_eq fun ⟨a, state⟩ => by
    cases state <;> rfl

/-- SpaceBound gives a linear encoding-size bound for every loop prefix. -/
theorem runtimeLoop_encodingBound (T : PolyTimeOracleScheme) (a : Word × Accuracy)
    (i : ℕ) (state : Option T.RuntimeConfig)
    (hi : i ≤ T.clock a.1 a.2)
    (hinv : T.runtimeSpaceInvariant a i state) :
    ∃ c, (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig state).length ≤
      1 + c * ((schemeInputEncoding a).length + T.clock a.1 a.2 + 2) := by
  cases state with
  | none => exact ⟨0, by simp [Turing.MultiTapeTM.encOption]⟩
  | some cfg =>
    have hspace := hinv cfg rfl
    obtain ⟨c, hc⟩ := Turing.MultiTapeTM.length_encFiniteConfig_le
      (k := T.workTapes) (State := Fin T.stateCount) (Oracle := Unit)
    have hcfg := hc (schemeInputEncoding a).length i 1 cfg hspace
    simp only [Turing.MultiTapeTM.encOption_some, List.length_cons]
    refine ⟨c, ?_⟩
    have hmono : (Turing.MultiTapeTM.encFiniteConfig cfg).length ≤
        c * ((schemeInputEncoding a).length + T.clock a.1 a.2 + 2) := by
      exact hcfg.trans (Nat.mul_le_mul_left c (by omega))
    omega

/-- The runtime interpreter's full bounded loop is tidy polynomial time. The final state
satisfies its SpaceBound invariant at the full clock value. -/
theorem runtimeLoop_efficient (T : PolyTimeOracleScheme)
    {answer : Word × Accuracy → Word → Answer}
    (hanswer : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Word => answer p.1 p.2)
      (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits) answerEncoding) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun a => (T.runtimeLoopStep answer a)^[T.clock a.1 a.2]
        (some (T.runtimeInitial a)))
      schemeInputEncoding (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig) ∧
    ∀ a, T.runtimeSpaceInvariant a (T.clock a.1 a.2)
      ((T.runtimeLoopStep answer a)^[T.clock a.1 a.2] (some (T.runtimeInitial a))) := by
  have hpar : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun a : Word × Accuracy => a) schemeInputEncoding schemeInputEncoding :=
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_eq fun _ => rfl
  have hlengthInput := Turing.MultiTapeTM.ComputableTidilyInPolyTime.encoding_length
    schemeInputEncoding
  have hcount : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun a : Word × Accuracy => T.clock a.1 a.2) schemeInputEncoding
      Turing.MultiTapeTM.encUnary := by
    change Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun a : Word × Accuracy => T.coefficient * ((schemeInputEncoding a).length + 1) ^ T.degree)
      schemeInputEncoding Turing.MultiTapeTM.encUnary
    fun_prop
  have hinitCfg : Turing.MultiTapeTM.ComputableTidilyInPolyTime T.runtimeInitial
      schemeInputEncoding Turing.MultiTapeTM.encFiniteConfig := by
    have hword : Turing.MultiTapeTM.ComputableTidilyInPolyTime
        (fun a : Word × Accuracy => schemeInputEncoding a) schemeInputEncoding
        Turing.MultiTapeTM.encBits :=
      Turing.MultiTapeTM.ComputableTidilyInPolyTime.of_eq fun _ => rfl
    exact Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_init
      (Oracle := Unit) hword T.machine.initial
  have hinit := (Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionSome
    Turing.MultiTapeTM.encFiniteConfig).comp hinitCfg
  have hstep := T.runtimeLoopStep_efficient hanswer
  obtain ⟨spaceCoeff, hlength⟩ := Turing.MultiTapeTM.length_encFiniteConfig_le
    (k := T.workTapes) (State := Fin T.stateCount) (Oracle := Unit)
  let size : ℕ → ℕ := fun n => 1 + spaceCoeff *
    (n + T.coefficient * (n + 1) ^ T.degree + 2)
  have hsize : Cslib.PolynomiallyBounded size := by
    dsimp [size]
    fun_prop
  have hbound : ∀ a i state, i ≤ T.clock a.1 a.2 → T.runtimeSpaceInvariant a i state →
      (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig state).length ≤
        size (schemeInputEncoding a).length := by
    intro a i state hi hinv
    cases state with
    | none => simp [Turing.MultiTapeTM.encOption, size]
    | some cfg =>
      have hspace := hinv cfg rfl
      have hcfg := hlength (schemeInputEncoding a).length i 1 cfg hspace
      change (Turing.MultiTapeTM.encFiniteConfig cfg).length + 1 ≤
        1 + spaceCoeff * ((schemeInputEncoding a).length +
          T.coefficient * ((schemeInputEncoding a).length + 1) ^ T.degree + 2)
      have hclock : T.clock a.1 a.2 =
          T.coefficient * ((schemeInputEncoding a).length + 1) ^ T.degree := by
        rfl
      have hi' : i ≤ T.coefficient * ((schemeInputEncoding a).length + 1) ^ T.degree := by
        simpa only [hclock] using hi
      have hsizele : (schemeInputEncoding a).length + i + 2 ≤
          (schemeInputEncoding a).length +
            T.coefficient * ((schemeInputEncoding a).length + 1) ^ T.degree + 2 := by omega
      have hmono : (Turing.MultiTapeTM.encFiniteConfig cfg).length ≤
          spaceCoeff * ((schemeInputEncoding a).length +
            T.coefficient * ((schemeInputEncoding a).length + 1) ^ T.degree + 2) := by
        exact hcfg.trans (Nat.mul_le_mul_left spaceCoeff hsizele)
      omega
  have hloop := Turing.MultiTapeTM.ComputableTidilyInPolyTime.iterateWith_spec
    (par := fun a : Word × Accuracy => a)
    (count := fun a => T.clock a.1 a.2)
    (init := fun a => some (T.runtimeInitial a))
    (step := fun a state => T.runtimeLoopStep answer a state)
    hpar hcount hinit hstep T.runtimeSpaceInvariant
    (fun a => by
      intro cfg hcfg
      cases hcfg
      exact T.runtimeInitial_spaceBound a)
    (fun a i state hi hinv => T.runtimeLoopStep_invariant answer a i state hinv)
    hsize hbound
  refine ⟨?_, ?_⟩
  · simpa only [Function.iterate_succ_apply'] using hloop.1
  · intro a
    exact hloop.2 a

/-- The certified finite instruction is exactly interpretation of the library's
finite machine instruction, including abort on an unavailable answer. -/
theorem runtimeMachineStep_eq_interpret (T : PolyTimeOracleScheme)
    (answer : Word × Accuracy → Word → Answer) (a : Word × Accuracy) (cfg : T.RuntimeConfig) :
    T.runtimeMachineStep answer a cfg =
      Cslib.OracleComp.interpret (m := Option) (answer a)
        (T.machine.finiteStep pure
          (fun _ request => List.singleton <$> Cslib.OracleComp.query request) cfg) := by
  cases hs : cfg.tapes.state with
  | none => simp [runtimeMachineStep, Turing.MultiTapeMachine.finiteStep, hs]
  | some state =>
    cases ht : T.machine.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
    | step action symbol move =>
      simp [runtimeMachineStep, runtimeActionStep, Turing.MultiTapeMachine.finiteStep, hs, ht]
    | query oracle next =>
      cases oracle
      cases ha : answer a (cfg.channels ()).1 <;>
        simp [runtimeMachineStep, runtimeActionStep, Turing.MultiTapeMachine.finiteStep, hs, ht, ha]
      all_goals rfl

/-- The absorbing-abort functional loop preserves the entire interpreted execution. -/
theorem runtimeLoop_eq_interpret (T : PolyTimeOracleScheme)
    (answer : Word × Accuracy → Word → Answer) (a : Word × Accuracy)
    (fuel : ℕ) (cfg : T.RuntimeConfig) :
    (T.runtimeLoopStep answer a)^[fuel] (some cfg) =
      Cslib.OracleComp.interpret (m := Option) (answer a)
        (Cslib.OracleComp.iterate fuel
          (T.machine.finiteStep pure
            (fun _ request => List.singleton <$> Cslib.OracleComp.query request)) cfg) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply', Cslib.OracleComp.iterate_succ,
      Cslib.OracleComp.interpret_bind, ← ih]
    cases hh : (T.runtimeLoopStep answer a)^[fuel] (some cfg) with
    | none => rfl
    | some next => exact T.runtimeMachineStep_eq_interpret answer a next

/-- Decode a final optional configuration; absence means oracle simulation aborted. -/
def runtimeResult (T : PolyTimeOracleScheme) (state : Option T.RuntimeConfig) : Answer :=
  state.bind (fun cfg => decodeOracleAnswer cfg.tapes.output)

/-- The runtime interpreter realizes precisely the semantic partial-oracle substitution. -/
theorem runtimeResult_eq_simulate (T : PolyTimeOracleScheme)
    (answer : Word × Accuracy → Word → Answer) (a : Word × Accuracy) :
    T.runtimeResult ((T.runtimeLoopStep answer a)^[T.clock a.1 a.2]
      (some (T.runtimeInitial a))) = T.simulate answer a := by
  rw [T.runtimeLoop_eq_interpret]
  have hfinite := Turing.MultiTapeMachine.finiteRunFrom_init T.machine
    (spec := fun _ : Word => Bool) pure
    (fun _ request => List.singleton <$> Cslib.OracleComp.query request)
    (T.clock a.1 a.2) (schemeInputEncoding a)
  have hprogram : T.program a = decodeOracleAnswer <$>
      T.machine.finiteRunFrom pure
        (fun _ request => List.singleton <$> Cslib.OracleComp.query request)
        (T.clock a.1 a.2) (T.runtimeInitial a) := by
    rw [runtimeInitial, hfinite]
    simp only [program, OracleMachine.program, OracleMachine.programFrom,
      Turing.MultiTapeMachine.run, Turing.MultiTapeMachine.runFrom, Functor.map_map]
  rw [simulate, hprogram]
  simp only [Turing.MultiTapeMachine.finiteRunFrom, Cslib.OracleComp.interpret_map]
  change Option.bind _ _ = Option.join (Option.map _ (Option.map _ _))
  cases Cslib.OracleComp.interpret (m := Option) (answer a)
    (Cslib.OracleComp.iterate (T.clock a.1 a.2)
      (T.machine.finiteStep pure
        (fun _ request => List.singleton <$> Cslib.OracleComp.query request)) (T.runtimeInitial a)) <;> rfl

/-- Decode the existing two-bit answer format in tidy polynomial time. -/
theorem decodeOracleAnswer_efficient :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime decodeOracleAnswer
      Turing.MultiTapeTM.encBits answerEncoding := by
  have hfalse := (Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_eq
    Turing.MultiTapeTM.encBits).comp
      ((Turing.MultiTapeTM.ComputableTidilyInPolyTime.id').prod
        (Turing.MultiTapeTM.ComputableTidilyInPolyTime.const [true, false]))
  have htrue := (Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_eq
    Turing.MultiTapeTM.encBits).comp
      ((Turing.MultiTapeTM.ComputableTidilyInPolyTime.id').prod
        (Turing.MultiTapeTM.ComputableTidilyInPolyTime.const [true, true]))
  have h : Turing.MultiTapeTM.ComputableTidilyInPolyTime _
      Turing.MultiTapeTM.encBits answerEncoding :=
    hfalse.cond (Turing.MultiTapeTM.ComputableTidilyInPolyTime.const (some false))
    (htrue.cond (Turing.MultiTapeTM.ComputableTidilyInPolyTime.const (some true))
      (Turing.MultiTapeTM.ComputableTidilyInPolyTime.const none))
  apply h.of_enc_eq
  intro word
  cases word with
  | nil => rfl
  | cons b word =>
    cases word with
    | nil => cases b <;> rfl
    | cons c word =>
      cases word with
      | nil => cases b <;> cases c <;> rfl
      | cons d word => simp [decodeOracleAnswer]

/-- Decoding an optional finite configuration is certified, including the abort flag. -/
theorem runtimeResult_efficient (T : PolyTimeOracleScheme) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime T.runtimeResult
      (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig) answerEncoding := by
  let defaultCfg := T.runtimeInitial ([], ⟨1, by decide⟩)
  have hstate : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun s : Option T.RuntimeConfig => s)
      (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig)
      (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encFiniteConfig) := .id'
  have hget := Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionGetDWithInput hstate
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.const defaultCfg)
  have hout := Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteCfg_output.comp
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.finiteConfig_tapes.comp hget)
  have hdecode := decodeOracleAnswer_efficient.comp hout
  have h := (Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionIsSome hstate).cond hdecode
    (Turing.MultiTapeTM.ComputableTidilyInPolyTime.const none)
  exact h.of_enc_eq fun state => by cases state <;> rfl

/-- Deterministic polynomial-time oracle substitution, including the cost of every
partial-oracle call, tape operation, and the bounded interpreter loop. -/
theorem simulate_efficient (T : PolyTimeOracleScheme)
    {answer : Word × Accuracy → Word → Answer}
    (hanswer : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Word => answer p.1 p.2)
      (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits) answerEncoding) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime (T.simulate answer)
      schemeInputEncoding answerEncoding := by
  have hh := T.runtimeResult_efficient.comp (T.runtimeLoop_efficient hanswer).1
  exact hh.of_enc_eq (fun a => congrArg answerEncoding (T.runtimeResult_eq_simulate answer a).symm)

end PolyTimeOracleScheme

end AverageCaseComplexity
