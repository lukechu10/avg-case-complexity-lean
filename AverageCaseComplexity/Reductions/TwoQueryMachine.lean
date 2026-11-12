module

public import AverageCaseComplexity.Reductions.QueryProtocol
public import AverageCaseComplexity.Reductions.OracleScheme

@[expose] public section

namespace AverageCaseComplexity.OracleMachine

open Turing Turing.MultiTapeMachine

variable {k : ℕ} {S T : Type}

/-- Blank work tapes with explicit control, query buffer, reply and output. -/
def wordConfig (input : Word) (state : Option S) (query answer output : Word) :
    Config k Bool S Unit input where
  tapes := wordsCfg input state (fun _ => []) output
  channels _ := ⟨query, answer, 0⟩

@[simp] theorem start_wordConfig (M : MultiTapeMachine k Bool T Unit Id)
    (input : Word) (state : Option S) (q a o : Word) :
    Sequential.start M (wordConfig input state q a o) =
      wordConfig input (some M.initial) q a o := rfl

@[simp] theorem left_wordConfig (M : MultiTapeMachine k Bool T Unit Id)
    (input : Word) (state : Option S) (q a o : Word) :
    Sequential.left M (wordConfig input state q a o) =
      wordConfig input (some (state.elim (Sum.inr M.initial) Sum.inl)) q a o := rfl

@[simp] theorem right_wordConfig (input : Word) (state : Option T) (q a o : Word) :
    Sequential.right (State₀ := S) (wordConfig (k := k) input state q a o) =
      wordConfig input (state.map Sum.inr) q a o := rfl

/-- A convenient exact sequencing rule for restored ordinary tapes. -/
theorem runFrom_seq_words
    (first : MultiTapeMachine k Bool S Unit Id)
    (second : MultiTapeMachine k Bool T Unit Id) (L : Language)
    (t₁ t₂ : ℕ) (input q₀ a₀ o₀ q₁ a₁ o₁ q₂ a₂ o₂ : Word)
    (trace₁ trace₂ : List (Word × Bool))
    (h₁ : runFrom first L t₁ (wordConfig input (some first.initial) q₀ a₀ o₀) =
      (wordConfig input none q₁ a₁ o₁, trace₁))
    (h₂ : runFrom second L t₂ (wordConfig input (some second.initial) q₁ a₁ o₁) =
      (wordConfig input none q₂ a₂ o₂, trace₂)) :
    runFrom (first.seq second) L (t₁ + t₂)
        (wordConfig input (some (.inl first.initial)) q₀ a₀ o₀) =
      (wordConfig input none q₂ a₂ o₂, trace₁ ++ trace₂) := by
  have hh₁ : (runFrom first L t₁
      (wordConfig input (some first.initial) q₀ a₀ o₀)).1.tapes.state = none := by
    rw [h₁]; rfl
  have hh₂ : (runFrom second L t₂ (Sequential.start second
      (runFrom first L t₁ (wordConfig input (some first.initial) q₀ a₀ o₀)).1)).1.tapes.state = none := by
    simp only [h₁, start_wordConfig, h₂]
    rfl
  simpa only [left_wordConfig, Option.elim_some, h₁, Prod.fst, Prod.snd,
    start_wordConfig, h₂, right_wordConfig, Option.map_none] using
    runFrom_seq first second L t₁ t₂
      (wordConfig input (some first.initial) q₀ a₀ o₀) hh₁ hh₂

/-- A certified tidy computation prepares exactly its computed query, retaining
any previous reply and without submitting any additional oracle calls. -/
theorem runFrom_writeQuery_words (M : MultiTapeTM k Bool S) (L : Language)
    (input query answer output : Word) (time space : ℕ)
    (h : M.ComputesTidilyInTimeAndSpace input query time space) :
    runFrom (writeQuery M) L time (wordConfig input (some M.q₀) [] answer output) =
      (wordConfig input none query answer output, []) := by
  have hs : wordConfig (k := k) input (some M.q₀) [] answer output =
      queryConfig (M.initCfg input) answer output 0 := by
    apply Config.ext
    · simp [wordConfig, queryConfig, MultiTapeNTM.initCfg, Cfg.init, wordsCfg]
    · rfl
  rw [hs, runFrom_writeQuery, runFrom_eq_wordsCfg M input query time space h]
  rfl

/-- Two arbitrary deterministic query computations, with real tape instructions
for writing, submission, reply comparison and final answer emission. -/
noncomputable def twoQuery (first : MultiTapeTM k Bool S) (second : MultiTapeTM k Bool T) :
    MultiTapeMachine k Bool (S ⊕ (Bool ⊕ (T ⊕ (Option Bool ⊕ Bool)))) Unit Id :=
  (writeQuery first).seq (ask.seq ((writeQuery second).seq agree))

/-- Full machine-level execution: exactly two calls, in the prescribed order,
and a valid encoded agree-or-give-up answer. The oracle is arbitrary. -/
theorem run_twoQuery (first : MultiTapeTM k Bool S) (second : MultiTapeTM k Bool T)
    (L : Language) (input q₀ q₁ : Word) (t₀ s₀ t₁ s₁ : ℕ)
    (h₀ : first.ComputesTidilyInTimeAndSpace input q₀ t₀ s₀)
    (h₁ : second.ComputesTidilyInTimeAndSpace input q₁ t₁ s₁) :
    run (twoQuery first second) L (t₀ + (2 + (t₁ + 3))) input =
      (wordConfig input none [] [L q₁]
        (answerEncoding (Completeness.TwoQuery.combine (L q₀) (L q₁))),
        [(q₀, L q₀), (q₁, L q₁)]) := by
  have hw₀ := runFrom_writeQuery_words first L input q₀ [] [] t₀ s₀ h₀
  have hw₁ := runFrom_writeQuery_words second L input q₁ [L q₀] [] t₁ s₁ h₁
  have ha : runFrom (ask (k := k)) L 2
      (wordConfig input (some false) q₀ [] []) =
      (wordConfig input none [] [L q₀] [], [(q₀, L q₀)]) :=
    runFrom_ask L _ rfl
  have hg : runFrom (agree (k := k)) L 3
      (wordConfig input (some (.inl none)) q₁ [L q₀] []) =
      (wordConfig input none [] [L q₁]
        (answerEncoding (Completeness.TwoQuery.combine (L q₀) (L q₁))), [(q₁, L q₁)]) := by
    simpa only [wordConfig, queried, Cfg.withState, wordsCfg, List.nil_append] using
      runFrom_agree L (wordConfig (k := k) input (some (.inl none)) q₁ [L q₀] [])
        (L q₀) rfl (by simp [wordConfig, Config.answerSymbols, Channel.answerSymbol])
  have htail := runFrom_seq_words (writeQuery second) agree L t₁ 3 input
    [] [L q₀] [] q₁ [L q₀] [] [] [L q₁]
    (answerEncoding (Completeness.TwoQuery.combine (L q₀) (L q₁))) [] [(q₁, L q₁)] hw₁ hg
  have hmid := runFrom_seq_words ask ((writeQuery second).seq agree) L 2 (t₁ + 3) input
    q₀ [] [] [] [L q₀] [] [] [L q₁]
    (answerEncoding (Completeness.TwoQuery.combine (L q₀) (L q₁)))
    [(q₀, L q₀)] [(q₁, L q₁)] ha (by simpa using htail)
  have hfull := runFrom_seq_words (writeQuery first) (ask.seq ((writeQuery second).seq agree)) L
    t₀ (2 + (t₁ + 3)) input [] [] [] q₀ [] [] [] [L q₁]
    (answerEncoding (Completeness.TwoQuery.combine (L q₀) (L q₁)))
    [] [(q₀, L q₀), (q₁, L q₁)] hw₀ (by simpa using hmid)
  have hinit : (twoQuery first second).initialConfig input =
      wordConfig input (some (Sum.inl first.q₀)) [] [] [] := by
    apply Config.ext
    · simp [MultiTapeMachine.initialConfig, twoQuery, writeQuery,
        MultiTapeMachine.seq, wordConfig, Cfg.init, wordsCfg]
    · rfl
  change runFrom (twoQuery first second) L (t₀ + (2 + (t₁ + 3)))
    ((twoQuery first second).initialConfig input) = _
  rw [hinit]
  simpa only [twoQuery, writeQuery, List.nil_append] using hfull

/-- Uniform construction from any two tidily polynomial-time query functions.
The certificate contains an actual finite transition table, a uniform clock,
and exact two-query execution for every language oracle. -/
theorem exists_twoQuery_machine {α : Type} (encIn : α ↪ Word) (q₀ q₁ : α → Word)
    (h₀ : MultiTapeTM.ComputableTidilyInPolyTime q₀ encIn (Function.Embedding.refl Word))
    (h₁ : MultiTapeTM.ComputableTidilyInPolyTime q₁ encIn (Function.Embedding.refl Word)) :
    ∃ (tapes : ℕ) (State : Type) (_ : Finite State)
      (M : MultiTapeMachine tapes Bool State Unit Id) (c d : ℕ),
      ∀ (a : α) (L : Language), run M L (c * ((encIn a).length + 1) ^ d) (encIn a) =
        (wordConfig (encIn a) none [] [L (q₁ a)]
          (answerEncoding (Completeness.TwoQuery.combine (L (q₀ a)) (L (q₁ a)))),
          [(q₀ a, L (q₀ a)), (q₁ a, L (q₁ a))]) := by
  obtain ⟨t₀, s₀, ht₀, _, k₀, S₀, hfinite₀, M₀, hM₀⟩ := h₀
  obtain ⟨t₁, s₁, ht₁, _, k₁, S₁, hfinite₁, M₁, hM₁⟩ := h₁
  letI : Finite S₀ := hfinite₀
  letI : Finite S₁ := hfinite₁
  let first := M₀.extendTapes (Fin.castLEEmb (le_max_left k₀ k₁))
  let second := M₁.extendTapes (Fin.castLEEmb (le_max_right k₀ k₁))
  have hfirst (a : α) : first.ComputesTidilyInTimeAndSpace
      (encIn a) (q₀ a) (t₀ a) (s₀ a + (max k₀ k₁ - k₀)) :=
    (hM₀ a).extendTapes _
  have hsecond (a : α) : second.ComputesTidilyInTimeAndSpace
      (encIn a) (q₁ a) (t₁ a) (s₁ a + (max k₀ k₁ - k₁)) :=
    (hM₁ a).extendTapes _
  have htime : MultiTapeTM.PolyBounded (fun a => (encIn a).length)
      (fun a => t₀ a + (2 + (t₁ a + 3))) :=
    ((ht₀.add ht₁).add (MultiTapeTM.PolyBounded.const 5)).mono (by intro a; omega)
  obtain ⟨c, d, hbound⟩ := htime
  refine ⟨max k₀ k₁, S₀ ⊕ (Bool ⊕ (S₁ ⊕ (Option Bool ⊕ Bool))), inferInstance,
    twoQuery first second, c, d, ?_⟩
  intro a L
  have hs := run_twoQuery first second L (encIn a) (q₀ a) (q₁ a)
    (t₀ a) _ (t₁ a) _ (hfirst a) (hsecond a)
  have hh : (run (twoQuery first second) L (t₀ a + (2 + (t₁ a + 3))) (encIn a)).1.tapes.state =
      none := by rw [hs]; rfl
  exact (runFrom_eq_of_halted (twoQuery first second) L
    (t₀ a + (2 + (t₁ a + 3))) _ ((twoQuery first second).initialConfig (encIn a))
    (hbound a) hh).trans hs

end AverageCaseComplexity.OracleMachine
