module

public import AverageCaseComplexity.Completeness.BoundedMachine
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Machine

@[expose] public section

/-! # Structured fair-table replay bounds

This file certifies resource invariants for the run of two already-structured universal
 descriptions. In particular, no raw-code parser or well-formedness assumption is involved.
-/

namespace AverageCaseComplexity.Completeness.TwoQuery

open Turing.MultiTapeTM
open Turing.MultiTapeTM.Universal
/-- Replay `coins` by selecting the false or true description at each step. -/
def runStructuredTables (p : Desc × (Desc × (List ℕ × Word))) : List ℕ :=
  let df := p.1
  let dt := p.2.1
  let input := p.2.2.1
  let coins := p.2.2.2
  let step (c : SCfg × List ℕ) (b : Bool) : SCfg × List ℕ :=
    stepOut (if b then dt else df) input c
  (coins.foldl step (init df, [])).2

/-- Common-description-size monotonicity for the configuration invariant. -/
private theorem inv_size_mono {D D' X j : ℕ} {c : SCfg}
    (h : Inv D X j c) (hD : D ≤ D') : Inv D' X j c := by
  refine ⟨?_, h.inputPos, ?_, ?_⟩
  · exact h.state.trans hD
  · exact h.tapes.trans hD
  · intro t ht
    obtain ⟨hh, hl, hv⟩ := h.workTapes t ht
    exact ⟨hh, hl, fun o ho => (hv o ho).trans hD⟩

private theorem tapeInv_mono {D j j' : ℕ} {t : Tape} (h : TapeInv D j t)
    (hj : j ≤ j') : TapeInv D j' t := by
  obtain ⟨hh, hl, hv⟩ := h
  exact ⟨hh.trans hj, hl.trans (by omega), hv⟩

private theorem getD_headD_le_local {D : ℕ} {l : List (Option ℕ)}
    (h : ∀ o ∈ l, o.getD 0 ≤ D) : (l.headD none).getD 0 ≤ D := by
  cases l with
  | nil => simp
  | cons o l => exact h o (List.mem_cons_self ..)

private theorem tapeInv_apply {D j : ℕ} {t : Tape} (h : TapeInv D j t) {a : TapeAct}
    (ha : (a.1.getD none).getD 0 ≤ D) : TapeInv D (j + 1) (t.apply a) := by
  obtain ⟨hh, hl, hv⟩ := h
  obtain ⟨w, m⟩ := a
  have ⟨hl', hv'⟩ : (w.elim t t.write).left.length + (w.elim t t.write).right.length ≤
      2 * j + 1 ∧ ∀ o ∈ (w.elim t t.write).left ++ (w.elim t t.write).right,
        o.getD 0 ≤ D := by
    rcases w with _ | o
    · exact ⟨by simp; omega, hv⟩
    · refine ⟨by simp only [Option.elim, Tape.write, List.length_cons,
          List.length_tail]; omega, fun o' ho' => ?_⟩
      simp only [Option.elim, Tape.write, List.mem_append, List.mem_cons] at ho'
      rcases ho' with ho' | rfl | ho'
      · exact hv o' (List.mem_append_left _ ho')
      · exact ha
      · exact hv o' (List.mem_append_right _ (List.mem_of_mem_tail ho'))
  have hhead : (w.elim t t.write).head = t.head := by cases w <;> rfl
  have hvl : ∀ o ∈ (w.elim t t.write).left, o.getD 0 ≤ D :=
    fun o ho => hv' o (List.mem_append_left _ ho)
  have hvr : ∀ o ∈ (w.elim t t.write).right, o.getD 0 ≤ D :=
    fun o ho => hv' o (List.mem_append_right _ ho)
  rcases m with _ | _ | _
  · exact ⟨by simp only [Tape.apply, Tape.move, hhead]; omega,
      by simp only [Tape.apply, Tape.move]; omega, hv'⟩
  · refine ⟨by simp only [Tape.apply, Tape.move, hhead]; omega,
      by simp only [Tape.apply, Tape.move, List.length_tail, List.length_cons]; omega,
      fun o ho => ?_⟩
    simp only [Tape.apply, Tape.move, List.mem_append, List.mem_cons] at ho
    rcases ho with ho | rfl | ho
    · exact hvl o (List.mem_of_mem_tail ho)
    · exact getD_headD_le_local hvl
    · exact hvr o ho
  · refine ⟨by simp only [Tape.apply, Tape.move, hhead]; omega,
      by simp only [Tape.apply, Tape.move, List.length_tail, List.length_cons]; omega,
      fun o ho => ?_⟩
    simp only [Tape.apply, Tape.move, Tape.read, List.mem_append, List.mem_cons] at ho
    rcases ho with (rfl | ho) | ho
    · exact getD_headD_le_local hvr
    · exact hvl o ho
    · exact hvr o (List.mem_of_mem_tail ho)

private theorem mem_applyTapes_local {ts : List Tape} {as : List TapeAct} {t' : Tape}
    (h : t' ∈ applyTapes ts as) : ∃ t ∈ ts, t' = t ∨ ∃ a ∈ as, t' = t.apply a := by
  induction ts generalizing as with
  | nil => simp [applyTapes] at h
  | cons t ts ih => cases as <;> simp only [applyTapes, List.mem_cons] at h <;> grind

private theorem inv_init_common (df : Desc) (input : List ℕ) {D : ℕ}
    (hD : descLen df ≤ D) : Inv D input.length 0 (init df) := by
  refine ⟨?_, by simp [init], ?_, ?_⟩
  · have hq : df.q₀ ≤ descLen df := by
      change df.q₀ ≤ (eDesc df).length
      simp only [eDesc_apply, length_encPair, encUnary_apply, List.length_replicate]
      omega
    exact hq.trans hD
  · have ht : df.tapes ≤ descLen df := by
      change df.tapes ≤ (eDesc df).length
      simp only [eDesc_apply, length_encPair, encUnary_apply, List.length_replicate]
      omega
    simpa [init] using ht.trans hD
  · intro t ht
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp ht
    exact ⟨by simp, by simp, by simp⟩

private theorem option_number_le_encoding (o : Option ℕ) :
    o.getD 0 ≤ (eSym o).length := by
  cases o <;> simp

private theorem action_next_le (d : Desc) {e : Key × Act} (he : e ∈ d.table) :
    e.2.state.getD 0 ≤ descLen d := by
  have hrow := length_le_encList_of_mem (encPair eKey eAct) he
  have hact := (length_le_encPair_right eKey eAct e).trans hrow
  have hval := option_number_le_encoding e.2.state
  simp only [descLen, eDesc_apply, eAct_apply, length_encPair] at hact hval ⊢
  omega

private theorem action_output_le (d : Desc) {e : Key × Act} (he : e ∈ d.table) :
    e.2.output.getD 0 ≤ descLen d := by
  have hrow := length_le_encList_of_mem (encPair eKey eAct) he
  have hact := (length_le_encPair_right eKey eAct e).trans hrow
  have hval := option_number_le_encoding e.2.output
  simp only [descLen, eDesc_apply, eAct_apply, length_encPair] at hact hval ⊢
  omega

private theorem action_write_le (d : Desc) {e : Key × Act} (he : e ∈ d.table)
    {ta : TapeAct} (hta : ta ∈ e.2.workTapes) :
    (ta.1.getD none).getD 0 ≤ descLen d := by
  have hrow := length_le_encList_of_mem (encPair eKey eAct) he
  have hact := (length_le_encPair_right eKey eAct e).trans hrow
  have hta' := length_le_encList_of_mem eTA hta
  have hval := option_number_le_encoding (ta.1.getD none)
  have hopt : (eSym (ta.1.getD none)).length ≤ (encOption eSym ta.1).length := by
    cases ta.1 <;> simp
  simp only [descLen, eDesc_apply, eAct_apply, length_encPair] at hact hta' hval hopt ⊢
  omega

/-- One step remains inside a common invariant even when the chosen description changes. -/
private theorem inv_step_common (d : Desc) {D X j : ℕ} {x : List ℕ} {c : SCfg}
    (h : Inv D X j c) (hD : descLen d ≤ D) (hX : x.length = X) :
    Inv D X (j + 1) (step d x c).1 ∧ (step d x c).2.getD 0 ≤ D := by
  rcases hs : c.state with _ | q
  · rw [show Universal.step d x c = (c, none) by simp [Universal.step, hs]]
    exact ⟨⟨h.state, h.inputPos, h.tapes, fun t ht => tapeInv_mono (h.workTapes t ht) (by omega)⟩,
      by simp⟩
  rcases hf : d.table.find? (·.1 = c.key x q) with _ | ⟨key, act⟩
  · rw [show Universal.step d x c = ({ c with state := none }, none) by
      simp [Universal.step, hs, hf]]
    exact ⟨⟨by simp, h.inputPos, h.tapes, fun t ht => tapeInv_mono (h.workTapes t ht) (by omega)⟩,
      by simp⟩
  · rw [show Universal.step d x c = (act.apply x c, act.output) by
      simp [Universal.step, hs, hf]]
    have he := List.mem_of_find?_eq_some hf
    have hnext : act.state.getD 0 ≤ D := (action_next_le d he).trans hD
    have hout : act.output.getD 0 ≤ D := (action_output_le d he).trans hD
    refine ⟨?_, hout⟩
    refine ⟨hnext, ?_, ?_, ?_⟩
    · have hin : c.inputPos ≤ x.length + 1 := by rw [hX]; exact h.inputPos
      have hm := moveInput_le hin act.inputTape
      change moveInput c.inputPos (inputSymbol x c.inputPos) act.inputTape ≤ X + 1
      rw [← hX]
      exact hm
    · simpa [Act.apply, length_applyTapes_eq] using h.tapes
    · intro t' ht'
      obtain ⟨t, ht, hsame | ⟨ta, hta, happly⟩⟩ := mem_applyTapes_local ht'
      · rw [hsame]
        exact tapeInv_mono (h.workTapes t ht) (by omega)
      · rw [happly]
        exact tapeInv_apply (h.workTapes t ht) ((action_write_le d he hta).trans hD)

/-- The selected-table fold preserves a common size/clock invariant. -/
private theorem fold_inv (df dt : Desc) (input : List ℕ) (coins : Word)
    (D : ℕ) (hdf : descLen df ≤ D) (hdt : descLen dt ≤ D) :
    ∀ i ≤ coins.length,
      Inv D input.length i
        ((coins.take i).foldl
          (fun c b => stepOut (if b then dt else df) input c) (init df, [])).1 ∧
      ((coins.take i).foldl
          (fun c b => stepOut (if b then dt else df) input c) (init df, [])).2.length ≤ i ∧
      ∀ o ∈ ((coins.take i).foldl
          (fun c b => stepOut (if b then dt else df) input c) (init df, [])).2, o ≤ D := by
  intro i hi
  induction i with
  | zero =>
      simp only [List.take_zero, List.foldl_nil]
      refine ⟨inv_init_common df input hdf, by simp, ?_⟩
      simp
  | succ i ih =>
      have hi' : i ≤ coins.length := by omega
      obtain ⟨hc, hlen, hout⟩ := ih hi'
      have hbnd : i < coins.length := by omega
      let b := coins[i]
      let prev := (coins.take i).foldl
        (fun c bit => stepOut (if bit then dt else df) input c) (init df, [])
      have htake : coins.take (i + 1) = coins.take i ++ [b] := by
        rw [List.take_add_one]
        simp [b, hbnd]
      have hfold : (coins.take (i + 1)).foldl
          (fun c bit => stepOut (if bit then dt else df) input c) (init df, []) =
          stepOut (if b then dt else df) input prev := by
        simp [htake, prev, List.foldl_append]
      have hstep := inv_step_common (if b then dt else df) hc
        (by split_ifs <;> assumption) rfl
      rw [hfold]
      refine ⟨?_, ?_, ?_⟩
      · simpa [stepOut, prev] using hstep.1
      · change (prev.2 ++ (step (if b then dt else df) input prev.1).2.toList).length ≤ i + 1
        have hlen' : prev.2.length ≤ i := by simpa [prev] using hlen
        cases hs : (step (if b then dt else df) input prev.1).2 <;>
          simp [List.length_append] <;> omega
      · intro o ho
        simp only [stepOut, List.mem_append, Option.mem_toList] at ho
        rcases ho with ho | ho
        · exact hout o ho
        · cases hs : (step (if b then dt else df) input prev.1).2 with
          | none => simp [hs] at ho
          | some n =>
              simp [hs] at ho
              subst o
              have hb := hstep.2
              rw [hs] at hb
              simpa using hb

/-- The actual run stays in a configuration space whose description-size parameter is the
larger of the two supplied descriptions.  No agreement of tape counts, initial states, or table
shapes is assumed. -/
theorem runStructuredTables_invariant (p : Desc × (Desc × (List ℕ × Word))) :
    let df := p.1
    let dt := p.2.1
    let input := p.2.2.1
    let coins := p.2.2.2
    let D := max (descLen df) (descLen dt)
    let final := coins.foldl
      (fun c b => stepOut (if b then dt else df) input c) (init df, [])
    Inv D input.length coins.length final.1 ∧ final.2.length ≤ coins.length ∧
      (∀ o ∈ final.2, o ≤ D) := by
  let df := p.1
  let dt := p.2.1
  let input := p.2.2.1
  let coins := p.2.2.2
  let D := max (descLen df) (descLen dt)
  have hdf : descLen df ≤ D := Nat.le_max_left _ _
  have hdt : descLen dt ≤ D := Nat.le_max_right _ _
  have h := fold_inv df dt input coins D hdf hdt coins.length le_rfl
  have hfull :
      Inv D input.length coins.length
        (coins.foldl (fun c b => stepOut (if b then dt else df) input c) (init df, [])).1 ∧
      (coins.foldl (fun c b => stepOut (if b then dt else df) input c) (init df, [])).2.length ≤ coins.length ∧
      (∀ o ∈ (coins.foldl (fun c b => stepOut (if b then dt else df) input c) (init df, [])).2,
        o ≤ D) := by
    simpa [List.take_length] using h
  simpa [df, dt, input, coins, D] using hfull

/-- The output's unary encoding has size at most the number of supplied coins times the
unary-description symbol bound. This is the output-size part of the structured resource bound. -/
theorem runStructuredTables_encodedOutput_bound
    (p : Desc × (Desc × (List ℕ × Word))) :
    (encList encUnary (runStructuredTables p)).length ≤
      p.2.2.2.length * (2 * max (descLen p.1) (descLen p.2.1) + 1) := by
  let df := p.1
  let dt := p.2.1
  let input := p.2.2.1
  let coins := p.2.2.2
  let D := max (descLen df) (descLen dt)
  have hvalues := (runStructuredTables_invariant p).2.2
  have hlen := (runStructuredTables_invariant p).2.1
  have hlen' : (runStructuredTables p).length ≤ coins.length := by
    simpa [df, dt, input, coins, runStructuredTables] using hlen
  have henc : (encList encUnary (runStructuredTables p)).length ≤
      (runStructuredTables p).length * (2 * D + 1) :=
    length_encList_le encUnary (runStructuredTables p) (b := D) (by
      intro n hn
      have hn' : n ≤ D := by
        simpa [df, dt, input, coins, D, runStructuredTables] using hvalues n hn
      simpa [encUnary_apply, List.length_replicate] using hn')
  change (encList encUnary (runStructuredTables p)).length ≤ coins.length * (2 * D + 1)
  exact henc.trans (Nat.mul_le_mul_right _ hlen')

/-- The raw-machine wrapper is definitionally just the structured replay certified above. -/
theorem runTables_structured (m : RawFairMachine) (input : List ℕ) (coins : Word) :
    runTables m input coins =
      runStructuredTables
        (⟨⟨m.tapes, m.initial, m.falseTable⟩,
          ⟨⟨m.tapes, m.initial, m.trueTable⟩, (input, coins)⟩⟩) := rfl

/-- Every structured replay emits at most one symbol per supplied coin, and each emitted symbol
is bounded by the size of one of the two supplied descriptions. -/
theorem runTables_output_bound (m : RawFairMachine) (input : List ℕ) (coins : Word) :
    (runTables m input coins).length ≤ coins.length ∧
      (∀ o ∈ runTables m input coins, o ≤
        max (descLen ⟨m.tapes, m.initial, m.falseTable⟩)
            (descLen ⟨m.tapes, m.initial, m.trueTable⟩)) := by
  rw [runTables_structured]
  have h := runStructuredTables_invariant
    (⟨⟨m.tapes, m.initial, m.falseTable⟩,
      ⟨⟨m.tapes, m.initial, m.trueTable⟩, (input, coins)⟩⟩)
  rcases h with ⟨_, hlen, hout⟩
  constructor
  · simpa [runStructuredTables] using hlen
  · intro o ho
    have ho' : o ∈ (coins.foldl
        (fun c b => stepOut
          (if b then (⟨m.tapes, m.initial, m.trueTable⟩ : Desc)
            else ⟨m.tapes, m.initial, m.falseTable⟩) input c)
          (init ⟨m.tapes, m.initial, m.falseTable⟩, [])).2 := by
      simpa [runStructuredTables] using ho
    exact hout o ho'

/-- The input encoding used by the runtime certificate: two unrestricted descriptions, a unary
symbol list, and an explicit coin tape. -/
def eStructuredTables : Desc × (Desc × (List ℕ × Word)) ↪ Word :=
  encPair eDesc (encPair eDesc (encPair (encList encUnary) encBits))

end AverageCaseComplexity.Completeness.TwoQuery
