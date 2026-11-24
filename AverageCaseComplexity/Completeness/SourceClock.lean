module

public import Complexity.Computability.Probabilistic.PPT.Clock
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Closed

@[expose] public section

/-! # Intrinsically clocked realizations of efficient randomized programs

An `IsPPTOn` certificate normally exposes a cutoff run.  For source-machine
constructions it is useful to have a machine that has genuinely halted by a
polynomial bound: once halted, every larger `runClosed` budget has exactly the
same output law.  This packages the existing clock compiler and its halting
certificate into that stronger interface.
-/

namespace Cslib.Probability

open Cslib Turing.MultiTapePTM

/-- An efficient probabilistic program has a finite-control realization that
actually halts by a uniform polynomial bound, and whose closed output law is
unchanged at every larger instruction budget.  The law is stated in the
requested output encoding.  Halting is guaranteed even for raw words that are
not in the range of the input encoding. -/
theorem IsPPTOn.exists_intrinsically_clocked_machine
    {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {program : α → ProbComp β} (h : IsPPTOn input output program) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State)
      (machine : Turing.MultiTapePTM k Bool State) (c d : ℕ),
      (∀ a,
        (ProbComp.eval (program a)).map output =
          ProbComp.eval (machine.runClosed (c * ((input a).length + 1) ^ d) (input a))) ∧
      (∀ a larger, c * ((input a).length + 1) ^ d ≤ larger →
        ProbComp.eval (machine.runClosed larger (input a)) =
          (ProbComp.eval (program a)).map output) ∧
      (∀ word,
        ∀ final ∈ (ProbComp.eval (machine.runConfigFrom (ProbComp.uniform Bool)
          Empty.elim (c * (word.length + 1) ^ d) (machine.initialConfig word))).support,
          final.tapes.state = none) := by
  obtain ⟨k, State, hfinite, machine, c, d, hlaw, hhalt⟩ :=
    h.exists_halting_machine
  refine ⟨k, State, hfinite, machine, c, d, hlaw, ?_, hhalt⟩
  intro a larger hbound
  calc
    ProbComp.eval (machine.runClosed larger (input a)) =
        ProbComp.eval
          (machine.runClosed (c * ((input a).length + 1) ^ d) (input a)) :=
      Turing.MultiTapePTM.eval_runClosed_eq_of_halted machine (input a) hbound (hhalt (input a))
    _ = (ProbComp.eval (program a)).map output := (hlaw a).symm

end Cslib.Probability
