module

public import AverageCaseComplexity.Completeness.FairReplay
public import AverageCaseComplexity.Completeness.VoteRuntime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import Mathlib.Data.Nat.Size

@[expose] public section

/-! # Tidy exhaustive coin enumeration for exact voting

The exponential work is represented by a list whose encoded size is charged to
unary accuracy.  In particular, we never compute a unary `2^m` before checking
that `m < k.size`.
-/

namespace AverageCaseComplexity.Completeness.TwoQuery

open Turing.MultiTapeTM

/-- One doubling stage: prepend either possible next coin to every old tape. -/
def coinWordsStep (ws : List Word) : List Word :=
  ws.map (fun w => false :: w) ++ ws.map (fun w => true :: w)

/-- Generate all length-`m` coin words by iterated doubling. -/
def coinWords (m : ℕ) : List Word :=
  coinWordsStep^[m] [[]]

private theorem coinWordsStep_length (ws : List Word) :
    (coinWordsStep ws).length = 2 * ws.length := by
  simp [coinWordsStep, List.length_append]
  omega

private theorem coinWordsStep_mem_length (ws : List Word) (n : ℕ)
    (h : ∀ w ∈ ws, w.length = n) :
    ∀ w ∈ coinWordsStep ws, w.length = n + 1 := by
  intro w hw
  simp only [coinWordsStep, List.mem_append, List.mem_map] at hw
  rcases hw with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;>
    simp [h v hv]

private theorem coinWords_invariant (m : ℕ) :
    (coinWords m).length = 2 ^ m ∧ ∀ w ∈ coinWords m, w.length = m := by
  induction m with
  | zero => simp [coinWords]
  | succ m ih =>
      constructor
      · change (coinWordsStep^[m + 1] [[]]).length = 2 ^ (m + 1)
        rw [Function.iterate_succ_apply']
        change (coinWordsStep (coinWords m)).length = 2 ^ (m + 1)
        rw [coinWordsStep_length, ih.1]
        simp [pow_succ]
        omega
      · change ∀ w ∈ (coinWordsStep^[m + 1] [[]]), w.length = m + 1
        rw [Function.iterate_succ_apply']
        change ∀ w ∈ coinWordsStep (coinWords m), w.length = m + 1
        exact coinWordsStep_mem_length (coinWords m) m ih.2

/-- The guarded loop count.  This is polynomial-time computable even when the
binary exponent would otherwise specify an enormous unary iteration. -/
def guardedCoinCount (m k : ℕ) : ℕ := if m < k.size then m else 0

private theorem pow_guardedCoinCount_le (m k i : ℕ)
    (hi : i ≤ guardedCoinCount m k) : 2 ^ i ≤ k + 1 := by
  unfold guardedCoinCount at hi
  split at hi
  · rename_i h
    have hm : 2 ^ m ≤ k := Nat.lt_size.1 h
    have hie : i ≤ m := hi
    exact (Nat.pow_le_pow_right (by omega : 0 < 2) hie).trans (by omega)
  · have hz : i = 0 := by omega
    subst i
    change 1 ≤ k + 1
    omega

/-- The list of all guarded coin words has polynomial encoded size.  Its
intermediate loop states satisfy the same bound, so the doubling loop itself
has a tidy polynomial-time certificate. -/
theorem guardedCoinWords_efficient :
    ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ => coinWords (guardedCoinCount p.1 p.2))
      (encPair encUnary encUnary) (encList encBits) := by
  have hcount : ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ => guardedCoinCount p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
    have hb : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.2.bits)
        (encPair encUnary encUnary) encBits :=
      (ComputableTidilyInPolyTime.unary_to_binary.comp
        (ComputableTidilyInPolyTime.snd encUnary encUnary)).of_enc_eq
          (fun p => by simp [encNat_apply])
    have hs : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.2.size)
        (encPair encUnary encUnary) encUnary :=
      (ComputableTidilyInPolyTime.length_bits.comp hb).of_enc_eq
        (fun p => by simp [Nat.size_eq_bits_len])
    have hlt := ComputableTidilyInPolyTime.unary_lt'
      (ComputableTidilyInPolyTime.fst encUnary encUnary) hs
    exact hlt.ite_decide (ComputableTidilyInPolyTime.fst encUnary encUnary)
      (ComputableTidilyInPolyTime.const 0)
  have hstep : ComputableTidilyInPolyTime coinWordsStep (encList encBits) (encList encBits) := by
    unfold coinWordsStep
    fun_prop
  have hloop := ComputableTidilyInPolyTime.iterate_spec hcount
      (ComputableTidilyInPolyTime.const [[]]) hstep
      (fun p i ws => ws.length = 2 ^ i ∧ ∀ w ∈ ws, w.length = i)
      (by intro p; simp)
      (by
        intro p i ws hi hws
        constructor
        · change (coinWordsStep ws).length = 2 ^ (i + 1)
          rw [coinWordsStep_length, hws.1]
          simp [pow_succ]
          omega
        · exact coinWordsStep_mem_length ws i hws.2)
      (size := fun n => 3 * (n + 1) ^ 2)
      (by fun_prop)
      (by
        intro p i ws hi hws
        have hm : p.1 ≤ (encPair encUnary encUnary p).length := by
          rw [length_encPair, encUnary_apply, encUnary_apply,
            List.length_replicate, List.length_replicate]
          omega
        have hk : p.2 ≤ (encPair encUnary encUnary p).length := by
          rw [length_encPair, encUnary_apply, encUnary_apply,
            List.length_replicate, List.length_replicate]
          omega
        have hi' : i ≤ guardedCoinCount p.1 p.2 := hi
        have hi_m : i ≤ p.1 := by
          unfold guardedCoinCount at hi'
          split at hi' <;> omega
        have hp : 2 ^ i ≤ p.2 + 1 := pow_guardedCoinCount_le p.1 p.2 i hi'
        have hwlen : ∀ w ∈ ws, w.length = i := hws.2
        calc
          (encList encBits ws).length ≤ ws.length * (2 * i + 1) :=
            length_encList_le encBits ws (fun w hw => by simp [encBits_apply, hwlen w hw])
          _ = 2 ^ i * (2 * i + 1) := by rw [hws.1]
          _ ≤ (p.2 + 1) * (2 * p.1 + 1) := by
            exact Nat.mul_le_mul hp (by omega)
          _ ≤ 3 * ((encPair encUnary encUnary p).length + 1) ^ 2 := by
            nlinarith [hm, hk, show 0 ≤ p.1 from Nat.zero_le p.1,
              show 0 ≤ p.2 from Nat.zero_le p.2])
  simpa only [Function.iterate_succ_apply', guardedCoinCount, coinWords] using
    hloop.1

/-- The guarded exponent is always small enough for exact enumeration; if the
size test fails, the loop uses zero stages and does not enumerate an exponential
number of tapes. -/
theorem guardedCoinWords_count_bound (m k : ℕ) :
    (coinWords (guardedCoinCount m k)).length ≤ k + 1 := by
  rw [(coinWords_invariant _).1]
  exact pow_guardedCoinCount_le m k (guardedCoinCount m k) le_rfl


/-- Vote from an explicitly enumerated outcome list. The total number of
trials is taken from the list itself, avoiding an exponential unary `2^m`.
The give-up threshold and Boolean tie-break agree with `exactReplayBit` when
the list contains exactly one outcome per coin tape. -/
def exactVoteFromAnswers (answers : List Answer) (fallback : Bool) : Bool :=
  if answers.length ≤ 4 * answers.count none then fallback
  else decide (answers.count (some false) < answers.count (some true))

theorem exactVoteFromAnswers_efficient :
    ComputableTidilyInPolyTime
      (fun p : List Answer × Bool => exactVoteFromAnswers p.1 p.2)
      (encPair (encList answerEncoding) encBool) encBool := by
  have hlen : ComputableTidilyInPolyTime (fun p : List Answer × Bool => p.1.length)
      (encPair (encList answerEncoding) encBool) encUnary :=
    (ComputableTidilyInPolyTime.length answerEncoding).comp
      (ComputableTidilyInPolyTime.fst (encList answerEncoding) encBool)
  have hnone : ComputableTidilyInPolyTime
      (fun p : List Answer × Bool => 4 * AverageCaseComplexity.answerCount none p.1)
      (encPair (encList answerEncoding) encBool) encUnary := by
    fun_prop
  have htest := ComputableTidilyInPolyTime.unary_le' hlen hnone
  have hf : ComputableTidilyInPolyTime
      (fun p : List Answer × Bool => AverageCaseComplexity.answerCount (some false) p.1)
      (encPair (encList answerEncoding) encBool) encUnary :=
    (answerCount_computable (some false)).comp
      (ComputableTidilyInPolyTime.fst (encList answerEncoding) encBool)
  have ht : ComputableTidilyInPolyTime
      (fun p : List Answer × Bool => AverageCaseComplexity.answerCount (some true) p.1)
      (encPair (encList answerEncoding) encBool) encUnary :=
    (answerCount_computable (some true)).comp
      (ComputableTidilyInPolyTime.fst (encList answerEncoding) encBool)
  have hcmp := ComputableTidilyInPolyTime.unary_lt' hf ht
  exact htest.ite_decide
    (ComputableTidilyInPolyTime.snd (encList answerEncoding) encBool) hcmp

/-- The answer list obtained by replaying the input-dependent deterministic
computation on every guarded coin tape. -/
def enumeratedAnswers {α : Type} (steps k : α → ℕ)
    (replay : α × Word → Answer) (a : α) : List Answer :=
  (coinWords (guardedCoinCount (steps a) (k a))).map (fun coins => replay (a, coins))

theorem enumeratedAnswers_efficient {α : Type} {input : α ↪ Word}
    {steps k : α → ℕ} {replay : α × Word → Answer}
    (hsteps : ComputableTidilyInPolyTime steps input encUnary)
    (hk : ComputableTidilyInPolyTime k input encUnary)
    (hreplay : ComputableTidilyInPolyTime replay (encPair input encBits) answerEncoding) :
    ComputableTidilyInPolyTime (enumeratedAnswers steps k replay)
      input (encList answerEncoding) := by
  have hmeta : ComputableTidilyInPolyTime (fun a => (steps a, k a)) input
      (encPair encUnary encUnary) := hsteps.prod hk
  have hwords : ComputableTidilyInPolyTime
      (fun a => coinWords (guardedCoinCount (steps a) (k a))) input (encList encBits) :=
    guardedCoinWords_efficient.comp hmeta
  exact ComputableTidilyInPolyTime.mapWithInput hwords hreplay

/-- Guard an exact exhaustive vote by `steps < k.size`. In the false branch
we return the supplied fallback without attempting exponential enumeration. -/
def guardedExactVote {α : Type} (steps k : α → ℕ) (fallback : α → Bool)
    (replay : α × Word → Answer) (a : α) : Bool :=
  if steps a < (k a).size then
    exactVoteFromAnswers (enumeratedAnswers steps k replay a) (fallback a)
  else fallback a

private theorem exactBranchGuard_efficient {α : Type} {input : α ↪ Word}
    {steps k : α → ℕ}
    (hsteps : ComputableTidilyInPolyTime steps input encUnary)
    (hk : ComputableTidilyInPolyTime k input encUnary) :
    ComputableTidilyInPolyTime (fun a => decide (steps a < (k a).size)) input encBool := by
  have hbits : ComputableTidilyInPolyTime (fun a => (k a).bits) input encBits :=
    (ComputableTidilyInPolyTime.unary_to_binary.comp hk).of_enc_eq
      (fun a => by simp [encNat_apply])
  have hsize : ComputableTidilyInPolyTime (fun a => (k a).size) input encUnary :=
    (ComputableTidilyInPolyTime.length_bits.comp hbits).of_enc_eq
      (fun a => by simp [Nat.size_eq_bits_len])
  simpa only [Nat.size_eq_bits_len] using
    ComputableTidilyInPolyTime.unary_lt' hsteps hsize

theorem guardedExactVote_efficient {α : Type} {input : α ↪ Word}
    {steps k : α → ℕ} {fallback : α → Bool} {replay : α × Word → Answer}
    (hsteps : ComputableTidilyInPolyTime steps input encUnary)
    (hk : ComputableTidilyInPolyTime k input encUnary)
    (hfallback : ComputableTidilyInPolyTime fallback input encBool)
    (hreplay : ComputableTidilyInPolyTime replay (encPair input encBits) answerEncoding) :
    ComputableTidilyInPolyTime (guardedExactVote steps k fallback replay) input encBool := by
  have hanswers := enumeratedAnswers_efficient hsteps hk hreplay
  have hvote : ComputableTidilyInPolyTime
      (fun a => exactVoteFromAnswers (enumeratedAnswers steps k replay a) (fallback a))
      input encBool := by
    exact exactVoteFromAnswers_efficient.comp (hanswers.prod hfallback)
  exact (exactBranchGuard_efficient hsteps hk).ite_decide hvote hfallback

private theorem coinWords_nodup (n : ℕ) : (coinWords n).Nodup := by
  induction n with
  | zero => simp [coinWords]
  | succ n ih =>
    change (coinWordsStep^[n+1] [[]]).Nodup
    rw [Function.iterate_succ_apply', coinWordsStep, List.nodup_append]
    refine ⟨ih.map (by simp [Function.Injective]), ih.map (by simp [Function.Injective]), ?_⟩
    simp

private theorem mem_coinWords_self (w : Word) : w ∈ coinWords w.length := by
  induction w with
  | nil => simp [coinWords]
  | cons b w ih =>
    change _ ∈ coinWordsStep^[w.length+1] [[]]
    rw [Function.iterate_succ_apply', coinWordsStep, List.mem_append]
    cases b
    · exact Or.inl (List.mem_map.mpr ⟨w, ih, rfl⟩)
    · exact Or.inr (List.mem_map.mpr ⟨w, ih, rfl⟩)

/-- The doubling enumeration contains each fixed-length tape exactly once. -/
theorem coinWords_count (run : Word → Answer) (steps : ℕ) (a : Answer) :
    ((coinWords steps).map run).count a = replayCount run steps a := by
  let U := (Finset.univ : Finset (FixedWord steps))
  have he : (↑(coinWords steps) : Multiset Word) = U.val.map List.ofFn := by
    apply (Multiset.Nodup.ext (Multiset.coe_nodup.mpr (coinWords_nodup steps)) (U.nodup.map List.ofFn_injective)).mpr
    intro w
    constructor
    · intro hw
      have hlen := (coinWords_invariant steps).2 w hw
      subst steps
      exact Multiset.mem_map.mpr ⟨w.get, Finset.mem_univ _, List.ofFn_get _⟩
    · intro hw
      obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hw
      simpa using mem_coinWords_self (List.ofFn v)
  calc
    _ = Multiset.count a (Multiset.map run ↑(coinWords steps)) := by
      rw [Multiset.map_coe, Multiset.coe_count]
      simp only [List.count_eq_length_filter, beq_eq_decide]
    _ = _ := by
      rw [he, Multiset.map_map, Multiset.count_map]
      simp only [replayCount, Finset.card, Finset.filter_val, U, Function.comp_apply, eq_comm]

/-- Semantic connection to the finite replay counts. -/
theorem exactVoteFromAnswers_eq_exactReplayBit
    (run : Word → Answer) (steps : ℕ) (fallback : Bool) :
    exactVoteFromAnswers ((coinWords steps).map run) fallback =
      exactReplayBit run steps fallback := by
  unfold exactVoteFromAnswers exactReplayBit
  rw [List.length_map, coinWords_invariant steps |>.1, coinWords_count, coinWords_count, coinWords_count]

/-- On the exact branch, the guarded executable vote therefore agrees with the
mathematical replay-bit specification. -/
theorem guardedExactVote_eq_guardedReplayBit {α : Type}
    (steps k : α → ℕ) (fallback : α → Bool) (replay : α × Word → Answer) (a : α) :
    guardedExactVote steps k fallback replay a =
      if steps a < (k a).size then
        exactReplayBit (fun coins => replay (a, coins)) (steps a) (fallback a)
      else fallback a := by
  unfold guardedExactVote
  split
  · rename_i h
    have hm : guardedCoinCount (steps a) (k a) = steps a := by
      simp [guardedCoinCount, h]
    rw [enumeratedAnswers, hm]
    exact exactVoteFromAnswers_eq_exactReplayBit _ _ _
  · rfl

end AverageCaseComplexity.Completeness.TwoQuery
