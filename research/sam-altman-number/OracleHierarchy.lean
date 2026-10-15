import «research».«sam-altman-number».OracleMachine
import «research».«sam-altman-number».OracleSearch

/-!
Finite self-halting iteration and its omega-indexed join for the explicitly
encoded oracle language. No identification with an external Turing-machine
model or the intended universe of set theory is asserted.
-/

set_option autoImplicit false

namespace SamAltman.OracleHierarchy

open OracleMachine

/-- Iterate the diagonal halting operation for this oracle-program language. -/
noncomputable def jumpIter (base : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => base
  | k + 1 => selfHalting (jumpIter base k)

@[simp] theorem jumpIter_zero (base : ℕ → ℕ) : jumpIter base 0 = base := rfl

@[simp] theorem jumpIter_succ (base : ℕ → ℕ) (k : ℕ) :
    jumpIter base (k + 1) = selfHalting (jumpIter base k) := rfl

/-- The tagged join retains every finite stage, including the original base. -/
noncomputable def join (base : ℕ → ℕ) (address : ℕ) : ℕ :=
  jumpIter base address.unpair.1 address.unpair.2

@[simp] theorem join_pair (base : ℕ → ℕ) (k n : ℕ) :
    join base (Nat.pair k n) = jumpIter base k n := by
  simp [join]

@[simp] theorem join_zero_channel (base : ℕ → ℕ) (n : ℕ) :
    join base (Nat.pair 0 n) = base n := by simp

/-- Exact total-function computability in the concrete program language. -/
def Computes (oracle f : ℕ → ℕ) : Prop :=
  ∃ p : Program, ∀ n : ℕ, eval oracle p n = Part.some (f n)

/-- The diagonal theorem applies at every finite stage without extra assumptions. -/
theorem not_computes_successor (base : ℕ → ℕ) (k : ℕ) :
    ¬ Computes (jumpIter base k) (jumpIter base (k + 1)) := by
  exact no_selfHalting_program (jumpIter base k)

/-- Ordinary input transformation used to select a fixed join channel. -/
def channelInput (k : ℕ) : Program := .pair (constant k) (.prim .id)

@[simp] theorem eval_channelInput (oracle : ℕ → ℕ) (k n : ℕ) :
    eval oracle (channelInput k) n = Part.some (Nat.pair k n) := by
  simp [channelInput, eval, constant, Seq.seq]

/-- Run a program on inputs tagged with a fixed channel number. -/
def restrictChannel (p : Program) (k : ℕ) : Program := .comp p (channelInput k)

@[simp] theorem eval_restrictChannel (oracle : ℕ → ℕ) (p : Program) (k n : ℕ) :
    eval oracle (restrictChannel p k) n = eval oracle p (Nat.pair k n) := by
  simp [restrictChannel]

/-- Every finite stage is explicitly computable from the join oracle. -/
theorem computes_stage_from_join (base : ℕ → ℕ) (k : ℕ) :
    Computes (join base) (jumpIter base k) := by
  refine ⟨restrictChannel .query k, fun n => ?_⟩
  simp

/-- Channel restriction turns a join computation into any stage computation. -/
theorem computes_stage_of_computes_join (oracle base : ℕ → ℕ) (k : ℕ)
    (h : Computes oracle (join base)) : Computes oracle (jumpIter base k) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨restrictChannel p k, fun n => ?_⟩
  simp [hp]

/-- No finite stage computes the whole join: its next channel is diagonal. -/
theorem not_computes_join (base : ℕ → ℕ) (k : ℕ) :
    ¬ Computes (jumpIter base k) (join base) := by
  intro h
  exact not_computes_successor base k
    (computes_stage_of_computes_join (jumpIter base k) base (k + 1) h)

/-- The join cannot equal any of its finite-stage oracles. -/
theorem join_ne_stage (base : ℕ → ℕ) (k : ℕ) : join base ≠ jumpIter base k := by
  intro h
  apply not_computes_join base k
  refine ⟨.query, fun n => ?_⟩
  simp [h]

/-- The actual channel-zero search program returns the least base-predicate witness. -/
theorem eval_search_join_of_least (base : ℕ → ℕ) (P : ℕ → Prop) (b : ℕ)
    (hcorrect : ∀ n, base n = 0 ↔ P n)
    (hb : P b) (hmin : ∀ n, P n → b ≤ n) :
    eval (join base) (OracleSearch.taggedSearch 0) 0 = Part.some b := by
  apply OracleSearch.eval_taggedSearch_of_least (join base) 0 P b
  · simpa using hcorrect
  · exact hb
  · exact hmin

/-- A 31-bit executable witness gives the strict relative comparison. -/
theorem least_lt_join_busyBeaverBits (base : ℕ → ℕ) (P : ℕ → Prop) (b : ℕ)
    (hcorrect : ∀ n, base n = 0 ↔ P n)
    (hb : P b) (hmin : ∀ n, P n → b ≤ n) :
    b < busyBeaverBits (join base) 31 := by
  apply OracleSearch.tagged_least_lt_busyBeaverBits (join base) P b
  · simpa using hcorrect
  · exact hb
  · exact hmin

#print axioms jumpIter_succ
#print axioms join_zero_channel
#print axioms not_computes_successor
#print axioms eval_restrictChannel
#print axioms computes_stage_from_join
#print axioms not_computes_join
#print axioms join_ne_stage
#print axioms eval_search_join_of_least
#print axioms least_lt_join_busyBeaverBits

end SamAltman.OracleHierarchy
