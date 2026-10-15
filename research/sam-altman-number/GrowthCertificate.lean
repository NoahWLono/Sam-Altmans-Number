import «research».«sam-altman-number».ProfileSupport

/-!
A concrete program amplifies the comparison witness exponentially. Its
ordinary arithmetic code, partial evaluation, and finite encoding budget are
proved explicitly. The final comparison remains universal in the profile.
-/

set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option backward.isDefEq.respectTransparency false

namespace SamAltmanResearch.GrowthCertificate

open SamAltman.OracleMachine
open Nat.Partrec

/-- Add the two components of the paired input by primitive recursion. -/
def addition : Code := .prec .id (.comp .succ (.comp .right .right))

theorem eval_addition (a n : Nat) :
    Code.eval addition (Nat.pair a n) = Part.some (a + n) := by
  induction n with
  | zero => simp [addition]
  | succ n ih =>
      rw [addition, Code.eval_prec_succ]
      change (Code.eval addition (Nat.pair a n) >>= _) = _
      rw [ih]
      simp [Code.eval, Nat.add_assoc]

/-- Duplicate the input and add the copies. -/
def doubling : Code := .comp addition (.pair .id .id)

theorem eval_doubling (n : Nat) : Code.eval doubling n = Part.some (2 * n) := by
  simp [doubling, Code.eval, Seq.seq, eval_addition, two_mul]

def pow2Rec : Code := .prec (.const 1) (.comp doubling (.comp .right .right))

theorem eval_pow2Rec (a n : Nat) :
    Code.eval pow2Rec (Nat.pair a n) = Part.some (2 ^ n) := by
  induction n with
  | zero => simp [pow2Rec]
  | succ n ih =>
      rw [pow2Rec, Code.eval_prec_succ]
      change (Code.eval pow2Rec (Nat.pair a n) >>= _) = _
      rw [ih]
      simp [Code.eval, eval_doubling, Nat.pow_succ, Nat.mul_comm]

/-- Turn unary input into the recursion pair; the first component is unused. -/
def pow2 : Code := .comp pow2Rec (.pair (.const 0) .id)

theorem eval_pow2 (n : Nat) : Code.eval pow2 n = Part.some (2 ^ n) := by
  simp [pow2, Code.eval, Seq.seq, eval_pow2Rec]

/-- Search for the finite naming boundary, then compute two to that power. -/
def witness : Program := .comp (.prim pow2) Candidate.witness

set_option maxRecDepth 10000 in
theorem witness_code_lt : encode witness < 2 ^ 2048 := by decide

theorem witness_output (T : FiniteProfile.Profile) (budget : Nat) :
    eval (FiniteProfile.oracle T budget) witness 0 =
      Part.some (2 ^ FiniteProfile.boundary T budget) := by
  simp [witness, FiniteProfile.witness_output, eval_pow2]

theorem exponential_boundary_lt_number (T : FiniteProfile.Profile)
    (budget bits : Nat) (hbits : 2048 ≤ bits) :
    2 ^ FiniteProfile.boundary T budget < FiniteProfile.number T budget bits := by
  apply eval_lt_busyBeaverBits _ bits witness _
  · exact lt_of_lt_of_le witness_code_lt (Nat.pow_le_pow_right (by decide) hbits)
  · rw [witness_output]
    exact Part.mem_some _

theorem googol_ge_2048 : 2048 ≤ Candidate.googol := by norm_num [Candidate.googol]

/-- Exponential amplification is certified at the already fixed googol budget. -/
theorem exponential_boundary_lt_samAltman (T : FiniteProfile.Profile) :
    2 ^ FiniteProfile.boundary (FiniteProfile.restrict T Candidate.googol)
      Candidate.googol < FiniteProfile.samAltman T :=
  exponential_boundary_lt_number (FiniteProfile.restrict T Candidate.googol)
    Candidate.googol Candidate.googol googol_ge_2048

#print axioms eval_addition
#print axioms eval_doubling
#print axioms eval_pow2
#print axioms witness_code_lt
#print axioms witness_output
#print axioms exponential_boundary_lt_samAltman

end SamAltmanResearch.GrowthCertificate
