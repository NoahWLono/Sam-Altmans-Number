import «research».«sam-altman-number».BoundedTruth
import «research».«sam-altman-number».NaturalFormula
import «research».«sam-altman-number».OracleSearch

/-!
A fully specified bounded formula oracle. Channel zero is the literal finite
upper-bound formula; the other channels query the eligible formulas themselves.
The intended-universe interpretation is not identified with ZFSet here.
-/

set_option autoImplicit false

namespace SamAltmanResearch.FormulaOracle

open Formula
open SamAltman.OracleMachine SamAltman.OracleSearch

/-- No added truth symbol: every selected query is pure first-order syntax.
An out-of-range selector receives the always-false formula. -/
def queryFormula (budget : Nat) (natural : Formula 1) : Nat → Formula 1
  | 0 => upperBound budget natural
  | i + 1 => ((descriptionList budget)[i]?).getD (.neg (.equal 0 0))

universe u

/-- The zero convention agrees with the minimization instruction. The input
is a pair of a finite-formula selector and a natural parameter. -/
noncomputable def oracle {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (budget : Nat) (natural : Formula 1) (input : Nat) : Nat := by
  classical
  exact if Sat mem (queryFormula budget natural input.unpair.1)
      (fun _ => nat input.unpair.2) then 0 else 1

theorem oracle_pair_eq_zero {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (budget : Nat) (natural : Formula 1) (i n : Nat) :
    oracle mem nat budget natural (Nat.pair i n) = 0 ↔
      Sat mem (queryFormula budget natural i) (fun _ => nat n) := by
  classical
  simp [oracle]

theorem oracle_cutoff {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) (natural : Formula 1)
    (hnatural : ∀ x, Sat mem natural (fun _ => x) ↔ ∃ n, x = nat n)
    (hmem : ∀ m n, mem (nat m) (nat n) ↔ m < n) (budget b : Nat) :
    oracle mem nat budget natural (Nat.pair 0 b) = 0 ↔
      boundary mem nat budget ≤ b := by
  rw [oracle_pair_eq_zero]
  exact sat_upperBound_iff_boundary_le mem nat hnat natural hnatural hmem budget b

theorem compiled_search_output {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) (natural : Formula 1)
    (hnatural : ∀ x, Sat mem natural (fun _ => x) ↔ ∃ n, x = nat n)
    (hmem : ∀ m n, mem (nat m) (nat n) ↔ m < n) (budget : Nat) :
    eval (oracle mem nat budget natural) (taggedSearch 0) 0 =
      Part.some (boundary mem nat budget) := by
  apply eval_taggedSearch_of_least _ 0 (fun n => boundary mem nat budget ≤ n)
  · exact oracle_cutoff mem nat hnat natural hnatural hmem budget
  · exact le_rfl
  · exact fun _ h => h

theorem boundary_lt_compiled_oracle_bound {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) (natural : Formula 1)
    (hnatural : ∀ x, Sat mem natural (fun _ => x) ↔ ∃ n, x = nat n)
    (hmem : ∀ m n, mem (nat m) (nat n) ↔ m < n) (budget : Nat) :
    boundary mem nat budget < busyBeaverBits (oracle mem nat budget natural) 31 := by
  apply tagged_least_lt_busyBeaverBits _ (fun n => boundary mem nat budget ≤ n)
  · exact oracle_cutoff mem nat hnat natural hnatural hmem budget
  · exact le_rfl
  · exact fun _ h => h

/-- Model instance used to check the entire concrete syntax/oracle/program
chain. It is not a declaration of the original intended-universe Rayo value. -/
noncomputable def modelOracle (budget : Nat) : Nat → Nat :=
  oracle (α := ZFSet.{u}) (· ∈ ·) NaturalFormula.nat budget NaturalFormula.natFormula

theorem model_boundary_lt (budget : Nat) :
    boundary (α := ZFSet.{u}) (· ∈ ·) NaturalFormula.nat budget <
      busyBeaverBits (modelOracle.{u} budget) 31 :=
  boundary_lt_compiled_oracle_bound _ _ NaturalFormula.nat_injective
    NaturalFormula.natFormula NaturalFormula.sat_natFormula
    NaturalFormula.mem_nat_iff budget

#print axioms oracle_pair_eq_zero
#print axioms oracle_cutoff
#print axioms compiled_search_output
#print axioms boundary_lt_compiled_oracle_bound
#print axioms model_boundary_lt

end SamAltmanResearch.FormulaOracle
