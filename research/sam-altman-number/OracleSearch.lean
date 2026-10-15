import «research».«sam-altman-number».OracleMachine
import «research».«sam-altman-number».FormulaSemantics

/-!
Actual oracle-search programs and finite encoding certificates.
The oracle specification is a predicate, never a supplied numerical boundary.
Connecting that predicate to intended-universe set truth remains separate work.
-/

set_option autoImplicit false

namespace SamAltman.OracleSearch

open OracleMachine

/-- Search using a program that converts the search input and trial number into
an oracle address. `find` supplies the address program with `Nat.pair input n`. -/
def searchWith (address : Program) : Program := .find (.comp .query address)

theorem mem_eval_searchWith (oracle : ℕ → ℕ) (address : Program)
    (input : ℕ) (addressFn : ℕ → ℕ)
    (haddress : ∀ n, eval oracle address (Nat.pair input n) = Part.some (addressFn n))
    (b : ℕ) :
    b ∈ eval oracle (searchWith address) input ↔
      oracle (addressFn b) = 0 ∧ ∀ n < b, oracle (addressFn n) ≠ 0 := by
  rw [searchWith, mem_eval_find]
  simp [haddress, eq_comm]

/-- The compiler needs only a predicate's correctness and its least witness.
It does not ask the oracle to return that witness. -/
theorem eval_searchWith_of_least (oracle : ℕ → ℕ) (address : Program)
    (input : ℕ) (addressFn : ℕ → ℕ) (P : ℕ → Prop) (b : ℕ)
    (haddress : ∀ n, eval oracle address (Nat.pair input n) = Part.some (addressFn n))
    (hcorrect : ∀ n, oracle (addressFn n) = 0 ↔ P n)
    (hb : P b) (hmin : ∀ n, P n → b ≤ n) :
    eval oracle (searchWith address) input = Part.some b := by
  apply Part.eq_some_iff.mpr
  apply (mem_eval_searchWith oracle address input addressFn haddress b).mpr
  refine ⟨(hcorrect b).mpr hb, fun n hn hzero => ?_⟩
  exact (Nat.not_le_of_lt hn) (hmin n ((hcorrect n).mp hzero))

/-- The direct two-parameter variant queries `oracle (Nat.pair input n)`. -/
def parameterSearch : Program := .find .query

theorem parameterSearch_code : encode parameterSearch = 14 := by decide

theorem mem_eval_parameterSearch (oracle : ℕ → ℕ) (input b : ℕ) :
    b ∈ eval oracle parameterSearch input ↔
      oracle (Nat.pair input b) = 0 ∧
        ∀ n < b, oracle (Nat.pair input n) ≠ 0 := by
  rw [parameterSearch, mem_eval_find]
  simp [eq_comm]

/-- Discard the parameter supplied by `find`, leaving the candidate natural. -/
def rightAddress : Program := .prim .right

@[simp] theorem eval_rightAddress (oracle : ℕ → ℕ) (n : ℕ) :
    eval oracle rightAddress n = Part.some n.unpair.2 := by
  simp [rightAddress, Nat.Partrec.Code.eval]

/-- A fixed program for searching a unary predicate oracle from blank input. -/
def fixedSearch : Program := searchWith rightAddress

theorem fixedSearch_code : encode fixedSearch = 36966 := by decide

theorem fixedSearch_code_lt : encode fixedSearch < 2 ^ 16 := by
  rw [fixedSearch_code]
  decide

theorem eval_fixedSearch_of_least (oracle : ℕ → ℕ) (P : ℕ → Prop) (b : ℕ)
    (hcorrect : ∀ n, oracle n = 0 ↔ P n)
    (hb : P b) (hmin : ∀ n, P n → b ≤ n) :
    eval oracle fixedSearch 0 = Part.some b := by
  apply eval_searchWith_of_least oracle rightAddress 0 id P b
  · intro n
    simp
  · exact hcorrect
  · exact hb
  · exact hmin

theorem least_lt_busyBeaverBits (oracle : ℕ → ℕ) (P : ℕ → Prop) (b : ℕ)
    (hcorrect : ∀ n, oracle n = 0 ↔ P n)
    (hb : P b) (hmin : ∀ n, P n → b ≤ n) :
    b < busyBeaverBits oracle 16 := by
  apply eval_lt_busyBeaverBits oracle 16 fixedSearch b fixedSearch_code_lt
  rw [eval_fixedSearch_of_least oracle P b hcorrect hb hmin]
  exact Part.mem_some _

/-- Attach a channel tag to each trial. This supports combining the predicate
oracle with independent truth or diagonal-halting channels. -/
def taggedAddress (tag : ℕ) : Program := .pair (constant tag) rightAddress

@[simp] theorem eval_taggedAddress (oracle : ℕ → ℕ) (tag n : ℕ) :
    eval oracle (taggedAddress tag) n = Part.some (Nat.pair tag n.unpair.2) := by
  change (Nat.pair <$> eval oracle (constant tag) n <*> eval oracle rightAddress n) = _
  rw [eval_constant, eval_rightAddress]
  simp [Seq.seq]

def taggedSearch (tag : ℕ) : Program := searchWith (taggedAddress tag)

theorem taggedSearch_zero_code : encode (taggedSearch 0) = 1360724646 := by decide

theorem taggedSearch_zero_code_lt : encode (taggedSearch 0) < 2 ^ 31 := by
  rw [taggedSearch_zero_code]
  decide

theorem eval_taggedSearch_of_least (oracle : ℕ → ℕ) (tag : ℕ)
    (P : ℕ → Prop) (b : ℕ)
    (hcorrect : ∀ n, oracle (Nat.pair tag n) = 0 ↔ P n)
    (hb : P b) (hmin : ∀ n, P n → b ≤ n) :
    eval oracle (taggedSearch tag) 0 = Part.some b := by
  apply eval_searchWith_of_least oracle (taggedAddress tag) 0 (Nat.pair tag) P b
  · intro n
    simp
  · exact hcorrect
  · exact hb
  · exact hmin

theorem tagged_least_lt_busyBeaverBits (oracle : ℕ → ℕ) (P : ℕ → Prop) (b : ℕ)
    (hcorrect : ∀ n, oracle (Nat.pair 0 n) = 0 ↔ P n)
    (hb : P b) (hmin : ∀ n, P n → b ≤ n) :
    b < busyBeaverBits oracle 31 := by
  apply eval_lt_busyBeaverBits oracle 31 (taggedSearch 0) b taggedSearch_zero_code_lt
  rw [eval_taggedSearch_of_least oracle 0 P b hcorrect hb hmin]
  exact Part.mem_some _

open SamAltmanResearch

universe u

/-- A cutoff query expressed directly through compositional formula semantics.
Its definition does not mention `Formula.boundary` or any Rayo value. -/
def BelowDescriptions {α : Type u} (mem : α → α → Prop) (nat : ℕ → α)
    (budget n : ℕ) : Prop :=
  ∀ p : Formula 1, p.symbols < budget → ∀ m : ℕ, Formula.Denotes mem nat p m → m < n

theorem belowDescriptions_boundary {α : Type u} (mem : α → α → Prop)
    (nat : ℕ → α) (hnat : Function.Injective nat) (budget : ℕ) :
    BelowDescriptions mem nat budget (Formula.boundary mem nat budget) := by
  intro p hp m hm
  exact Formula.denotes_lt_boundary hnat hp hm

theorem boundary_le_of_belowDescriptions {α : Type u} (mem : α → α → Prop)
    (nat : ℕ → α) (hnat : Function.Injective nat) (budget n : ℕ)
    (h : BelowDescriptions mem nat budget n) : Formula.boundary mem nat budget ≤ n := by
  apply Formula.boundary_le
  intro m hm
  obtain ⟨p, hp, hpm⟩ := (Formula.mem_values hnat).mp hm
  exact h p hp m hpm

/-- This semantic oracle is defined for arbitrary type-sized structures.
It is not identified here with truth in the intended universe of all sets. -/
noncomputable def descriptionOracle {α : Type u} (mem : α → α → Prop)
    (nat : ℕ → α) (budget n : ℕ) : ℕ := by
  classical
  exact if BelowDescriptions mem nat budget n then 0 else 1

theorem descriptionOracle_eq_zero {α : Type u} (mem : α → α → Prop)
    (nat : ℕ → α) (budget n : ℕ) :
    descriptionOracle mem nat budget n = 0 ↔ BelowDescriptions mem nat budget n := by
  classical
  simp [descriptionOracle]

theorem eval_fixedSearch_descriptionOracle {α : Type u} (mem : α → α → Prop)
    (nat : ℕ → α) (hnat : Function.Injective nat) (budget : ℕ) :
    eval (descriptionOracle mem nat budget) fixedSearch 0 =
      Part.some (Formula.boundary mem nat budget) :=
  eval_fixedSearch_of_least (descriptionOracle mem nat budget)
    (BelowDescriptions mem nat budget) (Formula.boundary mem nat budget)
    (descriptionOracle_eq_zero mem nat budget)
    (belowDescriptions_boundary mem nat hnat budget)
    (boundary_le_of_belowDescriptions mem nat hnat budget)

/-- A proved relative comparison with an actual 16-bit witness. The intended
universe interpretation and its object-language oracle are not supplied here. -/
theorem description_boundary_lt_busyBeaverBits {α : Type u} (mem : α → α → Prop)
    (nat : ℕ → α) (hnat : Function.Injective nat) (budget : ℕ) :
    Formula.boundary mem nat budget < busyBeaverBits (descriptionOracle mem nat budget) 16 :=
  least_lt_busyBeaverBits (descriptionOracle mem nat budget)
    (BelowDescriptions mem nat budget) (Formula.boundary mem nat budget)
    (descriptionOracle_eq_zero mem nat budget)
    (belowDescriptions_boundary mem nat hnat budget)
    (boundary_le_of_belowDescriptions mem nat hnat budget)

#print axioms mem_eval_searchWith
#print axioms eval_searchWith_of_least
#print axioms fixedSearch_code_lt
#print axioms least_lt_busyBeaverBits
#print axioms taggedSearch_zero_code_lt
#print axioms tagged_least_lt_busyBeaverBits
#print axioms eval_fixedSearch_descriptionOracle
#print axioms description_boundary_lt_busyBeaverBits

end SamAltman.OracleSearch
