import «research».«sam-altman-number».FormulaOracle
import «research».«sam-altman-number».OracleHierarchy

/-!
The concrete candidate and its complete model-relative comparison. The
proper-class/object-language certificate for original Rayo remains separate.
-/

set_option autoImplicit false

namespace SamAltmanResearch.Candidate

open Formula
open SamAltman.OracleMachine SamAltman.OracleSearch SamAltman.OracleHierarchy

/-- Select channel zero of the hierarchy, then channel zero of its formula base. -/
def witnessAddress : Program := .pair (constant 0) (taggedAddress 0)

@[simp] theorem eval_witnessAddress (oracle : Nat → Nat) (n : Nat) :
    eval oracle witnessAddress n = Part.some (Nat.pair 0 (Nat.pair 0 n.unpair.2)) := by
  change (Nat.pair <$> eval oracle (constant 0) n <*> eval oracle (taggedAddress 0) n) = _
  rw [eval_constant, eval_taggedAddress]
  simp [Seq.seq]

def witness : Program := searchWith witnessAddress

theorem witness_code : encode witness = 1851571349958786726 := by decide

theorem witness_code_lt : encode witness < 2 ^ 61 := by
  rw [witness_code]
  decide

universe u

noncomputable def hierarchy {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (budget : Nat) (natural : Formula 1) : Nat → Nat :=
  join (FormulaOracle.oracle mem nat budget natural)

theorem eval_witness {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) (natural : Formula 1)
    (hnatural : ∀ x, Sat mem natural (fun _ => x) ↔ ∃ n, x = nat n)
    (hmem : ∀ m n, mem (nat m) (nat n) ↔ m < n) (budget : Nat) :
    eval (hierarchy mem nat budget natural) witness 0 =
      Part.some (boundary mem nat budget) := by
  apply eval_searchWith_of_least _ witnessAddress 0
    (fun n => Nat.pair 0 (Nat.pair 0 n)) (fun n => boundary mem nat budget ≤ n)
  · intro n
    simp
  · intro n
    simp only [hierarchy, join_zero_channel]
    exact FormulaOracle.oracle_cutoff mem nat hnat natural hnatural hmem budget n
  · exact le_rfl
  · exact fun _ h => h

noncomputable def number {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (budget bits : Nat) (natural : Formula 1) : Nat :=
  busyBeaverBits (hierarchy mem nat budget natural) bits

theorem boundary_lt_number {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) (natural : Formula 1)
    (hnatural : ∀ x, Sat mem natural (fun _ => x) ↔ ∃ n, x = nat n)
    (hmem : ∀ m n, mem (nat m) (nat n) ↔ m < n)
    (budget bits : Nat) (hbits : 61 ≤ bits) :
    boundary mem nat budget < number mem nat budget bits natural := by
  apply eval_lt_busyBeaverBits _ bits witness _
  · exact lt_of_lt_of_le witness_code_lt (Nat.pow_le_pow_right (by decide) hbits)
  · rw [eval_witness mem nat hnat natural hnatural hmem budget]
    exact Part.mem_some _

/-- The exact surface-language naming collection, realized inside this carrier.
The finite scoped collection only supplies a finite container for it. -/
noncomputable def rawValues {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (budget : Nat) : Finset Nat := by
  classical
  exact (values mem nat budget).filter fun n =>
    ∃ p : RawFormula, p.symbols < budget ∧ p.Denotes mem nat n

theorem mem_rawValues {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) (budget n : Nat) :
    n ∈ rawValues mem nat budget ↔
      ∃ p : RawFormula, p.symbols < budget ∧ p.Denotes mem nat n := by
  classical
  simp only [rawValues, Finset.mem_filter]
  apply and_iff_right_of_imp
  rintro ⟨p, hp, hn⟩
  apply (mem_values hnat).mpr
  refine ⟨p.scope (fun _ => 0), ?_, RawFormula.denotes_scope hn⟩
  simpa [RawFormula.symbols_scope] using hp

/-- Least strict bound for precisely the eligible surface names in this carrier. -/
noncomputable def rawRayo {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (budget : Nat) : Nat := by
  classical
  let v := rawValues mem nat budget
  exact if v.Nonempty then v.sup id + 1 else 0

theorem rawRayo_isLeast {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) (budget : Nat) :
    (∀ p : RawFormula, ∀ n, p.symbols < budget → p.Denotes mem nat n →
      n < rawRayo mem nat budget) ∧
    (∀ b, (∀ p : RawFormula, ∀ n, p.symbols < budget → p.Denotes mem nat n → n < b) →
      rawRayo mem nat budget ≤ b) := by
  classical
  constructor
  · intro p n hp hn
    have hv := (mem_rawValues mem nat hnat budget n).mpr ⟨p, hp, hn⟩
    rw [rawRayo, ite_eq_left ⟨n, hv⟩]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hv)
  · intro b hb
    have h : ∀ n ∈ rawValues mem nat budget, n < b := by
      intro n hn
      obtain ⟨p, hp, hpn⟩ := (mem_rawValues mem nat hnat budget n).mp hn
      exact hb p n hp hpn
    dsimp only [rawRayo]
    split_ifs with hn
    · obtain ⟨n, hn⟩ := hn
      exact Nat.succ_le_of_lt ((Finset.sup_lt_iff (lt_of_le_of_lt (Nat.zero_le n)
        (h n hn))).mpr h)
    · exact Nat.zero_le b

theorem rawRayo_le_boundary {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) (budget : Nat) :
    rawRayo mem nat budget ≤ boundary mem nat budget := by
  apply (rawRayo_isLeast mem nat hnat budget).2
  intro p n hp hn
  exact RawFormula.denotes_lt_scoped_boundary hnat hp hn

theorem rawRayo_lt_number {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) (natural : Formula 1)
    (hnatural : ∀ x, Sat mem natural (fun _ => x) ↔ ∃ n, x = nat n)
    (hmem : ∀ m n, mem (nat m) (nat n) ↔ m < n)
    (budget bits : Nat) (hbits : 61 ≤ bits) :
    rawRayo mem nat budget < number mem nat budget bits natural :=
  lt_of_le_of_lt (rawRayo_le_boundary mem nat hnat budget)
    (boundary_lt_number mem nat hnat natural hnatural hmem budget bits hbits)

def googol : Nat := 10 ^ 100

theorem googol_ge_61 : 61 ≤ googol := by norm_num [googol]

/-- This fixed natural is a model-indexed validation instance. The name of the
intended-universe construction is reserved until its separate certificate exists. -/
noncomputable def modelNumber : Nat :=
  number (α := ZFSet.{u}) (· ∈ ·) NaturalFormula.nat googol googol
    NaturalFormula.natFormula

theorem model_comparison :
    rawRayo (α := ZFSet.{u}) (· ∈ ·) NaturalFormula.nat googol < modelNumber.{u} :=
  rawRayo_lt_number _ _ NaturalFormula.nat_injective NaturalFormula.natFormula
    NaturalFormula.sat_natFormula NaturalFormula.mem_nat_iff googol googol googol_ge_61

#print axioms witness_code_lt
#print axioms eval_witness
#print axioms rawRayo_isLeast
#print axioms rawRayo_lt_number
#print axioms model_comparison

end SamAltmanResearch.Candidate
