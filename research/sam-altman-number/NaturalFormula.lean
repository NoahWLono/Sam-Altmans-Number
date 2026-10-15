import «research».«sam-altman-number».FormulaSemantics
import Mathlib.SetTheory.ZFC.Ordinal

/-!
A pure equality/membership formula for the finite von Neumann ordinals in
`ZFSet`. This verifies a concrete predicate in this model; it does not identify
the model with the intended universe used in Rayo's informal definition.
-/

set_option autoImplicit false

namespace SamAltmanResearch.NaturalFormula

universe u v

/-- The finite von Neumann ordinal represented by a natural number. -/
noncomputable def nat (n : Nat) : ZFSet.{u} := (n : Ordinal.{u}).toZFSet

theorem nat_injective : Function.Injective nat.{u} := by
  intro m n h
  have h' := Ordinal.toZFSet_injective h
  exact_mod_cast h'

@[simp] theorem nat_zero : nat.{u} 0 = ∅ := by simp [nat]

@[simp] theorem nat_succ (n : Nat) : nat.{u} (n + 1) = insert (nat n) (nat n) := by
  simp [nat, Nat.cast_add, Nat.cast_one]

@[simp] theorem mem_nat_iff (m n : Nat) : nat.{u} m ∈ nat n ↔ m < n := by
  simp [nat]

/-- Abbreviations below expand entirely into the five primitive constructors. -/
def all_ {k : Nat} (p : Formula (k + 1)) : Formula k := .neg (.exists_ (.neg p))

def imp {k : Nat} (p q : Formula k) : Formula k := .neg (.conj p (.neg q))

def disj {k : Nat} (p q : Formula k) : Formula k := .neg (.conj (.neg p) (.neg q))

def iff_ {k : Nat} (p q : Formula k) : Formula k := .conj (imp p q) (imp q p)

theorem sat_all {α : Type v} (mem : α → α → Prop) {k : Nat}
    (p : Formula (k + 1)) (s : Fin k → α) :
    Formula.Sat mem (all_ p) s ↔ ∀ x, Formula.Sat mem p (Fin.cons x s) := by
  classical
  simp [all_, Formula.Sat]

theorem sat_imp {α : Type v} (mem : α → α → Prop) {k : Nat}
    (p q : Formula k) (s : Fin k → α) :
    Formula.Sat mem (imp p q) s ↔ (Formula.Sat mem p s → Formula.Sat mem q s) := by
  classical
  simp [imp, Formula.Sat]

theorem sat_disj {α : Type v} (mem : α → α → Prop) {k : Nat}
    (p q : Formula k) (s : Fin k → α) :
    Formula.Sat mem (disj p q) s ↔ (Formula.Sat mem p s ∨ Formula.Sat mem q s) := by
  classical
  simp only [disj, Formula.Sat]
  tauto

theorem sat_iff {α : Type v} (mem : α → α → Prop) {k : Nat}
    (p q : Formula k) (s : Fin k → α) :
    Formula.Sat mem (iff_ p q) s ↔ (Formula.Sat mem p s ↔ Formula.Sat mem q s) := by
  simp only [iff_, Formula.Sat, sat_imp, iff_def]

/-- Coordinate `i` has no elements. -/
def emptyAt {k : Nat} (i : Fin k) : Formula k := .neg (.exists_ (.member 0 i.succ))

/-- Coordinate `j` is the von Neumann successor of coordinate `i`. -/
def successorAt {k : Nat} (i j : Fin k) : Formula k :=
  all_ (iff_ (.member 0 j.succ) (disj (.equal 0 i.succ) (.member 0 i.succ)))

/-- Coordinate `i` is an inductive set. Bound coordinates are added at zero. -/
def inductiveAt {k : Nat} (i : Fin k) : Formula k :=
  .conj
    (.exists_ (.conj (emptyAt 0) (.member 0 i.succ)))
    (all_ (imp (.member 0 i.succ)
      (.exists_ (.conj (successorAt 1 0) (.member 0 i.succ.succ)))))

/-- The one free variable belongs to every inductive set. -/
def natFormula : Formula 1 := all_ (imp (inductiveAt 0) (.member 1 0))

/-- Exact size after all logical abbreviations have been expanded. -/
theorem natFormula_symbols : natFormula.symbols = 150 := by rfl

/-- Mathematical meaning of the syntactically expanded inductive-set formula. -/
def IsInductive (I : ZFSet.{u}) : Prop :=
  (∅ : ZFSet.{u}) ∈ I ∧ ∀ y ∈ I, insert y y ∈ I

theorem sat_emptyAt {k : Nat} (i : Fin k) (s : Fin k → ZFSet.{u}) :
    Formula.Sat (· ∈ ·) (emptyAt i) s ↔ s i = ∅ := by
  simp [emptyAt, Formula.Sat, ZFSet.eq_empty]

theorem sat_successorAt {k : Nat} (i j : Fin k) (s : Fin k → ZFSet.{u}) :
    Formula.Sat (· ∈ ·) (successorAt i j) s ↔ s j = insert (s i) (s i) := by
  simp [successorAt, sat_all, sat_iff, sat_disj, Formula.Sat, ZFSet.ext_iff]

theorem sat_inductiveAt {k : Nat} (i : Fin k) (s : Fin k → ZFSet.{u}) :
    Formula.Sat (· ∈ ·) (inductiveAt i) s ↔ IsInductive (s i) := by
  simp [inductiveAt, Formula.Sat, sat_emptyAt, sat_all, sat_imp, sat_successorAt,
    IsInductive]

theorem sat_natFormula_inductive (x : ZFSet.{u}) :
    Formula.Sat (· ∈ ·) natFormula (fun _ => x) ↔ ∀ I, IsInductive I → x ∈ I := by
  simp [natFormula, sat_all, sat_imp, sat_inductiveAt, Formula.Sat]

theorem nat_mem_of_inductive {I : ZFSet.{u}} (hI : IsInductive I) (n : Nat) :
    nat n ∈ I := by
  induction n with
  | zero => simpa using hI.1
  | succ n ih => simpa using hI.2 (nat n) ih

theorem range_nat_inductive : IsInductive (ZFSet.range nat.{u}) := by
  constructor
  · exact ZFSet.mem_range.mpr ⟨0, nat_zero⟩
  · intro y hy
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hy
    exact ZFSet.mem_range.mpr ⟨n + 1, nat_succ n⟩

/-- Exact characterization, including zero, with no added semantic assumption. -/
theorem sat_natFormula (x : ZFSet.{u}) :
    Formula.Sat (· ∈ ·) natFormula (fun _ => x) ↔ ∃ n : Nat, x = nat n := by
  rw [sat_natFormula_inductive]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := ZFSet.mem_range.mp (h _ range_nat_inductive)
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, rfl⟩ I hI
    exact nat_mem_of_inductive hI n

end SamAltmanResearch.NaturalFormula

#print axioms SamAltmanResearch.NaturalFormula.nat_injective
#print axioms SamAltmanResearch.NaturalFormula.mem_nat_iff
#print axioms SamAltmanResearch.NaturalFormula.natFormula_symbols
#print axioms SamAltmanResearch.NaturalFormula.sat_inductiveAt
#print axioms SamAltmanResearch.NaturalFormula.sat_natFormula
