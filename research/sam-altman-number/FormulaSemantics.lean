import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
Research foundation for the target in TARGET.md. These are scoped formulas,
raw-to-scoped translation, and semantics in an arbitrary type. The original
Rayo comparison and bounded object-language truth construction are not
established by this file.
-/

set_option autoImplicit false

namespace SamAltmanResearch

/-- A formula with `k` available variables. An existential adds coordinate zero. -/
inductive Formula : Nat → Type
  | equal {k : Nat} (i j : Fin k) : Formula k
  | member {k : Nat} (i j : Fin k) : Formula k
  | neg {k : Nat} (p : Formula k) : Formula k
  | conj {k : Nat} (p q : Formula k) : Formula k
  | exists_ {k : Nat} (p : Formula (k + 1)) : Formula k
  deriving DecidableEq

namespace Formula

/-- Fully parenthesized token convention; each variable occurrence is one token. -/
def symbols {k : Nat} : Formula k → Nat
  | .equal _ _ => 3
  | .member _ _ => 3
  | .neg p => p.symbols + 3
  | .conj p q => p.symbols + q.symbols + 3
  | .exists_ p => p.symbols + 4

def depth {k : Nat} : Formula k → Nat
  | .equal _ _ => 1
  | .member _ _ => 1
  | .neg p => p.depth + 1
  | .conj p q => max p.depth q.depth + 1
  | .exists_ p => p.depth + 1

theorem depth_pos {k : Nat} (p : Formula k) : 0 < p.depth := by
  cases p <;> simp [depth]

theorem depth_le_symbols {k : Nat} (p : Formula k) : p.depth ≤ p.symbols := by
  induction p with
  | equal => simp [depth, symbols]
  | member => simp [depth, symbols]
  | neg p ih => simp only [depth, symbols]; omega
  | conj p q ihp ihq => simp only [depth, symbols]; omega
  | exists_ p ih => simp only [depth, symbols]; omega

/-- A finite, effective enumeration by syntactic depth. -/
def enumerate (k : Nat) : Nat → Finset (Formula k)
  | 0 => ∅
  | d + 1 =>
      (Finset.univ.product Finset.univ).image (fun ij : Fin k × Fin k => .equal ij.1 ij.2) ∪
      (Finset.univ.product Finset.univ).image (fun ij : Fin k × Fin k => .member ij.1 ij.2) ∪
      (enumerate k d).image .neg ∪
      ((enumerate k d).product (enumerate k d)).image (fun pq => .conj pq.1 pq.2) ∪
      (enumerate (k + 1) d).image .exists_

theorem mem_enumerate {k d : Nat} (p : Formula k) :
    p ∈ enumerate k d ↔ p.depth ≤ d := by
  induction d generalizing k with
  | zero => simp [enumerate, Nat.not_le.mpr p.depth_pos]
  | succ d ih =>
      cases p <;> simp [enumerate, depth, ih]

/-- The finite scoped collection selected by a strict token budget. -/
def descriptions (budget : Nat) : Finset (Formula 1) :=
  (enumerate 1 budget).filter (fun p => p.symbols < budget)

theorem mem_descriptions {budget : Nat} (p : Formula 1) :
    p ∈ descriptions budget ↔ p.symbols < budget := by
  simp only [descriptions, Finset.mem_filter, mem_enumerate]
  exact and_iff_right_of_imp (fun h => le_trans p.depth_le_symbols (Nat.le_of_lt h))

universe u

/-- Compositional semantics; no truth oracle is postulated. -/
def Sat {α : Type u} (mem : α → α → Prop) {k : Nat} :
    Formula k → (Fin k → α) → Prop
  | .equal i j, s => s i = s j
  | .member i j, s => mem (s i) (s j)
  | .neg p, s => ¬Sat mem p s
  | .conj p q, s => Sat mem p s ∧ Sat mem q s
  | .exists_ p, s => ∃ x : α, Sat mem p (Fin.cons x s)

/-- Exactly one object satisfies the formula, and that object is the chosen natural. -/
def Denotes {α : Type u} (mem : α → α → Prop) (nat : Nat → α)
    (p : Formula 1) (n : Nat) : Prop :=
  ∀ x : α, Sat mem p (fun _ => x) ↔ x = nat n

theorem denotes_unique {α : Type u} {mem : α → α → Prop} {nat : Nat → α}
    (hnat : Function.Injective nat) {p : Formula 1} {m n : Nat}
    (hm : Denotes mem nat p m) (hn : Denotes mem nat p n) : m = n := by
  apply hnat
  exact (hn (nat m)).mp ((hm (nat m)).mpr rfl)

/-- A second satisfying object is enough to reject a proposed name. -/
theorem not_denotes_of_other {α : Type u} {mem : α → α → Prop} {nat : Nat → α}
    {p : Formula 1} {n : Nat} {x : α}
    (hx : Sat mem p (fun _ => x)) (hne : x ≠ nat n) : ¬Denotes mem nat p n := by
  intro h
  exact hne ((h x).mp hx)

noncomputable def values {α : Type u} (mem : α → α → Prop) (nat : Nat → α)
    (budget : Nat) : Finset Nat := by
  classical
  exact (descriptions budget).biUnion (fun p =>
    if h : ∃ n : Nat, Denotes mem nat p n then {h.choose} else ∅)

theorem mem_values {α : Type u} {mem : α → α → Prop} {nat : Nat → α}
    (hnat : Function.Injective nat) {budget n : Nat} :
    n ∈ values mem nat budget ↔
      ∃ p : Formula 1, p.symbols < budget ∧ Denotes mem nat p n := by
  classical
  simp only [values, Finset.mem_biUnion, mem_descriptions]
  constructor
  · rintro ⟨p, hp, hn⟩
    split_ifs at hn with h
    · have heq : n = h.choose := Finset.mem_singleton.mp hn
      exact ⟨p, hp, heq ▸ h.choose_spec⟩
    · exact False.elim (Finset.notMem_empty n hn)
  · rintro ⟨p, hp, hn⟩
    refine ⟨p, hp, ?_⟩
    have hex : ∃ m, Denotes mem nat p m := ⟨n, hn⟩
    rw [dite_eq_left hex]
    exact Finset.mem_singleton.mpr (denotes_unique hnat hn hex.choose_spec)

/-- Least strict bound; the empty collection has bound zero. -/
noncomputable def boundary {α : Type u} (mem : α → α → Prop) (nat : Nat → α)
    (budget : Nat) : Nat := by
  classical
  let v := values mem nat budget
  exact if v.Nonempty then v.sup id + 1 else 0

theorem lt_boundary {α : Type u} {mem : α → α → Prop} {nat : Nat → α}
    {budget n : Nat} (hn : n ∈ values mem nat budget) :
    n < boundary mem nat budget := by
  classical
  dsimp only [boundary]
  rw [ite_eq_left ⟨n, hn⟩]
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)

theorem boundary_le {α : Type u} {mem : α → α → Prop} {nat : Nat → α}
    {budget b : Nat} (hb : ∀ n ∈ values mem nat budget, n < b) :
    boundary mem nat budget ≤ b := by
  classical
  dsimp only [boundary]
  split_ifs with h
  · obtain ⟨n, hn⟩ := h
    have hbpos : 0 < b := lt_of_le_of_lt (Nat.zero_le n) (hb n hn)
    exact Nat.succ_le_of_lt ((Finset.sup_lt_iff hbpos).mpr hb)
  · exact Nat.zero_le b

theorem denotes_lt_boundary {α : Type u} {mem : α → α → Prop} {nat : Nat → α}
    (hnat : Function.Injective nat) {p : Formula 1} {n budget : Nat}
    (hp : p.symbols < budget) (hn : Denotes mem nat p n) :
    n < boundary mem nat budget :=
  lt_boundary ((mem_values hnat).mpr ⟨p, hp, hn⟩)

end Formula

/-- Surface syntax with arbitrary natural-number variable names. -/
inductive RawFormula
  | equal (i j : Nat)
  | member (i j : Nat)
  | neg (p : RawFormula)
  | conj (p q : RawFormula)
  | exists_ (i : Nat) (p : RawFormula)
  deriving DecidableEq

namespace RawFormula

def symbols : RawFormula → Nat
  | .equal _ _ => 3
  | .member _ _ => 3
  | .neg p => p.symbols + 3
  | .conj p q => p.symbols + q.symbols + 3
  | .exists_ _ p => p.symbols + 4

def freeVars : RawFormula → Finset Nat
  | .equal i j => {i, j}
  | .member i j => {i, j}
  | .neg p => p.freeVars
  | .conj p q => p.freeVars ∪ q.freeVars
  | .exists_ i p => p.freeVars.erase i

/-- Resolve binding into de Bruijn coordinates, keeping the token count. -/
def scope {k : Nat} (names : Nat → Fin k) : RawFormula → Formula k
  | .equal i j => .equal (names i) (names j)
  | .member i j => .member (names i) (names j)
  | .neg p => .neg (p.scope names)
  | .conj p q => .conj (p.scope names) (q.scope names)
  | .exists_ i p => .exists_ (p.scope (fun j => if j = i then 0 else (names j).succ))

theorem symbols_scope {k : Nat} (names : Nat → Fin k) (p : RawFormula) :
    (p.scope names).symbols = p.symbols := by
  induction p generalizing k with
  | equal => rfl
  | member => rfl
  | neg p ih => simp [scope, Formula.symbols, symbols, ih]
  | conj p q ihp ihq => simp [scope, Formula.symbols, symbols, ihp, ihq]
  | exists_ i p ih => simp [scope, Formula.symbols, symbols, ih]

universe u

def Sat {α : Type u} (mem : α → α → Prop) : RawFormula → (Nat → α) → Prop
  | .equal i j, s => s i = s j
  | .member i j, s => mem (s i) (s j)
  | .neg p, s => ¬Sat mem p s
  | .conj p q, s => Sat mem p s ∧ Sat mem q s
  | .exists_ i p, s => ∃ x : α, Sat mem p (Function.update s i x)

theorem sat_congr {α : Type u} (mem : α → α → Prop) (p : RawFormula)
    (s t : Nat → α) (h : ∀ i ∈ p.freeVars, s i = t i) :
    p.Sat mem s ↔ p.Sat mem t := by
  induction p generalizing s t with
  | equal i j =>
      simp only [freeVars, Finset.mem_insert, Finset.mem_singleton] at h
      simp only [Sat, h i (Or.inl rfl), h j (Or.inr rfl)]
  | member i j =>
      simp only [freeVars, Finset.mem_insert, Finset.mem_singleton] at h
      simp only [Sat, h i (Or.inl rfl), h j (Or.inr rfl)]
  | neg p ih => exact not_congr (ih s t h)
  | conj p q ihp ihq =>
      exact and_congr (ihp s t (fun i hi => h i (Finset.mem_union_left _ hi)))
        (ihq s t (fun i hi => h i (Finset.mem_union_right _ hi)))
  | exists_ i p ih =>
      apply exists_congr
      intro x
      apply ih
      intro j hj
      by_cases hji : j = i
      · subst j; simp
      · simpa [Function.update_of_ne hji] using h j (Finset.mem_erase.mpr ⟨hji, hj⟩)

theorem sat_scope {α : Type u} (mem : α → α → Prop) {k : Nat}
    (names : Nat → Fin k) (p : RawFormula) (s : Fin k → α) :
    Formula.Sat mem (p.scope names) s ↔ p.Sat mem (fun i => s (names i)) := by
  induction p generalizing k with
  | equal => rfl
  | member => rfl
  | neg p ih => exact not_congr (ih names s)
  | conj p q ihp ihq => exact and_congr (ihp names s) (ihq names s)
  | exists_ i p ih =>
      simp only [scope, Formula.Sat, Sat]
      apply exists_congr
      intro x
      rw [ih]
      have heq : (fun j => (Fin.cons x s : Fin (_ + 1) → α)
          (if j = i then 0 else (names j).succ)) =
          Function.update (fun j => s (names j)) i x := by
        funext j
        by_cases hji : j = i
        · subst j; simp
        · simp [hji]
      rw [heq]

/-- The quantified assignment condition used by a one-free-variable surface name. -/
def Denotes {α : Type u} (mem : α → α → Prop) (nat : Nat → α)
    (p : RawFormula) (n : Nat) : Prop :=
  p.freeVars = {0} ∧ ∀ s : Nat → α, p.Sat mem s ↔ s 0 = nat n

/-- Equivalence to existence plus uniqueness over all variable assignments. -/
theorem denotes_iff_winning_condition {α : Type u} {mem : α → α → Prop}
    {nat : Nat → α} {p : RawFormula} {n : Nat} :
    p.Denotes mem nat n ↔ p.freeVars = {0} ∧
      (∃ s : Nat → α, s 0 = nat n ∧ p.Sat mem s) ∧
      (∀ t : Nat → α, p.Sat mem t → t 0 = nat n) := by
  constructor
  · rintro ⟨hfree, h⟩
    exact ⟨hfree, ⟨(fun _ => nat n), rfl, (h _).mpr rfl⟩,
      fun t ht => (h t).mp ht⟩
  · rintro ⟨hfree, ⟨s, hsval, hsat⟩, huniq⟩
    refine ⟨hfree, fun t => ⟨huniq t, fun ht => ?_⟩⟩
    apply (sat_congr mem p s t ?_).mp hsat
    intro i hi
    rw [hfree, Finset.mem_singleton] at hi
    subst i
    exact hsval.trans ht.symm

theorem denotes_scope {α : Type u} {mem : α → α → Prop} {nat : Nat → α}
    {p : RawFormula} {n : Nat} (h : p.Denotes mem nat n) :
    Formula.Denotes mem nat (p.scope (fun _ => (0 : Fin 1))) n := by
  intro x
  rw [sat_scope]
  exact h.2 (fun _ => x)

theorem denotes_of_scope {α : Type u} {mem : α → α → Prop} {nat : Nat → α}
    {p : RawFormula} {n : Nat} (hfree : p.freeVars = {0})
    (h : Formula.Denotes mem nat (p.scope (fun _ => (0 : Fin 1))) n) :
    p.Denotes mem nat n := by
  refine ⟨hfree, fun s => ?_⟩
  have hc : p.Sat mem s ↔ p.Sat mem (fun _ => s 0) := by
    apply sat_congr
    intro i hi
    rw [hfree, Finset.mem_singleton] at hi
    subst i
    rfl
  rw [hc, ← sat_scope mem (fun _ => (0 : Fin 1)) p (fun _ => s 0)]
  exact h (s 0)

/-- Every eligible surface name is covered despite the infinite variable alphabet. -/
theorem denotes_lt_scoped_boundary {α : Type u} {mem : α → α → Prop}
    {nat : Nat → α} (hnat : Function.Injective nat)
    {p : RawFormula} {n budget : Nat} (hp : p.symbols < budget)
    (hn : p.Denotes mem nat n) : n < Formula.boundary mem nat budget := by
  apply Formula.denotes_lt_boundary hnat (p := p.scope (fun _ => 0))
  · simpa [symbols_scope] using hp
  · exact denotes_scope hn

end RawFormula

end SamAltmanResearch

#print axioms SamAltmanResearch.Formula.mem_enumerate
#print axioms SamAltmanResearch.Formula.mem_values
#print axioms SamAltmanResearch.Formula.denotes_lt_boundary
#print axioms SamAltmanResearch.Formula.boundary_le
#print axioms SamAltmanResearch.RawFormula.symbols_scope
#print axioms SamAltmanResearch.RawFormula.sat_scope
#print axioms SamAltmanResearch.RawFormula.denotes_of_scope
#print axioms SamAltmanResearch.RawFormula.denotes_iff_winning_condition
#print axioms SamAltmanResearch.RawFormula.denotes_lt_scoped_boundary
