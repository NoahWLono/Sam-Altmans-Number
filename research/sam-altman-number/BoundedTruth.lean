import «research».«sam-altman-number».FormulaSemantics

/-! Literal finite expansion of the bounded naming condition. The final
intended-universe comparison is not asserted here. -/

set_option autoImplicit false

namespace SamAltmanResearch.Formula

def rename {k l : Nat} (f : Fin k → Fin l) : Formula k → Formula l
  | .equal i j => .equal (f i) (f j)
  | .member i j => .member (f i) (f j)
  | .neg p => .neg (rename f p)
  | .conj p q => .conj (rename f p) (rename f q)
  | .exists_ p => .exists_ (rename (Fin.cases 0 (fun i => (f i).succ)) p)

theorem symbols_rename {k l : Nat} (f : Fin k → Fin l) (p : Formula k) :
    (rename f p).symbols = p.symbols := by
  induction p generalizing l <;> simp_all [rename, symbols]

universe u

theorem sat_rename {α : Type u} (mem : α → α → Prop) {k l : Nat}
    (f : Fin k → Fin l) (p : Formula k) (s : Fin l → α) :
    Sat mem (rename f p) s ↔ Sat mem p (s ∘ f) := by
  induction p generalizing l with
  | equal => rfl
  | member => rfl
  | neg p ih => exact not_congr (ih f s)
  | conj p q ihp ihq => exact and_congr (ihp f s) (ihq f s)
  | exists_ p ih =>
      simp only [rename, Sat]
      apply exists_congr
      intro x
      rw [ih]
      have h : (Fin.cons x s) ∘ Fin.cases 0 (fun i => (f i).succ) =
          Fin.cons x (s ∘ f) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      rw [h]

def implies {k : Nat} (p q : Formula k) : Formula k := .neg (.conj p (.neg q))
def all {k : Nat} (p : Formula (k + 1)) : Formula k := .neg (.exists_ (.neg p))

@[simp] theorem sat_implies {α : Type u} (mem : α → α → Prop) {k : Nat}
    (p q : Formula k) (s : Fin k → α) :
    Sat mem (implies p q) s ↔ (Sat mem p s → Sat mem q s) := by
  classical
  simp [implies, Sat]

@[simp] theorem sat_all {α : Type u} (mem : α → α → Prop) {k : Nat}
    (p : Formula (k + 1)) (s : Fin k → α) :
    Sat mem (all p) s ↔ ∀ x, Sat mem p (Fin.cons x s) := by
  classical
  simp [all, Sat]

def atVar {k : Nat} (i : Fin k) (p : Formula 1) : Formula k := rename (fun _ => i) p

@[simp] theorem sat_atVar {α : Type u} (mem : α → α → Prop) {k : Nat}
    (i : Fin k) (p : Formula 1) (s : Fin k → α) :
    Sat mem (atVar i p) s ↔ Sat mem p (fun _ => s i) := sat_rename mem _ p s

/-- The sole satisfying object must equal the currently supplied object. -/
def unique (p : Formula 1) : Formula 1 :=
  .conj p (all (implies (atVar 0 p) (.equal 0 1)))

theorem sat_unique {α : Type u} (mem : α → α → Prop) (p : Formula 1) (x : α) :
    Sat mem (unique p) (fun _ => x) ↔
      ∀ y, Sat mem p (fun _ => y) ↔ y = x := by
  simp only [unique, Sat, sat_all, sat_implies, sat_atVar, Fin.cons_zero,
    Fin.cons_one]
  constructor
  · rintro ⟨hx, huniq⟩ y
    exact ⟨huniq y, fun h => h ▸ hx⟩
  · intro h
    exact ⟨(h x).mpr rfl, fun y => (h y).mp⟩

/-- Every natural object uniquely named by `p` lies below the supplied bound. -/
def boundClause (natural p : Formula 1) : Formula 1 :=
  all (implies (.conj (atVar 0 natural) (atVar 0 (unique p))) (.member 0 1))

theorem sat_boundClause {α : Type u} (mem : α → α → Prop)
    (natural p : Formula 1) (b : α) :
    Sat mem (boundClause natural p) (fun _ => b) ↔
      ∀ x, Sat mem natural (fun _ => x) →
        (∀ y, Sat mem p (fun _ => y) ↔ y = x) → mem x b := by
  simp only [boundClause, sat_all, sat_implies, Sat, sat_atVar,
    Fin.cons_zero, Fin.cons_one, sat_unique, and_imp]

/-- An ordered, effective enumeration; duplicates do not affect the conjunction. -/
def enumerateList (k : Nat) : Nat → List (Formula k)
  | 0 => []
  | d + 1 =>
      ((List.finRange k).flatMap fun i => (List.finRange k).map fun j => .equal i j) ++
      ((List.finRange k).flatMap fun i => (List.finRange k).map fun j => .member i j) ++
      (enumerateList k d).map .neg ++
      ((enumerateList k d).flatMap fun p => (enumerateList k d).map fun q => .conj p q) ++
      (enumerateList (k + 1) d).map .exists_

theorem mem_enumerateList {k d : Nat} (p : Formula k) :
    p ∈ enumerateList k d ↔ p.depth ≤ d := by
  induction d generalizing k with
  | zero => simp [enumerateList, Nat.not_le.mpr p.depth_pos]
  | succ d ih => cases p <;> simp [enumerateList, depth, ih]

def descriptionList (budget : Nat) : List (Formula 1) :=
  (enumerateList 1 budget).filter (fun p => p.symbols < budget)

theorem mem_descriptionList {budget : Nat} (p : Formula 1) :
    p ∈ descriptionList budget ↔ p.symbols < budget := by
  simp only [descriptionList, List.mem_filter, decide_eq_true_eq, mem_enumerateList]
  exact and_iff_right_of_imp (fun h => le_trans p.depth_le_symbols (Nat.le_of_lt h))

def conjunction : List (Formula 1) → Formula 1
  | [] => .equal 0 0
  | p :: ps => .conj p (conjunction ps)

theorem sat_conjunction {α : Type u} (mem : α → α → Prop)
    (ps : List (Formula 1)) (s : Fin 1 → α) :
    Sat mem (conjunction ps) s ↔ ∀ p ∈ ps, Sat mem p s := by
  induction ps with
  | nil => simp [conjunction, Sat]
  | cons p ps ih => simp [conjunction, Sat, ih]

/-- Pure first-order syntax: all eligible descriptions are literally inlined. -/
def upperBound (budget : Nat) (natural : Formula 1) : Formula 1 :=
  conjunction ((descriptionList budget).map (boundClause natural))

theorem sat_upperBound {α : Type u} (mem : α → α → Prop)
    (budget : Nat) (natural : Formula 1) (b : α) :
    Sat mem (upperBound budget natural) (fun _ => b) ↔
      ∀ p : Formula 1, p.symbols < budget → ∀ x,
        Sat mem natural (fun _ => x) →
        (∀ y, Sat mem p (fun _ => y) ↔ y = x) → mem x b := by
  simp [upperBound, sat_conjunction, mem_descriptionList, sat_boundClause]

theorem sat_upperBound_iff_boundary_le {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat)
    (natural : Formula 1)
    (hnatural : ∀ x, Sat mem natural (fun _ => x) ↔ ∃ n, x = nat n)
    (hmem : ∀ m n, mem (nat m) (nat n) ↔ m < n) (budget b : Nat) :
    Sat mem (upperBound budget natural) (fun _ => nat b) ↔
      boundary mem nat budget ≤ b := by
  rw [sat_upperBound]
  constructor
  · intro h
    apply boundary_le
    intro n hn
    obtain ⟨p, hp, hden⟩ := (mem_values hnat).mp hn
    exact (hmem n b).mp (h p hp (nat n) ((hnatural _).mpr ⟨n, rfl⟩) hden)
  · intro hb p hp x hx huniq
    obtain ⟨n, rfl⟩ := (hnatural x).mp hx
    apply (hmem n b).mpr
    exact lt_of_lt_of_le (denotes_lt_boundary hnat hp huniq) hb

theorem symbols_boundClause (natural p : Formula 1) :
    (boundClause natural p).symbols = natural.symbols + 2 * p.symbols + 50 := by
  simp [boundClause, unique, atVar, all, implies, symbols, symbols_rename]
  omega

#print axioms sat_rename
#print axioms sat_unique
#print axioms mem_enumerateList
#print axioms sat_upperBound
#print axioms sat_upperBound_iff_boundary_le
#print axioms symbols_boundClause

end SamAltmanResearch.Formula
