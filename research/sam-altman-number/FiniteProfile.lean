import «research».«sam-altman-number».Candidate

/-!
A carrier-free comparison certificate. A profile is a relation on finite
formula syntax and standard naturals. Its intended interpretation is certified
separately by explicit logical derivations; no carrier of all sets is assumed.
The main comparison is unconditional for every profile, including incoherent
ones, because a row is admitted only when it has a unique true entry.
-/

set_option autoImplicit false

namespace SamAltmanResearch.FiniteProfile

open Formula
open SamAltman.OracleMachine SamAltman.OracleSearch SamAltman.OracleHierarchy

abbrev Profile := Formula 1 → Nat → Prop

def Admits (T : Profile) (p : Formula 1) (n : Nat) : Prop :=
  T (unique p) n ∧ ∀ m, T (unique p) m → m = n

theorem admits_unique (T : Profile) (p : Formula 1) (m n : Nat)
    (hm : Admits T p m) (hn : Admits T p n) : m = n := hn.2 m hm.1

def Coherent (T : Profile) : Prop :=
  ∀ p m n, T (unique p) m → T (unique p) n → m = n

theorem admits_iff_of_coherent (T : Profile) (hT : Coherent T)
    (p : Formula 1) (n : Nat) : Admits T p n ↔ T (unique p) n := by
  exact ⟨And.left, fun h => ⟨h, fun m hm => hT p m n hm h⟩⟩

noncomputable def values (T : Profile) (budget : Nat) : Finset Nat := by
  classical
  exact (descriptions budget).biUnion fun p =>
    if h : ∃ n, Admits T p n then {h.choose} else ∅

theorem mem_values (T : Profile) (budget n : Nat) :
    n ∈ values T budget ↔ ∃ p : Formula 1, p.symbols < budget ∧ Admits T p n := by
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
    have hex : ∃ m, Admits T p m := ⟨n, hn⟩
    rw [dite_eq_left hex]
    exact Finset.mem_singleton.mpr (admits_unique T p n hex.choose hn hex.choose_spec)

noncomputable def boundary (T : Profile) (budget : Nat) : Nat := by
  classical
  let v := values T budget
  exact if v.Nonempty then v.sup id + 1 else 0

def Below (T : Profile) (budget n : Nat) : Prop :=
  ∀ p : Formula 1, p.symbols < budget → ∀ m, Admits T p m → m < n

theorem below_boundary (T : Profile) (budget : Nat) : Below T budget (boundary T budget) := by
  classical
  intro p hp m hm
  have hv := (mem_values T budget m).mpr ⟨p, hp, hm⟩
  rw [boundary, ite_eq_left ⟨m, hv⟩]
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hv)

theorem boundary_le (T : Profile) (budget n : Nat) (h : Below T budget n) :
    boundary T budget ≤ n := by
  classical
  have hb : ∀ m ∈ values T budget, m < n := by
    intro m hm
    obtain ⟨p, hp, hpm⟩ := (mem_values T budget m).mp hm
    exact h p hp m hpm
  dsimp only [boundary]
  split_ifs with hne
  · obtain ⟨m, hm⟩ := hne
    exact Nat.succ_le_of_lt ((Finset.sup_lt_iff
      (lt_of_le_of_lt (Nat.zero_le m) (hb m hm))).mpr hb)
  · exact Nat.zero_le n

/-- The base contains the comparison query and all ordinary description-truth channels.
It never receives a numerical boundary or Rayo value as an input parameter. -/
noncomputable def base (T : Profile) (budget input : Nat) : Nat := by
  classical
  exact match input.unpair.1 with
  | 0 => if Below T budget input.unpair.2 then 0 else 1
  | i + 1 => match (descriptionList budget)[i]? with
    | none => 1
    | some p => if T p input.unpair.2 then 0 else 1

theorem base_zero (T : Profile) (budget n : Nat) :
    base T budget (Nat.pair 0 n) = 0 ↔ Below T budget n := by
  classical
  simp [base]

noncomputable def oracle (T : Profile) (budget : Nat) : Nat → Nat := join (base T budget)

theorem oracle_comparison_query (T : Profile) (budget n : Nat) :
    oracle T budget (Nat.pair 0 (Nat.pair 0 n)) = 0 ↔ Below T budget n := by
  simp only [oracle, join_zero_channel, base_zero]

theorem witness_output (T : Profile) (budget : Nat) :
    eval (oracle T budget) Candidate.witness 0 = Part.some (boundary T budget) := by
  apply eval_searchWith_of_least _ Candidate.witnessAddress 0
    (fun n => Nat.pair 0 (Nat.pair 0 n)) (Below T budget)
  · intro n
    simp
  · exact oracle_comparison_query T budget
  · exact below_boundary T budget
  · exact boundary_le T budget

noncomputable def number (T : Profile) (budget bits : Nat) : Nat :=
  busyBeaverBits (oracle T budget) bits

/-- The arithmetic comparison has no coherence or semantic hypothesis. -/
theorem boundary_lt_number (T : Profile) (budget bits : Nat) (hbits : 61 ≤ bits) :
    boundary T budget < number T budget bits := by
  apply eval_lt_busyBeaverBits _ bits Candidate.witness _
  · exact lt_of_lt_of_le Candidate.witness_code_lt
      (Nat.pow_le_pow_right (by decide) hbits)
  · rw [witness_output]
    exact Part.mem_some _

noncomputable def fixedNumber (T : Profile) : Nat :=
  number T Candidate.googol Candidate.googol

theorem fixed_comparison (T : Profile) :
    boundary T Candidate.googol < fixedNumber T :=
  boundary_lt_number T Candidate.googol Candidate.googol Candidate.googol_ge_61

universe u

/-- This instance checks the profile interface against compositional semantics.
The main arithmetic certificate above does not require this or any other carrier. -/
def semanticProfile {α : Type u} (mem : α → α → Prop) (nat : Nat → α) : Profile :=
  fun p n => Sat mem p (fun _ => nat n)

theorem semanticProfile_iff {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (p : Formula 1) (n : Nat) :
    semanticProfile mem nat (unique p) n ↔ Denotes mem nat p n := sat_unique mem p (nat n)

theorem semanticProfile_coherent {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) :
    Coherent (semanticProfile mem nat) := by
  intro p m n hm hn
  exact denotes_unique hnat ((semanticProfile_iff mem nat p m).mp hm)
    ((semanticProfile_iff mem nat p n).mp hn)

theorem semanticProfile_values {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) (budget : Nat) :
    values (semanticProfile mem nat) budget = Formula.values mem nat budget := by
  ext n
  rw [mem_values, Formula.mem_values hnat]
  simp only [admits_iff_of_coherent _ (semanticProfile_coherent mem nat hnat),
    semanticProfile_iff]

theorem semanticProfile_boundary {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) (budget : Nat) :
    boundary (semanticProfile mem nat) budget = Formula.boundary mem nat budget := by
  unfold boundary Formula.boundary
  rw [semanticProfile_values mem nat hnat budget]

/-- Exact bridge to the independently defined raw-language benchmark. -/
theorem rawRayo_lt_profileNumber {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) :
    Candidate.rawRayo mem nat Candidate.googol < fixedNumber (semanticProfile mem nat) := by
  apply lt_of_le_of_lt (Candidate.rawRayo_le_boundary mem nat hnat Candidate.googol)
  rw [← semanticProfile_boundary mem nat hnat]
  exact fixed_comparison _

#print axioms admits_unique
#print axioms mem_values
#print axioms witness_output
#print axioms fixed_comparison
#print axioms semanticProfile_coherent
#print axioms rawRayo_lt_profileNumber

end SamAltmanResearch.FiniteProfile
