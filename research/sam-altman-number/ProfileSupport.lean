import «research».«sam-altman-number».FiniteProfile

/-!
Finite support of the semantic input. This is the precise reason the intended
profile can be supplied by finitely many Separation instances rather than an
unbounded set-theoretic truth predicate.
-/

set_option autoImplicit false

namespace SamAltmanResearch.FiniteProfile

open Formula

def support (budget : Nat) : Finset (Formula 1) :=
  descriptions budget ∪ (descriptions budget).image unique

theorem mem_support_of_small {budget : Nat} {p : Formula 1}
    (hp : p.symbols < budget) : p ∈ support budget :=
  Finset.mem_union_left _ ((mem_descriptions p).mpr hp)

theorem unique_mem_support_of_small {budget : Nat} {p : Formula 1}
    (hp : p.symbols < budget) : unique p ∈ support budget :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, (mem_descriptions p).mpr hp, rfl⟩)

def AgreeOn (T U : Profile) (budget : Nat) : Prop :=
  ∀ p ∈ support budget, ∀ n, T p n ↔ U p n

theorem admits_congr (T U : Profile) (budget : Nat) (h : AgreeOn T U budget)
    (p : Formula 1) (hp : p.symbols < budget) (n : Nat) :
    Admits T p n ↔ Admits U p n := by
  have ht := h (unique p) (unique_mem_support_of_small hp)
  simp only [Admits, ht]

theorem below_congr (T U : Profile) (budget : Nat) (h : AgreeOn T U budget) (n : Nat) :
    Below T budget n ↔ Below U budget n := by
  constructor
  · intro hb p hp m hm
    exact hb p hp m ((admits_congr T U budget h p hp m).mpr hm)
  · intro hb p hp m hm
    exact hb p hp m ((admits_congr T U budget h p hp m).mp hm)

theorem values_congr (T U : Profile) (budget : Nat) (h : AgreeOn T U budget) :
    values T budget = values U budget := by
  ext n
  rw [mem_values, mem_values]
  apply exists_congr
  intro p
  exact and_congr_right (fun hp => admits_congr T U budget h p hp n)

theorem boundary_congr (T U : Profile) (budget : Nat) (h : AgreeOn T U budget) :
    boundary T budget = boundary U budget := by
  unfold boundary
  rw [values_congr T U budget h]

theorem base_congr (T U : Profile) (budget : Nat) (h : AgreeOn T U budget) :
    base T budget = base U budget := by
  classical
  funext input
  unfold base
  cases hi : input.unpair.1 with
  | zero => simp only [below_congr T U budget h]
  | succ i =>
      cases he : (descriptionList budget)[i]? with
      | none => simp only [he]
      | some p =>
          have hp : p ∈ descriptionList budget := List.mem_of_getElem? he
          have hs := mem_support_of_small ((mem_descriptionList p).mp hp)
          simp only [he, h p hs]

theorem number_congr (T U : Profile) (budget bits : Nat) (h : AgreeOn T U budget) :
    number T budget bits = number U budget bits := by
  unfold number oracle
  rw [base_congr T U budget h]

def restrict (T : Profile) (budget : Nat) : Profile :=
  fun p n => p ∈ support budget ∧ T p n

theorem restrict_agrees (T : Profile) (budget : Nat) :
    AgreeOn (restrict T budget) T budget := by
  intro p hp n
  simp [restrict, hp]

theorem restrict_false_outside (T : Profile) (budget : Nat) (p : Formula 1)
    (hp : p ∉ support budget) (n : Nat) : ¬restrict T budget p n := by
  simp [restrict, hp]

theorem restrict_number (T : Profile) (budget bits : Nat) :
    number (restrict T budget) budget bits = number T budget bits :=
  number_congr _ _ _ _ (restrict_agrees T budget)

theorem restrict_boundary (T : Profile) (budget : Nat) :
    boundary (restrict T budget) budget = boundary T budget :=
  boundary_congr _ _ _ (restrict_agrees T budget)

/-- The fixed construction reads only the finite support at the fixed googol
budget. In the paper the argument is the explicitly specified intended profile. -/
noncomputable def samAltman (T : Profile) : Nat :=
  fixedNumber (restrict T Candidate.googol)

theorem samAltman_eq (T : Profile) : samAltman T = fixedNumber T :=
  restrict_number T Candidate.googol Candidate.googol

theorem samAltman_comparison (T : Profile) :
    boundary (restrict T Candidate.googol) Candidate.googol < samAltman T :=
  fixed_comparison (restrict T Candidate.googol)

universe u

theorem rawRayo_lt_samAltman {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) :
    Candidate.rawRayo mem nat Candidate.googol < samAltman (semanticProfile mem nat) := by
  rw [samAltman_eq]
  exact rawRayo_lt_profileNumber mem nat hnat

#print axioms unique_mem_support_of_small
#print axioms values_congr
#print axioms base_congr
#print axioms restrict_number
#print axioms samAltman_comparison
#print axioms rawRayo_lt_samAltman

end SamAltmanResearch.FiniteProfile
