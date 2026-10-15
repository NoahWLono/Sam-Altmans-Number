import «research».«sam-altman-number».GrowthCertificate

/-!
Exact raw-language benchmark for every profile `T : Formula 1 → Nat → Prop`.
For every natural budget, include exactly raw formulas with fewer than that
many symbols, free-variable set exactly `{0}`, and a uniquely admitted
natural in the scoped profile. The benchmark is the least strict bound on
these naturals, with value zero when there are none. All budgets and naturals,
including zero, are covered; no coherence or semantic hypothesis is needed.

The fixed comparison directly relates this original-language benchmark to
`FiniteProfile.samAltman T`. For compositional profiles in any type-carrier
structure with an injective natural representation, the benchmark equals
`Candidate.rawRayo`, including its original assignment-based naming condition.
The intended profile is interpreted externally as explained in the paper;
this module does not select the intended universe of sets.
-/

set_option autoImplicit false

namespace SamAltmanResearch.OriginalBenchmark

open FiniteProfile

/-- A surface name has exactly the designated free variable and is admitted
after the token-preserving scope translation. -/
def rawName (T : Profile) (p : RawFormula) (n : Nat) : Prop :=
  p.freeVars = {0} ∧ Admits T (p.scope (fun _ => (0 : Fin 1))) n

/-- The scoped finite collection is only a container; this filter retains
exactly the naturals with eligible raw-language names. -/
noncomputable def rawValues (T : Profile) (budget : Nat) : Finset Nat := by
  classical
  exact (FiniteProfile.values T budget).filter fun n =>
    ∃ p : RawFormula, p.symbols < budget ∧ rawName T p n

theorem mem_rawValues (T : Profile) (budget n : Nat) :
    n ∈ rawValues T budget ↔
      ∃ p : RawFormula, p.symbols < budget ∧ rawName T p n := by
  classical
  simp only [rawValues, Finset.mem_filter]
  apply and_iff_right_of_imp
  rintro ⟨p, hp, hn⟩
  apply (FiniteProfile.mem_values T budget n).mpr
  refine ⟨p.scope (fun _ => 0), ?_, hn.2⟩
  simpa only [RawFormula.symbols_scope] using hp

/-- Least strict bound for the exact raw naming collection. The empty
collection has least strict bound zero. -/
noncomputable def originalRayo (T : Profile) (budget : Nat) : Nat := by
  classical
  let v := rawValues T budget
  exact if v.Nonempty then v.sup id + 1 else 0

theorem originalRayo_isLeast (T : Profile) (budget : Nat) :
    (∀ p : RawFormula, ∀ n, p.symbols < budget → rawName T p n →
      n < originalRayo T budget) ∧
    (∀ b, (∀ p : RawFormula, ∀ n, p.symbols < budget → rawName T p n → n < b) →
      originalRayo T budget ≤ b) := by
  classical
  constructor
  · intro p n hp hn
    have hv := (mem_rawValues T budget n).mpr ⟨p, hp, hn⟩
    rw [originalRayo, ite_eq_left ⟨n, hv⟩]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hv)
  · intro b hb
    have h : ∀ n ∈ rawValues T budget, n < b := by
      intro n hn
      obtain ⟨p, hp, hpn⟩ := (mem_rawValues T budget n).mp hn
      exact hb p n hp hpn
    dsimp only [originalRayo]
    split_ifs with hn
    · obtain ⟨n, hn⟩ := hn
      exact Nat.succ_le_of_lt ((Finset.sup_lt_iff (lt_of_le_of_lt (Nat.zero_le n)
        (h n hn))).mpr h)
    · exact Nat.zero_le b

theorem originalRayo_le_boundary (T : Profile) (budget : Nat) :
    originalRayo T budget ≤ FiniteProfile.boundary T budget := by
  apply (originalRayo_isLeast T budget).2
  intro p n hp hn
  apply FiniteProfile.below_boundary T budget (p.scope (fun _ => 0)) _ n hn.2
  simpa only [RawFormula.symbols_scope] using hp

/-- Raw names below the budget depend only on the established finite support. -/
theorem rawName_congr (T U : Profile) (budget : Nat) (h : AgreeOn T U budget)
    (p : RawFormula) (hp : p.symbols < budget) (n : Nat) :
    rawName T p n ↔ rawName U p n := by
  have hs : (p.scope (fun _ => (0 : Fin 1))).symbols < budget := by
    simpa only [RawFormula.symbols_scope] using hp
  exact and_congr_right (fun _ => admits_congr T U budget h _ hs n)

theorem rawValues_congr (T U : Profile) (budget : Nat) (h : AgreeOn T U budget) :
    rawValues T budget = rawValues U budget := by
  ext n
  rw [mem_rawValues, mem_rawValues]
  apply exists_congr
  intro p
  exact and_congr_right (fun hp => rawName_congr T U budget h p hp n)

theorem originalRayo_congr (T U : Profile) (budget : Nat) (h : AgreeOn T U budget) :
    originalRayo T budget = originalRayo U budget := by
  unfold originalRayo
  rw [rawValues_congr T U budget h]

theorem restrict_originalRayo (T : Profile) (budget : Nat) :
    originalRayo (restrict T budget) budget = originalRayo T budget :=
  originalRayo_congr _ _ _ (restrict_agrees T budget)

/-- The original-language benchmark is below the named number for every
profile, without a set-carrier or truth hypothesis. -/
theorem originalRayo_lt_samAltman (T : Profile) :
    originalRayo T Candidate.googol < samAltman T := by
  apply lt_of_le_of_lt (originalRayo_le_boundary T Candidate.googol)
  simpa only [restrict_boundary] using samAltman_comparison T

/-- Direct exponential comparison between the exact original raw benchmark
and the fixed named number, uniformly for every profile. -/
theorem exponential_originalRayo_lt_samAltman (T : Profile) :
    2 ^ originalRayo T Candidate.googol < samAltman T := by
  apply lt_of_le_of_lt
    (Nat.pow_le_pow_right (by decide) (originalRayo_le_boundary T Candidate.googol))
  simpa only [restrict_boundary] using
    GrowthCertificate.exponential_boundary_lt_samAltman T

universe u

/-- For a compositional profile, raw profile naming agrees exactly with the
original assignment-based denotation condition, including all-object uniqueness. -/
theorem rawName_semanticProfile_iff {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) (p : RawFormula) (n : Nat) :
    rawName (semanticProfile mem nat) p n ↔ p.Denotes mem nat n := by
  rw [rawName, admits_iff_of_coherent _ (semanticProfile_coherent mem nat hnat),
    semanticProfile_iff]
  exact ⟨fun ⟨hfree, hscope⟩ => RawFormula.denotes_of_scope hfree hscope,
    fun h => ⟨h.1, RawFormula.denotes_scope h⟩⟩

theorem rawValues_semanticProfile {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) (budget : Nat) :
    rawValues (semanticProfile mem nat) budget = Candidate.rawValues mem nat budget := by
  ext n
  rw [mem_rawValues, Candidate.mem_rawValues mem nat hnat]
  simp only [rawName_semanticProfile_iff mem nat hnat]

/-- The carrier-free definition specializes to the independently defined
raw-language benchmark in every injectively represented type-carrier structure. -/
theorem originalRayo_semanticProfile {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) (budget : Nat) :
    originalRayo (semanticProfile mem nat) budget = Candidate.rawRayo mem nat budget := by
  unfold originalRayo Candidate.rawRayo
  rw [rawValues_semanticProfile mem nat hnat]

theorem semantic_exponential_comparison {α : Type u} (mem : α → α → Prop)
    (nat : Nat → α) (hnat : Function.Injective nat) :
    2 ^ Candidate.rawRayo mem nat Candidate.googol < samAltman (semanticProfile mem nat) := by
  rw [← originalRayo_semanticProfile mem nat hnat]
  exact exponential_originalRayo_lt_samAltman _

#print axioms mem_rawValues
#print axioms originalRayo_isLeast
#print axioms originalRayo_le_boundary
#print axioms restrict_originalRayo
#print axioms originalRayo_lt_samAltman
#print axioms exponential_originalRayo_lt_samAltman
#print axioms rawName_semanticProfile_iff
#print axioms originalRayo_semanticProfile
#print axioms semantic_exponential_comparison

end SamAltmanResearch.OriginalBenchmark
