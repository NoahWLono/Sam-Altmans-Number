import «research».«sam-altman-number».BoundedTruth

/-!
Explicit first-order natural deduction for the finite naming-bound compiler.
The precise helper target is recorded in FOUNDATIONS-ROUND2.md. There is no
rule importing semantic validity or an arbitrary Lean proof as a derivation.
The intended-universe final comparison is not asserted in this module.
-/

set_option autoImplicit false

namespace SamAltmanResearch.Formula

def instantiate {k : Nat} (p : Formula (k + 1)) (i : Fin k) : Formula k :=
  rename (Fin.cases i id) p

theorem rename_rename {k l m : Nat} (f : Fin k → Fin l) (g : Fin l → Fin m)
    (p : Formula k) : rename g (rename f p) = rename (g ∘ f) p := by
  induction p generalizing l m with
  | equal => rfl
  | member => rfl
  | neg p ih => simp [rename, ih]
  | conj p q ihp ihq => simp [rename, ihp, ihq]
  | exists_ p ih =>
      simp only [rename, ih]
      congr 2
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem rename_atVar {k l : Nat} (f : Fin k → Fin l) (i : Fin k)
    (p : Formula 1) : rename f (atVar i p) = atVar (f i) p := by
  simp [atVar, rename_rename, Function.comp_def]

universe u

theorem sat_instantiate {α : Type u} (mem : α → α → Prop) {k : Nat}
    (p : Formula (k + 1)) (i : Fin k) (s : Fin k → α) :
    Sat mem (instantiate p i) s ↔ Sat mem p (Fin.cons (s i) s) := by
  rw [instantiate, sat_rename]
  have hs : s ∘ Fin.cases i id = Fin.cons (s i) s := by
    funext j
    refine Fin.cases ?_ (fun l => ?_) j <;> simp
  rw [hs]

theorem sat_shift {α : Type u} (mem : α → α → Prop) {k : Nat}
    (p : Formula k) (x : α) (s : Fin k → α) :
    Sat mem (rename Fin.succ p) (Fin.cons x s) ↔ Sat mem p s := by
  simpa [Function.comp_def] using sat_rename mem Fin.succ p (Fin.cons x s)

/-- A syntactic derivation from a finite context. Every constructor is a rule. -/
inductive Derivation : {k : Nat} → List (Formula k) → Formula k → Prop
  | hypothesis {k : Nat} {Γ : List (Formula k)} {p : Formula k}
      (hp : p ∈ Γ) : Derivation Γ p
  | weaken {k : Nat} {Γ Δ : List (Formula k)} {p : Formula k}
      (h : Derivation Γ p) (hΓ : ∀ q ∈ Γ, q ∈ Δ) : Derivation Δ p
  | rename {k l : Nat} {Γ : List (Formula k)} {p : Formula k}
      (f : Fin k → Fin l) (h : Derivation Γ p) :
      Derivation (Γ.map (Formula.rename f)) (Formula.rename f p)
  | conjIntro {k : Nat} {Γ : List (Formula k)} {p q : Formula k}
      (hp : Derivation Γ p) (hq : Derivation Γ q) : Derivation Γ (.conj p q)
  | conjLeft {k : Nat} {Γ : List (Formula k)} {p q : Formula k}
      (h : Derivation Γ (.conj p q)) : Derivation Γ p
  | conjRight {k : Nat} {Γ : List (Formula k)} {p q : Formula k}
      (h : Derivation Γ (.conj p q)) : Derivation Γ q
  | impliesIntro {k : Nat} {Γ : List (Formula k)} {p q : Formula k}
      (h : Derivation (p :: Γ) q) : Derivation Γ (implies p q)
  | impliesElim {k : Nat} {Γ : List (Formula k)} {p q : Formula k}
      (h : Derivation Γ (implies p q)) (hp : Derivation Γ p) : Derivation Γ q
  | negIntro {k : Nat} {Γ : List (Formula k)} {p q : Formula k}
      (hq : Derivation (p :: Γ) q) (hnq : Derivation (p :: Γ) (.neg q)) :
      Derivation Γ (.neg p)
  | contradiction {k : Nat} {Γ : List (Formula k)} {p q : Formula k}
      (hp : Derivation Γ p) (hnp : Derivation Γ (.neg p)) : Derivation Γ q
  | classical {k : Nat} {Γ : List (Formula k)} {p q : Formula k}
      (hq : Derivation (.neg p :: Γ) q) (hnq : Derivation (.neg p :: Γ) (.neg q)) :
      Derivation Γ p
  | allIntro {k : Nat} {Γ : List (Formula k)} {p : Formula (k + 1)}
      (h : Derivation (Γ.map (Formula.rename Fin.succ)) p) : Derivation Γ (all p)
  | allElim {k : Nat} {Γ : List (Formula k)} {p : Formula (k + 1)}
      (i : Fin k) (h : Derivation Γ (all p)) : Derivation Γ (instantiate p i)
  | existsIntro {k : Nat} {Γ : List (Formula k)} {p : Formula (k + 1)}
      (i : Fin k) (h : Derivation Γ (instantiate p i)) : Derivation Γ (.exists_ p)
  | existsElim {k : Nat} {Γ : List (Formula k)} {p : Formula (k + 1)} {q : Formula k}
      (hp : Derivation Γ (.exists_ p))
      (hq : Derivation (p :: Γ.map (Formula.rename Fin.succ)) (Formula.rename Fin.succ q)) :
      Derivation Γ q
  | equalRefl {k : Nat} {Γ : List (Formula k)} (i : Fin k) : Derivation Γ (.equal i i)
  | equalSubst {k : Nat} {Γ : List (Formula k)} {i j : Fin k}
      (p : Formula (k + 1)) (hij : Derivation Γ (.equal i j))
      (hp : Derivation Γ (instantiate p i)) : Derivation Γ (instantiate p j)

namespace Derivation

/-- Structural soundness in every type-carrier structure, with no set-theory premises. -/
theorem sound {α : Type u} (mem : α → α → Prop) {k : Nat}
    {Γ : List (Formula k)} {p : Formula k} (h : Derivation Γ p) :
    ∀ s : Fin k → α, (∀ q ∈ Γ, Sat mem q s) → Sat mem p s := by
  induction h with
  | hypothesis hp => exact fun _ hs => hs _ hp
  | weaken h hΓ ih => exact fun s hs => ih s (fun q hq => hs q (hΓ q hq))
  | @rename k l Γ p f h ih =>
      intro s hs
      apply (sat_rename mem f p s).mpr
      apply ih
      intro q hq
      exact (sat_rename mem f q s).mp (hs _ (List.mem_map.mpr ⟨q, hq, rfl⟩))
  | conjIntro hp hq ihp ihq => exact fun s hs => ⟨ihp s hs, ihq s hs⟩
  | conjLeft h ih => exact fun s hs => (ih s hs).1
  | conjRight h ih => exact fun s hs => (ih s hs).2
  | @impliesIntro k Γ p q h ih =>
      intro s hs
      apply (sat_implies mem p q s).mpr
      intro hp
      apply ih s
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hp
      · exact hs r hr
  | impliesElim h hp ih ihp =>
      exact fun s hs => (sat_implies mem _ _ s).mp (ih s hs) (ihp s hs)
  | @negIntro k Γ p q hq hnq ihq ihnq =>
      intro s hs hp
      have hctx : ∀ r ∈ p :: Γ, Sat mem r s := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hp
        · exact hs r hr
      exact ihnq s hctx (ihq s hctx)
  | contradiction hp hnp ihp ihnp => exact fun s hs => False.elim (ihnp s hs (ihp s hs))
  | @classical k Γ p q hq hnq ihq ihnq =>
      intro s hs
      classical
      by_contra hp
      have hctx : ∀ r ∈ .neg p :: Γ, Sat mem r s := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hp
        · exact hs r hr
      exact ihnq s hctx (ihq s hctx)
  | @allIntro k Γ p h ih =>
      intro s hs
      apply (sat_all mem p s).mpr
      intro x
      apply ih (Fin.cons x s)
      intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
      exact (sat_shift mem r x s).mpr (hs r hr)
  | allElim i h ih =>
      intro s hs
      exact (sat_instantiate mem _ i s).mpr ((sat_all mem _ s).mp (ih s hs) (s i))
  | existsIntro i h ih =>
      intro s hs
      exact ⟨s i, (sat_instantiate mem _ i s).mp (ih s hs)⟩
  | @existsElim k Γ p q hp hq ihp ihq =>
      intro s hs
      obtain ⟨x, hx⟩ := ihp s hs
      apply (sat_shift mem q x s).mp
      apply ihq (Fin.cons x s)
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hx
      · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
        exact (sat_shift mem r' x s).mpr (hs r' hr')
  | equalRefl i => exact fun _ _ => rfl
  | equalSubst p hij hp ihij ihp =>
      intro s hs
      apply (sat_instantiate mem p _ s).mpr
      have h := (sat_instantiate mem p _ s).mp (ihp s hs)
      have heq := ihij s hs
      change s _ = s _ at heq
      rw [heq] at h
      exact h

theorem conjunction_elim {Γ : List (Formula 1)} {ps : List (Formula 1)}
    {p : Formula 1} (hp : p ∈ ps) (h : Derivation Γ (conjunction ps)) :
    Derivation Γ p := by
  induction ps with
  | nil => exact False.elim (List.not_mem_nil hp)
  | cons q qs ih =>
      rcases List.mem_cons.mp hp with rfl | hp
      · exact .conjLeft h
      · exact ih hp (.conjRight h)

/-- The compiler carries a syntactic proof of each eligible bound clause. -/
theorem upperBound_clause (budget : Nat) (natural p : Formula 1)
    (hp : p.symbols < budget) :
    Derivation [upperBound budget natural] (boundClause natural p) := by
  apply conjunction_elim (ps := (descriptionList budget).map (boundClause natural))
  · exact List.mem_map.mpr ⟨p, (mem_descriptionList p).mpr hp, rfl⟩
  · exact .hypothesis (List.mem_singleton.mpr rfl)

/-- The finite compiler's key inference, as an actual object-language derivation. -/
theorem upperBound_apply (budget : Nat) (natural p : Formula 1)
    (hp : p.symbols < budget) :
    Derivation
      [atVar (1 : Fin 2) (upperBound budget natural),
       atVar 0 natural, atVar 0 (unique p)] (.member 0 1) := by
  let Γ : List (Formula 2) :=
    [atVar 1 (upperBound budget natural), atVar 0 natural, atVar 0 (unique p)]
  change Derivation Γ (.member 0 1)
  have hbc : Derivation Γ (atVar (1 : Fin 2) (boundClause natural p)) := by
    have h := Derivation.rename (fun _ : Fin 1 => (1 : Fin 2))
      (upperBound_clause budget natural p hp)
    apply Derivation.weaken h
    intro q hq
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hq
    subst q
    exact List.mem_cons_self
  have hall : Derivation Γ
      (all (implies (.conj (atVar (0 : Fin 3) natural) (atVar 0 (unique p)))
        (.member 0 2))) := by
    have hidx : Fin.cases (0 : Fin 3) (fun _ : Fin 1 => (2 : Fin 3))
        (1 : Fin 2) = (2 : Fin 3) := rfl
    simpa [atVar, boundClause, all, implies, Formula.rename, rename_rename,
      Function.comp_def, hidx] using hbc
  have himp : Derivation Γ
      (implies (.conj (atVar (0 : Fin 2) natural) (atVar 0 (unique p)))
        (.member 0 1)) := by
    have hidx : Fin.cases (0 : Fin 2) (id : Fin 2 → Fin 2)
        (2 : Fin 3) = (1 : Fin 2) := rfl
    simpa [instantiate, implies, Formula.rename, atVar, rename_rename,
      Function.comp_def, hidx] using Derivation.allElim 0 hall
  apply Derivation.impliesElim himp
  exact .conjIntro (.hypothesis (by simp [Γ])) (.hypothesis (by simp [Γ]))

/-- All-object unique naming is single-valued, proved solely by logical rules. -/
theorem unique_same (p : Formula 1) :
    Derivation [atVar (0 : Fin 2) (unique p), atVar 1 (unique p)] (.equal 0 1) := by
  let Γ : List (Formula 2) := [atVar 0 (unique p), atVar 1 (unique p)]
  change Derivation Γ (.equal 0 1)
  have hx : Derivation Γ (atVar (0 : Fin 2) p) := by
    have h : Derivation Γ (atVar (0 : Fin 2) (unique p)) :=
      .hypothesis (by simp [Γ])
    exact .conjLeft h
  have hy : Derivation Γ (atVar (1 : Fin 2) (unique p)) :=
    .hypothesis (by simp [Γ])
  have hy' : Derivation Γ
      (.conj (atVar (1 : Fin 2) p)
        (all (implies (atVar (0 : Fin 3) p) (.equal 0 2)))) := by
    have hidx : Fin.cases (0 : Fin 3) (fun _ : Fin 1 => (2 : Fin 3))
        (1 : Fin 2) = (2 : Fin 3) := rfl
    simpa [atVar, unique, all, implies, Formula.rename, rename_rename,
      Function.comp_def, hidx] using hy
  have himp : Derivation Γ (implies (atVar (0 : Fin 2) p) (.equal 0 1)) := by
    have hidx : Fin.cases (0 : Fin 2) (id : Fin 2 → Fin 2)
        (2 : Fin 3) = (1 : Fin 2) := rfl
    simpa [instantiate, implies, Formula.rename, atVar, rename_rename,
      Function.comp_def, hidx] using Derivation.allElim 0 (Derivation.conjRight hy')
  exact .impliesElim himp hx

end Derivation

#print axioms Derivation.sound
#print axioms sat_instantiate
#print axioms Derivation.upperBound_clause
#print axioms Derivation.upperBound_apply
#print axioms Derivation.unique_same

end SamAltmanResearch.Formula
