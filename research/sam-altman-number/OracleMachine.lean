import Mathlib.Computability.PartrecCode
import Mathlib.Data.Finset.Lattice.Fold

/-!
Oracle-machine foundations for the proposed comparison witness.
The comparison with the original Rayo number is not proved in this file.
-/

namespace SamAltman.OracleMachine

set_option autoImplicit false

/-- Finite oracle programs. `prim` embeds an explicitly coded ordinary partial
recursive program; the other constructors allow its oracle-dependent composition. -/
inductive Program where
  | prim : Nat.Partrec.Code → Program
  | query : Program
  | guardZero : Program
  | pair : Program → Program → Program
  | comp : Program → Program → Program
  | prec : Program → Program → Program
  | find : Program → Program

/-- Tags occupy the bottom three binary digits. Tag 7 is reserved. -/
def encode : Program → ℕ
  | .prim p => 8 * Nat.Partrec.Code.encodeCode p
  | .query => 1
  | .guardZero => 2
  | .pair p q => 8 * Nat.pair (encode p) (encode q) + 3
  | .comp p q => 8 * Nat.pair (encode p) (encode q) + 4
  | .prec p q => 8 * Nat.pair (encode p) (encode q) + 5
  | .find p => 8 * encode p + 6

/-- Decode a natural code. Recursive child codes are strictly smaller than the
parent, independently of whether the parent is a valid encoding. -/
def decode (n : ℕ) : Option Program :=
  if hn : n = 0 then some (.prim .zero) else
    let m := n / 8
    have hm : m < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
    have hleft : m.unpair.1 < n := lt_of_le_of_lt m.unpair_left_le hm
    have hright : m.unpair.2 < n := lt_of_le_of_lt m.unpair_right_le hm
    match n % 8 with
    | 0 => some (.prim (Nat.Partrec.Code.ofNatCode m))
    | 1 => if m = 0 then some .query else none
    | 2 => if m = 0 then some .guardZero else none
    | 3 => do return .pair (← decode m.unpair.1) (← decode m.unpair.2)
    | 4 => do return .comp (← decode m.unpair.1) (← decode m.unpair.2)
    | 5 => do return .prec (← decode m.unpair.1) (← decode m.unpair.2)
    | 6 => do return .find (← decode m)
    | _ => none
termination_by n

@[simp] theorem decode_encode (p : Program) : decode (encode p) = some p := by
  induction p with
  | prim p =>
      rw [encode, decode]
      by_cases hp : Nat.Partrec.Code.encodeCode p = 0
      · have hpzero : p = .zero := by
          apply Encodable.encode_injective
          simpa [Nat.Partrec.Code.encodeCode_eq, Nat.Partrec.Code.encodeCode] using hp
        subst p
        simp [Nat.Partrec.Code.encodeCode]
      · have henc : Encodable.encode p ≠ 0 := hp
        simp [henc, ← Nat.Partrec.Code.encodeCode_eq,
          ← Nat.Partrec.Code.ofNatCode_eq]
  | query => simp [encode, decode]
  | guardZero => simp [encode, decode]
  | pair p q hp hq =>
      rw [encode, decode]
      simp [Nat.add_mod, Nat.mul_add_div, hp, hq]
  | comp p q hp hq =>
      rw [encode, decode]
      simp [Nat.add_mod, Nat.mul_add_div, hp, hq]
  | prec p q hp hq =>
      rw [encode, decode]
      simp [Nat.add_mod, Nat.mul_add_div, hp, hq]
  | find p hp =>
      rw [encode, decode]
      simp [Nat.add_mod, Nat.mul_add_div, hp]

theorem encode_injective : Function.Injective encode := by
  intro p q h
  have := congrArg decode h
  simpa using this

/-- Deterministic partial semantics. The oracle is an arbitrary total function;
no computability or set-truth assumption is made about it. -/
def eval (oracle : ℕ → ℕ) : Program → ℕ → Part ℕ
  | .prim p => Nat.Partrec.Code.eval p
  | .query => fun n => Part.some (oracle n)
  | .guardZero => fun n => if n = 0 then Part.some 0 else Part.none
  | .pair p q => fun n => Nat.pair <$> eval oracle p n <*> eval oracle q n
  | .comp p q => fun n => eval oracle q n >>= eval oracle p
  | .prec p q => Nat.unpaired fun a n =>
      n.rec (eval oracle p a) fun k previous => do
        let value ← previous
        eval oracle q (Nat.pair a (Nat.pair k value))
  | .find p => fun a =>
      Nat.rfind fun n => (fun m => m = 0) <$> eval oracle p (Nat.pair a n)

@[simp] theorem eval_prim (oracle : ℕ → ℕ) (p : Nat.Partrec.Code) (n : ℕ) :
    eval oracle (.prim p) n = Nat.Partrec.Code.eval p n := rfl

@[simp] theorem eval_query (oracle : ℕ → ℕ) (n : ℕ) :
    eval oracle .query n = Part.some (oracle n) := rfl

@[simp] theorem eval_comp (oracle : ℕ → ℕ) (p q : Program) (n : ℕ) :
    eval oracle (.comp p q) n = (eval oracle q n >>= eval oracle p) := rfl

@[simp] theorem eval_prec_zero (oracle : ℕ → ℕ) (p q : Program) (a : ℕ) :
    eval oracle (.prec p q) (Nat.pair a 0) = eval oracle p a := by
  simp [eval, Nat.unpaired]

theorem eval_prec_succ (oracle : ℕ → ℕ) (p q : Program) (a k : ℕ) :
    eval oracle (.prec p q) (Nat.pair a (k + 1)) =
      (eval oracle (.prec p q) (Nat.pair a k) >>= fun value =>
        eval oracle q (Nat.pair a (Nat.pair k value))) := by
  simp [eval, Nat.unpaired]

set_option backward.isDefEq.respectTransparency false in
/-- Minimization requires every preceding computation to terminate with a
nonzero value. A later zero cannot skip an earlier divergent computation. -/
theorem mem_eval_find (oracle : ℕ → ℕ) (p : Program) (a n : ℕ) :
    n ∈ eval oracle (.find p) a ↔
      0 ∈ eval oracle p (Nat.pair a n) ∧
        ∀ m < n, ∃ value, value ∈ eval oracle p (Nat.pair a m) ∧ value ≠ 0 := by
  change (n ∈ Nat.rfind (fun m => Part.map (fun v => decide (v = 0))
    (eval oracle p (Nat.pair a m)))) ↔ _
  rw [Nat.mem_rfind]
  simp [Part.mem_map_iff]

def constant (n : ℕ) : Program := .prim (Nat.Partrec.Code.const n)

@[simp] theorem eval_constant (oracle : ℕ → ℕ) (n input : ℕ) :
    eval oracle (constant n) input = Part.some n := by
  simp [constant]

/-- Hardwire an input while retaining the fixed blank-input Busy Beaver convention. -/
def onInput (p : Program) (n : ℕ) : Program := .comp p (constant n)

@[simp] theorem eval_onInput (oracle : ℕ → ℕ) (p : Program) (n input : ℕ) :
    eval oracle (onInput p n) input = eval oracle p n := by
  simp [onInput]

theorem eval_deterministic (oracle : ℕ → ℕ) (p : Program) (n a b : ℕ)
    (ha : a ∈ eval oracle p n) (hb : b ∈ eval oracle p n) : a = b :=
  Part.mem_unique ha hb

/-- Invalid codes diverge rather than being assigned an executable default. -/
def run (oracle : ℕ → ℕ) (code input : ℕ) : Part ℕ :=
  match decode code with
  | none => Part.none
  | some p => eval oracle p input

@[simp] theorem run_encode (oracle : ℕ → ℕ) (p : Program) (n : ℕ) :
    run oracle (encode p) n = eval oracle p n := by
  simp [run]

/-- A total auxiliary value used only to form the finite maximum. Divergent
programs contribute zero; this does not turn their evaluator into a total one. -/
noncomputable def outputOrZero (oracle : ℕ → ℕ) (code input : ℕ) : ℕ := by
  classical
  exact (run oracle code input).getOrElse 0

theorem outputOrZero_of_mem (oracle : ℕ → ℕ) (code input value : ℕ)
    (h : value ∈ run oracle code input) : outputOrZero oracle code input = value := by
  classical
  unfold outputOrZero
  rw [Part.getOrElse_of_dom _ h.fst]
  exact Part.get_eq_of_mem h _

/-- One above the finite maximum of outputs on the blank input, with a zero
fallback. This is a strict output bound, including for the empty code budget. -/
noncomputable def busyBeaver (oracle : ℕ → ℕ) (budget : ℕ) : ℕ :=
  (Finset.range budget).sup (fun code => outputOrZero oracle code 0) + 1

theorem busyBeaver_pos (oracle : ℕ → ℕ) (budget : ℕ) :
    0 < busyBeaver oracle budget := Nat.zero_lt_succ _

theorem busyBeaver_mono (oracle : ℕ → ℕ) : Monotone (busyBeaver oracle) := by
  intro a b hab
  apply Nat.add_le_add_right
  exact Finset.sup_mono (Finset.range_mono hab)

theorem output_lt_busyBeaver (oracle : ℕ → ℕ) (budget code value : ℕ)
    (hcode : code < budget) (hvalue : value ∈ run oracle code 0) :
    value < busyBeaver oracle budget := by
  unfold busyBeaver
  have hle := Finset.le_sup (f := fun code => outputOrZero oracle code 0)
    (Finset.mem_range.mpr hcode)
  rw [outputOrZero_of_mem oracle code 0 value hvalue] at hle
  exact Nat.lt_succ_of_le hle

theorem eval_lt_busyBeaver (oracle : ℕ → ℕ) (budget : ℕ) (p : Program) (value : ℕ)
    (hcode : encode p < budget) (hvalue : value ∈ eval oracle p 0) :
    value < busyBeaver oracle budget := by
  apply output_lt_busyBeaver oracle budget (encode p) value hcode
  simpa using hvalue

/-- Fixed-width binary budget: use the numerical codes strictly below
`2^bits`. At the zero-bit budget this convention admits only code zero. -/
noncomputable def busyBeaverBits (oracle : ℕ → ℕ) (bits : ℕ) : ℕ :=
  busyBeaver oracle (2 ^ bits)

theorem eval_lt_busyBeaverBits (oracle : ℕ → ℕ) (bits : ℕ) (p : Program) (value : ℕ)
    (hcode : encode p < 2 ^ bits) (hvalue : value ∈ eval oracle p 0) :
    value < busyBeaverBits oracle bits :=
  eval_lt_busyBeaver oracle (2 ^ bits) p value hcode hvalue

theorem input_eval_lt_busyBeaverBits (oracle : ℕ → ℕ) (bits : ℕ)
    (p : Program) (input value : ℕ)
    (hcode : encode (onInput p input) < 2 ^ bits)
    (hvalue : value ∈ eval oracle p input) : value < busyBeaverBits oracle bits := by
  apply eval_lt_busyBeaverBits oracle bits (onInput p input) value hcode
  simpa using hvalue

/-- The diagonal halting oracle for this very language and encoding. -/
noncomputable def selfHalting (oracle : ℕ → ℕ) (code : ℕ) : ℕ := by
  classical
  exact if (run oracle code code).Dom then 1 else 0

theorem no_selfHalting_program (oracle : ℕ → ℕ) :
    ¬ ∃ p : Program, ∀ n : ℕ, eval oracle p n = Part.some (selfHalting oracle n) := by
  classical
  rintro ⟨p, hp⟩
  let d : Program := .comp .guardZero p
  have hd := hp (encode d)
  have heval : eval oracle d (encode d) =
      (if (eval oracle d (encode d)).Dom then Part.none else Part.some 0) := by
    change (eval oracle p (encode d) >>= eval oracle .guardZero) = _
    rw [hd]
    simp only [selfHalting, run_encode]
    split <;> simp [eval]
  by_cases h : (eval oracle d (encode d)).Dom
  · rw [ite_eq_left h] at heval
    rw [heval] at h
    exact h
  · rw [ite_eq_right h] at heval
    apply h
    rw [heval]
    trivial

-- These kernel assertions specify the initial encoding and semantics contract.
example (p : Program) : decode (encode p) = some p := decode_encode p
example (o : ℕ → ℕ) (n : ℕ) : eval o .query n = Part.some (o n) := rfl
example (o : ℕ → ℕ) (n : ℕ) :
    eval o (.comp .query (.prim .succ)) n = Part.some (o (n + 1)) := by
  simp [eval, Nat.Partrec.Code.eval]
example (o : ℕ → ℕ) (n : ℕ) :
    eval o (.pair .query (.prim .succ)) n = Part.some (Nat.pair (o n) (n + 1)) := by
  simp [eval, Nat.Partrec.Code.eval, Seq.seq]
example (o : ℕ → ℕ) : eval o .guardZero 1 = Part.none := rfl
example : decode 7 = none := by rw [decode]; rfl
example : decode 9 = none := by rw [decode]; rfl

#print axioms decode_encode
#print axioms encode_injective
#print axioms mem_eval_find
#print axioms eval_deterministic
#print axioms eval_lt_busyBeaverBits
#print axioms input_eval_lt_busyBeaverBits
#print axioms no_selfHalting_program

end SamAltman.OracleMachine
