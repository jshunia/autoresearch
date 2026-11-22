import Mathlib

/-! Mathematical specifications from the PrimeSLPs and PolynomialCircuits manuscripts.
The open assertions below are types. The named theorems check examples of their definitions. -/

namespace ProofGraph.PrimeCircuitQuestions

/-! Fixed straight-line programs. A register holds the result of one earlier instruction.
Indices count from the most recently written register, starting at zero. -/

inductive Operand (arity : ℕ) where
  | arg (i : Fin arity)
  | lit (x : ℕ)
  | reg (i : ℕ)

def Operand.read {k : ℕ} (xs : Fin k → ℕ) (rs : List ℕ) : Operand k → Option ℕ
  | .arg i => some (xs i)
  | .lit x => some x
  | .reg i => rs[i]?

inductive BinaryGate where
  | add | sub | mul | div | rem | pow | band

def BinaryGate.apply : BinaryGate → ℕ → ℕ → Option ℕ
  | .add, a, b => some (a + b)
  | .sub, a, b => if b ≤ a then some (a - b) else none
  | .mul, a, b => some (a * b)
  | .div, a, b => if 0 < b then some (a / b) else none
  | .rem, a, b => if 0 < b then some (a % b) else none
  | .pow, a, b => some (a ^ b)
  | .band, a, b => some (a &&& b)

inductive Instruction (arity : ℕ) where
  | binary (op : BinaryGate) (a b : Operand arity)
  | logWidth (a : Operand arity)

structure Program (arity : ℕ) where
  gates : List (Instruction arity)
  result : Operand arity

/-- Each operand and the unreduced output of every instruction contribute to peak width.
The width language additionally admits a floor binary logarithm on a positive argument. -/
def Instruction.step {k : ℕ} (allowLog : Bool) (xs : Fin k → ℕ)
    (state : List ℕ × ℕ) (instr : Instruction k) : Option (List ℕ × ℕ) := do
  let (rs, peak) := state
  match instr with
  | .binary op x y =>
    let a ← x.read xs rs
    let b ← y.read xs rs
    let z ← op.apply a b
    return (z :: rs, max peak (max a.size (max b.size z.size)))
  | .logWidth x =>
    let a ← x.read xs rs
    if allowLog && decide (0 < a) then
      let z := Nat.log2 a
      return (z :: rs, max peak (max a.size z.size))
    else failure

def Program.run {k : ℕ} (p : Program k) (allowLog : Bool) (xs : Fin k → ℕ) :
    Option (ℕ × ℕ) := do
  let init := Finset.univ.sup fun i => (xs i).size
  let (rs, peak) ← p.gates.foldlM (Instruction.step allowLog xs) ([], init)
  let y ← p.result.read xs rs
  return (y, max peak y.size)

def PrimeOutput (p : Program 1) (allowLog : Bool) : Prop :=
  ∀ j : ℕ, ∃ bits, p.run allowLog (fun _ => j + 1) = some (Nat.nth Nat.Prime j, bits)

def NineteenGates : Prop := ∃ p : Program 1, p.gates.length ≤ 19 ∧ PrimeOutput p false

/-- Raising to integer powers expresses the eventual bound bits ≤ n^(1/2 + 1/t).
The same program works for every t. -/
def PrimeWidthEndpoint : Prop :=
  ∃ p : Program 1, PrimeOutput p true ∧ ∀ t : ℕ, 0 < t → ∃ N : ℕ, ∀ n ≥ N, 0 < n →
    ∃ y bits, p.run true (fun _ => n) = some (y, bits) ∧ bits ^ (2*t) ≤ n ^ (t+2)

/-- The register schedule of nth_prime_tilted in PrimeSLPs/prime_composition_slp.py. -/
def tiltedSchedule : Program 1 :=
  ⟨
   [.binary .pow (.lit 4) (.arg 0), -- scale
    .binary .pow (.lit 4) (.reg 0), -- exponent
    .binary .sub (.reg 1) (.lit 1), -- width
    .binary .mul (.reg 1) (.reg 0), -- band
    .binary .pow (.lit 4) (.reg 2), -- base
    .binary .pow (.reg 0) (.reg 1), -- row
    .binary .pow (.reg 0) (.arg 0), -- extent
    .binary .sub (.reg 2) (.lit 1), -- digit_mod
    .binary .div (.reg 1) (.reg 0), -- units
    .binary .pow (.reg 4) (.lit 3), -- cube
    .binary .sub (.reg 4) (.reg 0), -- fold_mod
    .binary .div (.reg 5) (.reg 10), -- three
    .binary .add (.reg 0) (.reg 7), -- letters
    .binary .add (.reg 0) (.lit 1), -- source
    .binary .pow (.reg 0) (.reg 12), -- expansion
    .binary .div (.reg 9) (.reg 10), -- drop
    .binary .div (.reg 1) (.reg 0), -- interior
    .binary .mul (.reg 13) (.reg 8), -- mask
    .binary .band (.reg 1) (.reg 0), -- witnesses
    .binary .rem (.reg 0) (.reg 8), -- sums
    .binary .sub (.reg 11) (.reg 0), -- signs
    .binary .band (.reg 0) (.reg 12), -- flags
    .binary .sub (.reg 0) (.arg 0), -- offset
    .binary .mul (.lit 2) (.reg 0), -- doubled
    .binary .mul (.reg 0) (.reg 15), -- counts
    .binary .sub (.reg 0) (.lit 1), -- seeded
    .binary .band (.reg 0) (.reg 17), -- selected
    .binary .rem (.reg 0) (.reg 19)], -- prime
    .reg 0⟩

theorem tilted_gate_count : tiltedSchedule.gates.length = 28 := rfl

def squareAndDouble : Program 1 :=
  ⟨[.binary .mul (.arg 0) (.arg 0), .binary .add (.reg 0) (.reg 0)], .reg 0⟩

theorem shared_square_at_three :
    squareAndDouble.gates.length = 2 ∧ squareAndDouble.run false (fun _ => 3) = some (18, 5) := by
  decide

theorem invalid_gates_fail :
    BinaryGate.sub.apply 2 3 = none ∧ BinaryGate.div.apply 3 0 = none ∧
    BinaryGate.rem.apply 3 0 = none ∧ (Operand.reg 0 : Operand 1).read (fun _ => 7) [] = none := by
  decide

theorem power_before_remainder :
    (Program.mk [.binary .pow (.lit 2) (.arg 0), .binary .rem (.reg 0) (.lit 3)]
      (.reg 0) : Program 1).run false (fun _ => 10) = some (1, 11) := by decide

/-! One concrete sparse-assembly task. A leading base digit 1 preserves even a string of
zero fields. Keys and payloads have independent field widths. Repeated keys are allowed. -/

def packFields (base n : ℕ) (digit : Fin n → ℕ) : ℕ :=
  base ^ n + ∑ i, digit i * base ^ (i : ℕ)

def scatterValue (b : ℕ) {n : ℕ} (key payload : Fin n → ℕ) : ℕ :=
  ∑ i, payload i * b ^ key i

def scatterInputs (n k w : ℕ) (key payload : Fin n → ℕ) : Fin 5 → ℕ :=
  ![n, k, w, packFields (2^k) n key, packFields (2^w) n payload]

def ScatterFits (n k w : ℕ) (key payload : Fin n → ℕ) : Prop :=
  0 < k ∧ 0 < w ∧ (∀ i, key i < 2^k ∧ payload i < 2^w) ∧
    ∀ j : ℕ, (∑ i, if key i = j then payload i else 0) < 2^w

/-- Ordinary binary input lengths plus the exact output length; the sentinel charges padding. -/
def scatterSize (xs : Fin 5 → ℕ) (y : ℕ) : ℕ := 1 + (∑ i, (xs i).size) + y.size

def NearLinearScatter : Prop :=
  ∃ p : Program 5,
    (∀ n k w (key payload : Fin n → ℕ), ScatterFits n k w key payload →
      ∃ bits, p.run true (scatterInputs n k w key payload) =
        some (scatterValue (2^w) key payload, bits)) ∧
    ∀ t : ℕ, 0 < t → ∃ N : ℕ, ∀ n k w (key payload : Fin n → ℕ),
      ScatterFits n k w key payload →
      let xs := scatterInputs n k w key payload
      let y := scatterValue (2^w) key payload
      let s := scatterSize xs y
      N ≤ s → ∃ bits, p.run true xs = some (y, bits) ∧ bits ^ t ≤ s ^ (t+1)

theorem scatter_repeated_key :
    scatterValue 8 ![1, 0, 1] ![2, 4, 3] = 44 ∧
    packFields 2 3 ![1, 0, 1] = 13 ∧ packFields 8 3 ![2, 4, 3] = 738 := by decide

/-! The three optimizers use the same feasible set. Numeric order on a fixed-width word
is lexicographic order when the most significant bit is read first. -/

def weight (a : ℕ) : ℕ := a.bits.count true

def CarryFree (a x : ℕ) : Prop := weight (a*x) = weight a * weight x

instance (a x : ℕ) : Decidable (CarryFree a x) := inferInstanceAs (Decidable (_ = _))

def feasibleWords (a : ℕ) : List ℕ := (List.range (2^a.size)).filter (fun x => decide (CarryFree a x))

def largestWord (a : ℕ) : ℕ := (feasibleWords a).foldl max 0

def maximumWeight (a : ℕ) : ℕ := (feasibleWords a).foldl (fun v x => max v (weight x)) 0

/-- A heavier word wins. Equal weights are ordered by the numerical word itself. -/
def preferWord (u v : ℕ) : ℕ :=
  if weight u < weight v ∨ (weight u = weight v ∧ u ≤ v) then v else u

def greatestOptimum (a : ℕ) : ℕ := (feasibleWords a).foldl preferWord 0

private theorem preferWord_weight (u v : ℕ) :
    weight (preferWord u v) = max (weight u) (weight v) := by
  unfold preferWord
  split
  · rename_i h
    exact (max_eq_right (by omega)).symm
  · rename_i h
    exact (max_eq_left (by omega)).symm

private theorem fold_preferWord_weight (xs : List ℕ) (u : ℕ) :
    weight (xs.foldl preferWord u) = xs.foldl (fun m x => max m (weight x)) (weight u) := by
  induction xs generalizing u with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, ih, preferWord_weight]

theorem greatestOptimum_weight (a : ℕ) : weight (greatestOptimum a) = maximumWeight a :=
  fold_preferWord_weight (feasibleWords a) 0

/-- Exactly the fixed-composition modular basis in Arithmetic Terms for FP. -/
inductive ModularTerm where
  | input
  | lit (n : ℕ)
  | add (a b : ModularTerm)
  | div (a b : ModularTerm)
  | band (a b : ModularTerm)
  | smash (a b : ModularTerm)
  | modPow (a e m : ModularTerm)
  | gcd (a b : ModularTerm)
  | invMod (a m : ModularTerm)

def ModularTerm.eval (x : ℕ) : ModularTerm → ℕ
  | .input => x
  | .lit n => n
  | .add a b => a.eval x + b.eval x
  | .div a b => a.eval x / b.eval x
  | .band a b => a.eval x &&& b.eval x
  | .smash a b => 2 ^ ((a.eval x).size * (b.eval x).size)
  | .modPow a e m => if m.eval x = 0 then 0 else (a.eval x) ^ (e.eval x) % (m.eval x)
  | .gcd a b => (a.eval x).gcd (b.eval x)
  | .invMod a m =>
    let v := a.eval x
    let d := m.eval x
    if 1 < d ∧ v.Coprime d then (Nat.gcdA v d % (d : ℤ)).toNat else 0

def ModularPredecessor : Prop := ∃ t : ModularTerm, ∀ a, t.eval a = largestWord a

theorem modular_basis_examples :
    (ModularTerm.invMod .input (.lit 11)).eval 3 = 4 ∧
    (ModularTerm.invMod .input (.lit 6)).eval 3 = 0 ∧
    (ModularTerm.modPow .input (.lit 5) (.lit 0)).eval 3 = 0 ∧
    (ModularTerm.smash .input (.lit 2)).eval 3 = 16 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2400000 in
theorem three_optima_at_seventy :
    largestWord 70 = 80 ∧ maximumWeight 70 = 3 ∧ greatestOptimum 70 = 73 := by decide

/-! Deterministic polynomial bit time, with a finite alphabet on every mathlib TM2 stack.
Inputs and outputs are binary words. The machine, alphabets and time polynomial are fixed. -/

def BinaryPoly {α β : Type} (encA : α → List Bool) (encB : β → List Bool) (f : α → β) : Prop :=
  ∃ m : Turing.TM2ComputableInPolyTime encA encB f, ∀ k, Finite (m.tm.Γ k)

def WeightInFP : Prop := BinaryPoly Computability.encodeNat Computability.encodeNat maximumWeight

def StrictPrimeInFP : Prop :=
  ∃ f : ℕ → ℕ, BinaryPoly Computability.encodeNat Computability.encodeNat f ∧
    ∀ n, IsLeast {p : ℕ | n < p ∧ p.Prime} (f n)

theorem binary_identity : BinaryPoly Computability.encodeNat Computability.encodeNat id :=
  ⟨Turing.idComputableInPolyTime _, fun _ => inferInstanceAs (Finite Bool)⟩

theorem strict_successor_at_thirteen : IsLeast {p : ℕ | 13 < p ∧ p.Prime} 17 := by
  constructor
  · change 13 < 17 ∧ Nat.Prime 17
    norm_num
  · intro p hp
    change 13 < p ∧ p.Prime at hp
    by_contra! h
    obtain rfl | rfl | rfl : p = 14 ∨ p = 15 ∨ p = 16 := by omega
    all_goals norm_num at hp

/-- A clause consists of its positive and negative variable masks. The first variable
is the highest assignment bit. An empty clause is false and an empty conjunction true. -/
structure Formula where
  varCount : ℕ
  clauses : List (ℕ × ℕ)

def Formula.valid (f : Formula) : Prop :=
  ∀ c ∈ f.clauses, c.1 < 2^f.varCount ∧ c.2 < 2^f.varCount

def Formula.accepts (f : Formula) (x : ℕ) : Bool :=
  f.clauses.all fun (pos, neg) => (x &&& pos) != 0 || (x &&& neg) != neg

def Formula.satisfiable (f : Formula) : Prop :=
  ∃ x < 2^f.varCount, f.accepts x = true

def Formula.greatestAssignment (f : Formula) : ℕ :=
  ((List.range (2^f.varCount)).filter f.accepts).foldl max 0

def frame (w : List Bool) : List Bool := List.replicate w.length true ++ [false] ++ w

def Formula.encode (f : Formula) : List Bool :=
  List.replicate f.varCount true ++ [false] ++ f.clauses.flatMap fun (p, n) =>
    frame (Computability.encodeNat p) ++ frame (Computability.encodeNat n)

def decodeInput (v : Formula × ℕ) : List Bool := frame v.1.encode ++ Computability.encodeNat v.2

/-- A polynomial-time metric reduction. The decoder sees the formula and the result of
one query to the canonical optimum T. Its behavior on unsatisfiable inputs is unrestricted. -/
def OneCallLexSAT : Prop :=
  ∃ (build : Formula → ℕ) (read : Formula × ℕ → ℕ),
    BinaryPoly Formula.encode Computability.encodeNat build ∧
    BinaryPoly decodeInput Computability.encodeNat read ∧
    ∀ f, f.valid → f.satisfiable →
      read (f, greatestOptimum (build f)) = f.greatestAssignment

theorem two_variable_lex_order :
    (Formula.mk 2 [(3, 0), (0, 3)]).greatestAssignment = 2 ∧
    (Formula.mk 2 [(3, 0), (0, 3)]).accepts 1 = true ∧
    (Formula.mk 2 [(3, 0), (0, 3)]).accepts 3 = false := by decide

/-! A single integer polynomial and a fixed auxiliary arity for all binary containments.
Uniqueness and exclusion of false instances range over every natural tuple. -/

def IsRoot {k : ℕ} (p : MvPolynomial (Fin 2 ⊕ Fin k) ℤ) (x y : ℕ) (w : Fin k → ℕ) : Prop :=
  MvPolynomial.eval (Sum.elim (fun i => if i = 0 then (x : ℤ) else (y : ℤ))
    (fun i => (w i : ℤ))) p = 0

def ShortSingleFoldContainment : Prop :=
  ∃ (k : ℕ) (p : MvPolynomial (Fin 2 ⊕ Fin k) ℤ) (c d : ℕ), ∀ x y : ℕ,
    ((x &&& y = x) ↔ ∃ w, IsRoot p x y w) ∧
    (∀ u v, IsRoot p x y u → IsRoot p x y v → u = v) ∧
    (∀ w, IsRoot p x y w → 1 + (∑ i, (w i).size) ≤ c * (2 + x.size + y.size)^d)

theorem containment_examples : (5 &&& 13) = 5 ∧ (6 &&& 13) ≠ 6 := by decide

end ProofGraph.PrimeCircuitQuestions
