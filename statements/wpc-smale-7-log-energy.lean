import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OMA.S_wpc_smale_7_log_energy

open scoped BigOperators

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Primitive instructions of an exact real machine. Register addresses are fixed
offsets from the current origin, which the shift instruction can move by one cell. -/
inductive Instruction (q : ℕ) where
  | constant (destination : ℤ) (value : ℝ) (next : Fin (q + 1))
  | copy (destination source : ℤ) (next : Fin (q + 1))
  | add (destination left right : ℤ) (next : Fin (q + 1))
  | sub (destination left right : ℤ) (next : Fin (q + 1))
  | mul (destination left right : ℤ) (next : Fin (q + 1))
  | div (destination numerator denominator : ℤ) (next : Fin (q + 1))
  | test (source : ℤ) (ifNegative ifNonnegative : Fin (q + 1))
  | shift (right : Bool) (next : Fin (q + 1))
  | halt

abbrev Program (q : ℕ) := Fin (q + 1) → Instruction q

structure State (q : ℕ) where
  pc : Fin (q + 1)
  cells : ℤ → ℝ

/-- One unit-cost step. Division by zero has no valid successor. -/
noncomputable def step {q : ℕ} (program : Program q) (s : State q) : Option (State q) :=
  let write (destination : ℤ) (value : ℝ) (next : Fin (q + 1)) : Option (State q) :=
    some ⟨next, Function.update s.cells destination value⟩
  match program s.pc with
  | .constant destination value next => write destination value next
  | .copy destination source next => write destination (s.cells source) next
  | .add destination left right next => write destination (s.cells left + s.cells right) next
  | .sub destination left right next => write destination (s.cells left - s.cells right) next
  | .mul destination left right next => write destination (s.cells left * s.cells right) next
  | .div destination numerator denominator next =>
    if s.cells denominator = 0 then none
    else write destination (s.cells numerator / s.cells denominator) next
  | .test source ifNegative ifNonnegative =>
    some ⟨if s.cells source < 0 then ifNegative else ifNonnegative, s.cells⟩
  | .shift right next => some ⟨next, fun i => s.cells (i + (if right then 1 else -1))⟩
  | .halt => none

/-- The input is stored in register zero and all other cells start at zero. -/
noncomputable def initialState (q N : ℕ) : State q :=
  ⟨0, fun i => if i = 0 then (N : ℝ) else 0⟩

/-- A finite execution terminating at a halt instruction with a packed coordinate output. -/
def Computes {q N : ℕ} (program : Program q) (steps : ℕ) (points : Fin N → Space) : Prop :=
  ∃ trace : Fin (steps + 1) → State q,
    trace 0 = initialState q N ∧
    (∀ i : Fin steps, step program (trace i.castSucc) = some (trace i.succ)) ∧
    let last := trace (Fin.last steps)
    program last.pc = .halt ∧
    ∀ (i : Fin N) (j : Fin 3),
      points i j = last.cells (Int.ofNat (1 + 3 * i.val + j.val))

def IsConfiguration {N : ℕ} (points : Fin N → Space) : Prop :=
  Function.Injective points ∧ ∀ i, ‖points i‖ = 1

/-- Logarithmic energy with each unordered pair counted once. -/
noncomputable def logarithmicEnergy {N : ℕ} (points : Fin N → Space) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
    -Real.log (dist (points i) (points j))

/-- Smale's seventh problem in the exact real computation model. -/
theorem main :
    ∃ (q : ℕ) (program : Program q) (coefficient degree : ℕ) (c : ℝ), 0 < c ∧
      ∀ N : ℕ, 0 < N →
        ∃ (steps : ℕ) (points : Fin N → Space),
          steps ≤ coefficient * N ^ degree ∧
          Computes program steps points ∧
          IsConfiguration points ∧
          ∀ comparison : Fin N → Space, IsConfiguration comparison →
            logarithmicEnergy points ≤ logarithmicEnergy comparison + c * Real.log (N : ℝ) := by
  sorry

end OMA.S_wpc_smale_7_log_energy
