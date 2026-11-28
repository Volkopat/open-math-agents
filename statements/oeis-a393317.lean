import Mathlib

/-!
# Worst-case runtimes of the two-state, two-symbol Wolfram machines

M. F. Hasler's conjectures in OEIS A393317, indexed from n = 1.
The transition digits and one-sided binary tape follow the Wolfram Institute
implementation. The transition that leaves the tape counts toward runtime.

Sources: https://oeis.org/A393317 and
https://github.com/WolframInstitute/TuringMachine/blob/main/TuringMachine/Libs/ndtm_search/src/models.rs.
Credit: @marcelopierry
-/

namespace OMA.S_oeis_a393317

structure Config where
  stateB : Bool
  lower : List Bool
  high : ℕ

/-- Move outward after writing, halting when the lower stack is empty. -/
def outward (stateB : Bool) (high : ℕ) : List Bool → Option Config
  | [] => none
  | bit :: lower => some ⟨stateB, lower, 2*high+bit.toNat⟩

/-- The rule number has one octal digit per state and read symbol.
From most to least significant these are A1, A0, B1, B0. From most to least
significant the three bits specify next state, written symbol and direction. -/
def step (rule : ℕ) (c : Config) : Option Config :=
  let read := c.high % 2
  let index := (if c.stateB then 0 else 2) + read
  let digit := rule / 8^index % 8
  let stateB := decide (4 ≤ digit)
  let written := decide (2 ≤ digit%4)
  if digit % 2 = 1 then outward stateB (2*(c.high/2)+written.toNat) c.lower
  else some ⟨stateB, written :: c.lower, c.high/2⟩

/-- An exact run cannot take another transition after it has halted. -/
inductive Runs (rule : ℕ) : Config → ℕ → Option Config → Prop where
  | one (c) : Runs rule c 1 (step rule c)
  | more {c d t z} : step rule c = some d → Runs rule d t z → Runs rule c (t+1) z

/-- The source program counts zero as a one-bit input. -/
def fits (n input : ℕ) : Prop := (n=1 ∨ 2^(n-1) ≤ input) ∧ input < 2^n

/-- The all-ones input attains the stated maximum for this individual machine. -/
def allOnesWorst (rule n t : ℕ) : Prop :=
  Runs rule ⟨false,[],2^n-1⟩ t none ∧
  ∀ input, fits n input → ∀ k, Runs rule ⟨false,[],input⟩ k none → k ≤ t

/-- Only halting computations contribute a time to this set. -/
def haltingTimes (n : ℕ) : Set ℕ :=
  {k | ∃ rule < 4096, ∃ input, fits n input ∧ Runs rule ⟨false,[],input⟩ k none}

theorem main : ∀ n : ℕ, 0 < n →
    allOnesWorst 378 n (2^(n+2)-3) ∧
    allOnesWorst 1351 n (2^(n+2)-3) ∧
    allOnesWorst 1447 n (2*(n+2)^2-1) ∧
    IsGreatest (haltingTimes n) (if n < 5 then 2*(n+2)^2-1 else 2^(n+2)-3) := by
  sorry

end OMA.S_oeis_a393317
