import Mathlib

/-!
# Hartmanis–Stearns conjecture

Source: https://en.wikipedia.org/wiki/Hartmanis–Stearns_conjecture
Credit: @PipeCruz

The source states: if x is a real number whose expansion in some base b ≥ 2 is real-time
computable, then x is rational or transcendental. An infinite word is real-time computable when
there exists a multitape Turing machine which, run without input, writes the successive letters
of the word on its output tape, taking a bounded amount of time between two successive letters.

Modelling choices (standard readings; the source does not fix these details):
* A machine has `k` work tapes, `s` states (`Fin s`) and the tape alphabet `Fin (g + 1)`, with
  `0` as the blank. It reads no input: every tape starts blank, every head at cell `0`.
  At each step it reads the `k` scanned symbols, then changes state, writes on every tape, moves
  every head one cell left or right, and may append one letter to its write-only output tape
  (`Option α`). `k = 0` is allowed (finite-state output), which only enlarges the hypothesis
  class consistently with the source, since more tapes can simulate fewer.
* The word `w` is real-time computable when the letters are output at increasing times `t n`, the
  first within `C` steps and each next one within `C` steps of the previous, for one constant `C`,
  and nothing else is output.
* The base-`b` expansion of `x` is taken to be the digit word of its fractional part,
  `Int.fract x = ∑ w n / b ^ (n + 1)`. The integer part is a finite prefix: adding or removing it
  does not change real-time computability, and it does not change whether `x` is rational or
  transcendental. Either expansion of a number with two expansions is allowed.
-/

namespace OMA.S_wp_hartmanis_stearns_conjecture

/-- A multitape Turing machine with no input, `k` work tapes, `s` states, tape alphabet
`Fin (g + 1)` (blank `0`) and output alphabet `α`. -/
structure Machine (k s g : ℕ) (α : Type) where
  start : Fin s
  δ : Fin s → (Fin k → Fin (g + 1)) →
    Fin s × (Fin k → Fin (g + 1) × Turing.Dir) × Option α

/-- A configuration: current state, contents of the work tapes, positions of the heads. -/
structure Config (k s g : ℕ) where
  state : Fin s
  tape : Fin k → ℤ → Fin (g + 1)
  head : Fin k → ℤ

variable {k s g : ℕ} {α : Type}

/-- Head displacement. -/
def move : Turing.Dir → ℤ
  | Turing.Dir.left => -1
  | Turing.Dir.right => 1

/-- Run without input: all tapes blank, all heads at cell `0`. -/
def Machine.init (M : Machine k s g α) : Config k s g :=
  ⟨M.start, fun _ _ => 0, fun _ => 0⟩

/-- The transition taken from configuration `c`. -/
def Machine.transition (M : Machine k s g α) (c : Config k s g) :
    Fin s × (Fin k → Fin (g + 1) × Turing.Dir) × Option α :=
  M.δ c.state (fun i => c.tape i (c.head i))

/-- One step of the machine. -/
def Machine.next (M : Machine k s g α) (c : Config k s g) : Config k s g :=
  { state := (M.transition c).1
    tape := fun i => Function.update (c.tape i) (c.head i) ((M.transition c).2.1 i).1
    head := fun i => c.head i + move ((M.transition c).2.1 i).2 }

/-- The configuration after `n` steps. -/
def Machine.config (M : Machine k s g α) (n : ℕ) : Config k s g :=
  M.next^[n] M.init

/-- The letter (if any) appended to the output tape during step `n`. -/
def Machine.output (M : Machine k s g α) (n : ℕ) : Option α :=
  (M.transition (M.config n)).2.2

/-- An infinite word is real-time computable: some multitape Turing machine, run without input,
outputs exactly its successive letters, with a bounded number of steps before the first letter and
between any two successive letters. -/
def RealTimeComputable (w : ℕ → α) : Prop :=
  ∃ (k s g : ℕ) (M : Machine k s g α) (C : ℕ) (t : ℕ → ℕ),
    StrictMono t ∧ t 0 ≤ C ∧ (∀ n, t (n + 1) ≤ t n + C) ∧
    (∀ n, M.output (t n) = some (w n)) ∧
    (∀ m, (M.output m).isSome → m ∈ Set.range t)

/-- **Hartmanis–Stearns conjecture.** If the base-`b` expansion (`b ≥ 2`) of a real number `x` is
real-time computable, then `x` is rational or transcendental. -/
theorem main : ∀ (b : ℕ), 2 ≤ b → ∀ (x : ℝ) (w : ℕ → Fin b), RealTimeComputable w →
    Int.fract x = ∑' n : ℕ, ((w n : ℕ) : ℝ) / (b : ℝ) ^ (n + 1) →
    (∃ q : ℚ, (q : ℝ) = x) ∨ Transcendental ℚ x := by
  sorry

end OMA.S_wp_hartmanis_stearns_conjecture
