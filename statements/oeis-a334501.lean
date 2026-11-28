import Mathlib.Init

/-!
# OEIS A334501, Rule 190 on a finite ring

Source: https://oeis.org/A334501. Conjectures by Colin Barker (2020).
Credit: @garrytaulu
Prior classification and counterexamples: https://github.com/kinoyu-ai/rule190-period

At time zero just cell zero is ON. On a ring of positive width, a state is a
nonnegative integer whose low n bits are the cells. The local rule has one
exactly when the right neighbor is one or the left and center bits differ:
this gives Wolfram bits 10111110, or decimal 190. The observed cell is zero.
-/
namespace OMA.S_oeis_a334501

def step (n s : Nat) : Nat :=
  let left := (2 * s) % (2^n) + s / (2^(n-1))
  let right := s / 2 + (s % 2) * (2^(n-1))
  (left ^^^ s) ||| right

def state (n : Nat) : Nat → Nat
  | 0 => 1
  | t + 1 => step n (state n t)

def bit (n t : Nat) : Nat := state n t % 2

def Eventual (n p : Nat) : Prop :=
  0 < p ∧ ∃ start, ∀ t, start ≤ t → bit n (t + p) = bit n t

def Fundamental (n p : Nat) : Prop :=
  Eventual n p ∧ ∀ q, Eventual n q → p ≤ q

/-- Offset one, with zero constant coefficient for the generating function. -/
noncomputable def a (n : Nat) : Nat := by
  classical
  exact if n = 0 then 0 else if h : ∃ p, Fundamental n p then Classical.choose h else 0

def recurrence : Prop :=
  ∀ n : Nat, 8 < n → (a n : Int) = 2 * (a (n-4) : Int) - (a (n-8) : Int)

/-- Coefficients of the numerator exactly as given in OEIS, including its leading x. -/
def numerator : Nat → Int
  | 1 | 2 | 3 => 1
  | 4 => 4
  | 5 => 3
  | 6 => 4
  | 7 => 5
  | 8 => -4
  | 10 => -1
  | 11 => -2
  | _ => 0

/-- Formal generating-series equality, expressed coefficient by coefficient.
The given denominator (1-x)^2(1+x)^2(1+x^2)^2 equals (1-x^4)^2.
A negative index contributes zero. -/
def generatingFunction : Prop :=
  ∀ n : Nat, (a n : Int) - 2 * (if 4 ≤ n then (a (n-4) : Int) else 0)
    + (if 8 ≤ n then (a (n-8) : Int) else 0) = numerator n

theorem main : generatingFunction ∧ recurrence := by
  sorry

end OMA.S_oeis_a334501
