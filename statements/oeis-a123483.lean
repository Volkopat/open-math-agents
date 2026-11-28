import Mathlib.Data.Finset.Insert

/-!
# OEIS A123483: second-order Recaman coverage conjecture

Sources: https://oeis.org/A123483 and https://oeis.org/A005132
Credit: @hangumm

The generic recurrence starts at zero, remembers every previous value, and
subtracts the prescribed step when the result is positive and unseen.
Otherwise it adds that step. For ordinary Recaman the step at n is n;
for the second-order sequence it is the ordinary Recaman value at n.
Zero is already seen initially, so using a strict-positive test for the
ordinary sequence agrees with its nonnegative-and-unseen convention.

The conjecture asserts that every natural number, including zero, occurs.
This file states the conjecture; it does not prove it.
-/

namespace OMA.S_oeis_a123483

def state (step : ℕ → ℕ) : ℕ → ℕ × Finset ℕ
  | 0 => (0, {0})
  | n + 1 =>
    let s := state step n
    let d := step (n + 1)
    let next := if d < s.1 ∧ s.1 - d ∉ s.2 then s.1 - d else s.1 + d
    (next, insert next s.2)

def recaman (n : ℕ) : ℕ := (state id n).1

def secondOrder (n : ℕ) : ℕ := (state recaman n).1

theorem main : Function.Surjective secondOrder := by
  sorry

end OMA.S_oeis_a123483
