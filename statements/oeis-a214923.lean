import Mathlib

/-!
# A214923: Binary digit balance in the Fibonacci sequence

Source: https://oeis.org/A214923
Formalization: @pyaf

The initial Fibonacci number is written as a single zero digit.
-/

namespace OMA.S_oeis_a214923

def balance (x : ℕ) : ℤ :=
  if x = 0 then -1 else
    let digits := Nat.digits 2 x
    (digits.count 1 : ℤ) - (digits.count 0 : ℤ)

def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), balance (Nat.fib k)

theorem main : {n : ℕ | 0 < a n}.Infinite ∧ {n : ℕ | a n < 0}.Infinite := by
  sorry

end OMA.S_oeis_a214923
