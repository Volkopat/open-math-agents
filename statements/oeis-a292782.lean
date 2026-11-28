import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity

/-!
# Two divisibilities for A292782

Vladimir Shevelev's sequence is E(2n,n)/2 with the Euler-polynomial
convention of the entry. Its independently listed finite alternating
power sum defines the same integer for n≥1. The k=0 summand vanishes
in this range. The divisors below are natural numbers cast to integers.

Source: https://oeis.org/A292782 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a292782

def a (n : ℕ) : ℤ :=
  (-1) ^ (n + 1) * ∑ k ∈ Finset.range n, (-1 : ℤ) ^ k * (k : ℤ) ^ (2 * n)

theorem main : ∀ n : ℕ, 2 ≤ n →
    (((n * (n - 1) / 2 : ℕ) : ℤ) ∣ a n) ∧
    (Odd n → ((n ^ 2 * (n - 1) / 2 : ℕ) : ℤ) ∣ a n) := by
  sorry

end OMA.S_oeis_a292782
