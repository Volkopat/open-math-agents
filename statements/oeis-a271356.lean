import Mathlib

/-!
# Gaps between products of distinct Fibonacci numbers greater than one

Clark Kimberling's conjecture is recorded at https://oeis.org/A271356 and the
underlying increasing sequence at https://oeis.org/A271354. It starts with
6, 10, 15, 16. The first gap, from 6 to 10, is excluded.
-/

namespace OMA.S_oeis_a271356

/-- Products in A271354. The Fibonacci numbers greater than one have indices
starting at three and are strictly increasing from there. -/
def IsProduct (x : ℕ) : Prop :=
  ∃ i j : ℕ, 3 ≤ i ∧ i < j ∧ x = Nat.fib i * Nat.fib j

/-- Every gap after the first is a Fibonacci number. The existence of an earlier
product skips exactly the first gap. -/
theorem main : ∀ x y : ℕ, IsProduct x → IsProduct y → x < y →
    (∃ u : ℕ, IsProduct u ∧ u < x) →
    (∀ z : ℕ, x < z → z < y → ¬ IsProduct z) →
    ∃ k : ℕ, y - x = Nat.fib k := by
  sorry

end OMA.S_oeis_a271356
