import Mathlib

/-!
# Serov's two formulas for OEIS A023900

Source: https://oeis.org/A023900
Credit: @Heart-galaxy

The sequence is represented by the divisor sum of `d * μ d`, as in the source
and Sela Fried's proof (2025), https://oeis.org/A023900/a023900.pdf, Theorem 1.
The parameter `m` is the odd part specified by the factorization `n = 2 ^ t * m`.
-/

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace OMA.S_oeis_a023900

/-- OEIS A023900 as a weighted Möbius divisor sum. -/
def a (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (d : ℤ) * μ d

/-- The summand in Serov's two formulas. -/
def term (m i : ℕ) : ℤ := 4 * (min i (m - i) : ℕ) - (m : ℤ)

/-- Both of Serov's expressions for A023900 using the odd part of the index. -/
theorem main : ∀ n t m : ℕ, 1 < n → Odd m → n = 2 ^ t * m →
    (a n = (if m = n then -1 else 1) *
      ∑ i ∈ (Finset.Icc 1 m).filter (fun i => i.gcd m = 1), term m i) ∧
    (a n = (if m < n then -1 else 1) *
      (1 + ∑ i ∈ (Finset.Icc 1 m).filter (fun i => 1 < i.gcd m), term m i)) := by
  sorry

end OMA.S_oeis_a023900
