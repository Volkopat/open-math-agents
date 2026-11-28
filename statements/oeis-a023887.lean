import Mathlib

/-!
# A023887: a(n) = sigma_n(n): sum of n-th powers of divisors of n.

Source: https://oeis.org/A023887
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a023887

/-- A023887: a(n) = sigma_n(n), the sum of the n-th powers of the divisors of n (offset 1).
Mathlib's `ArithmeticFunction.sigma k n` is the sum of the k-th powers of the divisors of n. -/
def a (n : ℕ) : ℕ := ArithmeticFunction.sigma n n

/-- Conjecture (Rayhan Ahmed, Jun 2026): 5 is the only prime in this sequence (a(2) = 5), i.e. a
prime p occurs as a(n) for some n >= 1 if and only if p = 5. -/
theorem main : ∀ p : ℕ, p.Prime → ((∃ n : ℕ, 0 < n ∧ a n = p) ↔ p = 5) := by
  sorry

end OMA.S_oeis_a023887
