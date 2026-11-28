import Mathlib

/-!
# A059324: Numbers n such that 6n + 5 is composite.

Source: https://oeis.org/A059324
Credit: @agchua

Comment of A059324 (Philippe Lallouet, Mar 20 2008):
  Conjecture: There exists no pair of primes (p, q > p^2) such that q - p^2 = 6*n - 4 (see
  A138479).
Offset 1; the terms are the natural numbers n with 6n + 5 composite (5, 10, 12, 15, 19, ...).
The claim is stated for every term n, with the difference q - p^2 taken in the integers.
-/

namespace OMA.S_oeis_a059324

/-- n is a term of A059324: 6n + 5 is composite. -/
def IsTerm (n : ℕ) : Prop := 1 < 6 * n + 5 ∧ ¬ (6 * n + 5).Prime

/-- The conjecture: for every term n there are no primes p, q with q > p^2 and
q - p^2 = 6n - 4. -/
theorem main : ∀ n : ℕ, IsTerm n → ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ^ 2 < q ∧
    (q : ℤ) - (p : ℤ) ^ 2 = 6 * (n : ℤ) - 4 := by
  sorry

end OMA.S_oeis_a059324
