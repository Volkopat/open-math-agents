import Mathlib

/-!
# A215642: Primes p such that there is no D such that p+D, p-D, p+2*D, p-2*D are all primes.

Source: https://oeis.org/A215642
Credit: @darealpandaboi

Conjecture: a(243) = 34613 is the last term.

Translation notes.
* D ranges over positive integers; p - 2D must be a prime, so 2D < p and the subtraction is
  exact.
* 34613 is the last term is stated as: every prime p > 34613 has some D > 0 with
  p + D, p - D, p + 2D and p - 2D all prime.
* This reading reproduces the listed data: 2, 3, 5, 7, 11, 13, 19, 23, 31, 37, ...; below 40000
  there are exactly 243 terms and the last is 34613 (checked by computer).
-/

namespace OMA.S_oeis_a215642

theorem main : ∀ p : ℕ, p.Prime → 34613 < p → ∃ D : ℕ, 0 < D ∧ 2 * D < p ∧
    (p + D).Prime ∧ (p - D).Prime ∧ (p + 2 * D).Prime ∧ (p - 2 * D).Prime := by
  sorry

end OMA.S_oeis_a215642
