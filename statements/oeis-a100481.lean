import Mathlib

/-!
# A100481: greatest prime factor of `n + π(n)`.

Source: https://oeis.org/A100481 (and A095117)
Credit: @cjchaffin

A095117 is `a(n) = π(n) + n`. The present sequence is the greatest prime factor of
that value (with the convention that the term is `1` when `n+π(n) = 1`, which occurs
only at `n = 1`).

Conjecture (on the OEIS page): every prime appears infinitely often in this sequence.

Conventions: offset 1; `π(n)` is `Nat.primeCounting n`. For `m ≥ 2` the greatest
prime factor is `m.primeFactors.sup id`.
-/

namespace OMA.S_oeis_a100481

def largestPrimeFactor (m : ℕ) : ℕ := m.primeFactors.sup id

def a (n : ℕ) : ℕ := largestPrimeFactor (n + Nat.primeCounting n)

theorem main : ∀ p : ℕ, p.Prime → {n : ℕ | 1 ≤ n ∧ a n = p}.Infinite := by
  sorry

end OMA.S_oeis_a100481
