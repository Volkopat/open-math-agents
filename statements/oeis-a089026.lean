import Mathlib

/-!
# A089026: a(n) = n if n is a prime, otherwise a(n) = 1.

Source: https://oeis.org/A089026
Credit: @azmiozgen

Conjecture (Thomas Ordowski, Aug 02 2019): for n > 3, a(n) = gcd(n, A007406(n-1)).

Formalization notes:
* A007406(m) is the numerator of the Wolstenholme sum Sum_{k=1..m} 1/k^2 (in lowest terms).
* a(n) is defined exactly as in the name (offset 1).
* Controls: the identity holds for every n from 4 to 69 (checked by evaluation).
-/

namespace OMA.S_oeis_a089026

/-- A089026(n): `n` if `n` is prime, otherwise `1`. -/
def a (n : ℕ) : ℕ := if n.Prime then n else 1

/-- A007406(m): the numerator of `∑_{k=1}^{m} 1/k²`. -/
def wolstenholme (m : ℕ) : ℕ := (∑ k ∈ Finset.Icc 1 m, (1 : ℚ) / (k : ℚ) ^ 2).num.natAbs

/-- Ordowski's conjecture: `a(n) = gcd(n, A007406(n-1))` for `n > 3`. -/
theorem main : ∀ n : ℕ, 3 < n → a n = Nat.gcd n (wolstenholme (n - 1)) := by
  sorry

end OMA.S_oeis_a089026
