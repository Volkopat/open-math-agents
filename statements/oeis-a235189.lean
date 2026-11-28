import Mathlib

/-!
# A235189: Number of ways to write n = (1 + (n mod 2))*p + q with p < n/2 such that p, q and prime(p) - p + 1 are all prime.

Source: https://oeis.org/A235189
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A235189 (Zhi-Wei Sun, Jan 04 2014):
a(n) > 0 for all n > 6.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 2, 1, ...). `a n` is the number
  of natural numbers p with p < n/2 (written 2*p < n, since n/2 is the exact half), such that
  p, q = n - (1 + (n mod 2))*p and prime(p) - p + 1 are all prime.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed
  (`Nat.nth Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1.
* The natural subtractions are exact: (1 + (n mod 2))*p <= 2*p < n, and prime(p) >= p.
-/

namespace OMA.S_oeis_a235189

/-- A235189: number of p < n/2 with p, n - (1 + n mod 2)*p and prime(p) - p + 1 all prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ | 2 * p < n ∧ p.Prime ∧ (n - (1 + n % 2) * p).Prime ∧
    (Nat.nth Nat.Prime (p - 1) - p + 1).Prime}

/-- The conjecture of Sun: a(n) > 0 for all n > 6. -/
theorem main : ∀ n : ℕ, 6 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a235189
