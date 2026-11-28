import Mathlib

/-!
# A219433: a(n) is the smallest 3-smooth number such that prime(n)*a(n) + 1 is prime.

Source: https://oeis.org/A219433
Credit: @azmiozgen

Conjecture (from the entry; tested up to a(1000000)): a(n) < prime(n) except for a(522720).

Formalization notes:
* 3-smooth numbers are 2^i * 3^j (i, j ≥ 0); prime(n) = `Nat.nth Nat.Prime (n - 1)` (prime(1) = 2).
* a(n) < prime(n) is stated as the existence of a 3-smooth m < prime(n) with prime(n)*m + 1 prime
  (a(n) is the least such m). The statement covers every n ≥ 1 with n ≠ 522720.
* Controls (computed): a(1..32) = 1, 2, 2, 4, 2, 4, 6, 12, 2, 2, 12, 4, 2, 4, 6, 2, 12, 6, 4, 8, 4, 4,
  2, 2, 4, 6, 6, 6, 24, 2, 4, 2, as in the entry; a(n) < prime(n) for n < 20000.
-/

namespace OMA.S_oeis_a219433

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The conjecture: a 3-smooth `m < prime(n)` with `prime(n) m + 1` prime exists for `n ≠ 522720`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → n ≠ 522720 →
      ∃ i j : ℕ, 2 ^ i * 3 ^ j < prime n ∧ (prime n * (2 ^ i * 3 ^ j) + 1).Prime := by
  sorry

end OMA.S_oeis_a219433
