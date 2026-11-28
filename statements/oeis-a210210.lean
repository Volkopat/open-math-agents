import Mathlib

/-!
# A210210: Least number k among 1, ..., n such that pi(p+2*n) - pi(p+n) = pi(p+n) - pi(p) > 0 with p = prime(k), or 0 if such a number k does not exist, where pi(.) is given by A000720.

Source: https://oeis.org/A210210
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) > 0 for all n > 1.

Formalization notes:
* pi = `Nat.primeCounting`, prime(k) = `Nat.nth Nat.Prime (k - 1)`. a(n) > 0 is the existence of such
  a k in 1..n.
* Controls (computed): a(1..30) = 0, 1, 2, 4, 2, 2, 4, 1, 2, 3, 3, 6, 2, 9, 4, 6, 7, 4, 4, 6, 3, 3, 3, 5,
  2, 6, 4, 4, 4, 8, as in the entry; a(n) > 0 for 1 < n < 1500.
-/

namespace OMA.S_oeis_a210210

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 1 < n → ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
      Nat.primeCounting (prime k + 2 * n) - Nat.primeCounting (prime k + n) =
        Nat.primeCounting (prime k + n) - Nat.primeCounting (prime k) ∧
      0 < Nat.primeCounting (prime k + n) - Nat.primeCounting (prime k) := by
  sorry

end OMA.S_oeis_a210210
