import Mathlib

/-!
# A237598: a(n) = |{0 < k < prime(n): pi(k*n) is a square}|, where pi(.) is given by A000720.

Source: https://oeis.org/A237598
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 0.
(ii) For each n > 9, there is a positive integer k < prime(n)/2 such that pi(k*n) is a
triangular number.

Formalization notes:
* pi = `Nat.primeCounting` (pi(x) = number of primes ≤ x); prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2).
* "k < prime(n)/2" is stated as 2k < prime(n); triangular numbers are t(t+1)/2, t ≥ 0.
* Controls (computed): a(1..25) = 1, 1, 1, 2, 2, 2, 4, 3, 5, 2, 3, 5, 3, 6, 1, 2, 3, 3, 5, 3, 5, 2, 6,
  4, 4, as in the entry; both parts hold for n < 160.
-/

namespace OMA.S_oeis_a237598

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A237598(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 (prime n)).filter fun k => IsSquare (Nat.primeCounting (k * n))).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → 0 < a n) ∧
      ∀ n : ℕ, 9 < n → ∃ k, 0 < k ∧ 2 * k < prime n ∧
        ∃ t : ℕ, Nat.primeCounting (k * n) = t * (t + 1) / 2 := by
  sorry

end OMA.S_oeis_a237598
