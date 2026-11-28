import Mathlib

/-!
# A238386: a(n) = |{0 < k < n-1: p = prime(k) + pi(n-k) and p + 2 are both prime}|, where pi(.) is given by A000720.

Source: https://oeis.org/A238386
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 10.
(ii) For any integer n > 4, there is a positive integer k < n such that prime(k)^2 + pi(n-k)^2 is
prime.

Formalization notes:
* pi = `Nat.primeCounting` (pi(x) = number of primes ≤ x); prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2).
* Controls (computed): a(1..25) = 0, 0, 1, 0, 1, 2, 1, 0, 0, 0, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3, 3, 2,
  3, 2, as in the entry; both parts hold for n < 160.
-/

namespace OMA.S_oeis_a238386

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A238386(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 (n - 1)).filter fun k =>
    (prime k + Nat.primeCounting (n - k)).Prime ∧ (prime k + Nat.primeCounting (n - k) + 2).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 10 < n → 0 < a n) ∧
      ∀ n : ℕ, 4 < n → ∃ k, 0 < k ∧ k < n ∧ (prime k ^ 2 + Nat.primeCounting (n - k) ^ 2).Prime := by
  sorry

end OMA.S_oeis_a238386
