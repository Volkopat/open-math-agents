import Mathlib

/-!
# A237497: a(n) = |{0 < k <= n/2: pi(k*(n-k)) is prime}|, where pi(.) is given by A000720.

Source: https://oeis.org/A237497
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) > 0 for all n > 10, and a(n) = 1 for no n > 51.
Moreover, for any integer n > 10, there is a positive integer k < n with 2*k + 1 and
pi(k*(n-k)) both prime.

Formalization notes:
* pi = `Nat.primeCounting` (pi(x) = number of primes ≤ x); prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2).
* "k <= n/2" is stated as 2k ≤ n.
* Controls (computed): a(1..25) = 0, 0, 0, 2, 2, 1, 2, 1, 1, 0, 1, 4, 3, 1, 1, 1, 3, 2, 6, 2, 2, 2, 4,
  1, 1, as in the entry; all three claims hold for n < 160.
-/

namespace OMA.S_oeis_a237497

/-- A237497(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter fun k => 2 * k ≤ n ∧ (Nat.primeCounting (k * (n - k))).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 10 < n → 0 < a n) ∧ (∀ n : ℕ, 51 < n → a n ≠ 1) ∧
      ∀ n : ℕ, 10 < n → ∃ k, 0 < k ∧ k < n ∧ (2 * k + 1).Prime ∧
        (Nat.primeCounting (k * (n - k))).Prime := by
  sorry

end OMA.S_oeis_a237497
