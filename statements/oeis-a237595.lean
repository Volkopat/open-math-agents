import Mathlib

/-!
# A237595: a(n) = |{1 <= k <= n: n + pi(k^2) is prime}|, where pi(.) is given by A000720.

Source: https://oeis.org/A237595
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 4.
(ii) If n > 1 then n + pi(k*(k-1)) is prime for some k = 1, ..., n.
(iii) For any integer n > 1, there is a positive integer k <= (n+1)/2 such that
pi(n + k*(k+1)/2) is prime.
(iv) Any integer n > 1 can be written as p + pi(k*(k+1)/2), where p is a prime and k is among
1, ..., n-1.

Formalization notes:
* pi = `Nat.primeCounting` (pi(x) = number of primes ≤ x); prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2).
* Parts (i)-(iii) are stated. "k <= (n+1)/2" is stated as 2k ≤ n + 1.
* Part (iv) is not stated: a direct computation finds that it fails for n = 36 (the values
  36 - pi(k(k+1)/2) for k = 1..17 are 36, 34, 33, 32, 30, 28, 27, 25, 22, 20, 18, 15, 12, 9, 6, 4,
  0, none prime, and pi(k(k+1)/2) > 36 for k ≥ 18) and for n = 66.
* Controls (computed): a(1..25) = 0, 1, 3, 0, 3, 1, 3, 3, 3, 1, 5, 2, 6, 3, 4, 2, 6, 3, 7, 3, 2, 6, 8,
  1, 10, as in the entry; parts (i)-(iii) hold for n < 160.
-/

namespace OMA.S_oeis_a237595

/-- A237595(n). -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun k => (n + Nat.primeCounting (k ^ 2)).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 4 < n → 0 < a n) ∧
      (∀ n : ℕ, 1 < n → ∃ k, 1 ≤ k ∧ k ≤ n ∧ (n + Nat.primeCounting (k * (k - 1))).Prime) ∧
      ∀ n : ℕ, 1 < n → ∃ k, 0 < k ∧ 2 * k ≤ n + 1 ∧
        (Nat.primeCounting (n + k * (k + 1) / 2)).Prime := by
  sorry

end OMA.S_oeis_a237595
