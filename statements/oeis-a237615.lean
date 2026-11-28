import Mathlib

/-!
# A237615: a(n) = |{0 < k < n: k^2 + k - 1 and pi(k*n) are both prime}|, where pi(.) is given by A000720.

Source: https://oeis.org/A237615
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 5.
(ii) For each n = 4, 5, ..., there is a positive integer k < n with k^2 + k - 1 and pi(k*n) + 1
both prime. Also, for any integer n > 6, there is a positive integer k < n with k^2 + k - 1 and
pi(k*n) - 1 both prime.
(iii) For every integer n > 15, there is a positive integer k < n such that pi(k) - 1 and
pi(k*n) are both prime.

Formalization notes:
* pi = `Nat.primeCounting` (pi(x) = number of primes ≤ x); prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2).
* Subtractions are in ℕ; a truncated value 0 is not prime, as negative numbers are not prime.
* Controls (computed): a(1..25) = 0, 0, 1, 1, 0, 2, 2, 1, 2, 1, 3, 2, 1, 4, 1, 3, 4, 4, 2, 4, 3, 6, 2,
  2, 2, as in the entry; all parts hold for n < 160.
-/

namespace OMA.S_oeis_a237615

/-- A237615(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter fun k => (k ^ 2 + k - 1).Prime ∧ (Nat.primeCounting (k * n)).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 5 < n → 0 < a n) ∧
      (∀ n : ℕ, 4 ≤ n → ∃ k, 0 < k ∧ k < n ∧ (k ^ 2 + k - 1).Prime ∧
        (Nat.primeCounting (k * n) + 1).Prime) ∧
      (∀ n : ℕ, 6 < n → ∃ k, 0 < k ∧ k < n ∧ (k ^ 2 + k - 1).Prime ∧
        (Nat.primeCounting (k * n) - 1).Prime) ∧
      ∀ n : ℕ, 15 < n → ∃ k, 0 < k ∧ k < n ∧ (Nat.primeCounting k - 1).Prime ∧
        (Nat.primeCounting (k * n)).Prime := by
  sorry

end OMA.S_oeis_a237615
