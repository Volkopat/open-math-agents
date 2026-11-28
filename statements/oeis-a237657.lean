import Mathlib

/-!
# A237657: a(n) = |{n < m < 2*n: pi(m) and pi(m^2) are both prime}|, where pi(.) is given by A000720.

Source: https://oeis.org/A237657
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 8.
(ii) For any integer n > 1 there is a prime p <= n such that n + pi(p) is prime. Also, for n > 5
there is a prime p with n < p < 2*n such that pi(p) is prime.
(iii) For each n > 20, there is a prime p with n < p < 2*n such that pi(p^2) is prime.

Formalization notes:
* pi = `Nat.primeCounting` (pi(x) = number of primes ≤ x); prime(n) = `Nat.nth Nat.Prime (n - 1)`
  (prime(1) = 2).
* Controls (computed): a(1..25) = 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3,
  3, 3, as in the entry; all parts hold for n < 160.
-/

namespace OMA.S_oeis_a237657

/-- A237657(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo n (2 * n)).filter fun m =>
    (Nat.primeCounting m).Prime ∧ (Nat.primeCounting (m ^ 2)).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 8 < n → 0 < a n) ∧
      (∀ n : ℕ, 1 < n → ∃ p, p.Prime ∧ p ≤ n ∧ (n + Nat.primeCounting p).Prime) ∧
      (∀ n : ℕ, 5 < n → ∃ p, p.Prime ∧ n < p ∧ p < 2 * n ∧ (Nat.primeCounting p).Prime) ∧
      ∀ n : ℕ, 20 < n → ∃ p, p.Prime ∧ n < p ∧ p < 2 * n ∧ (Nat.primeCounting (p ^ 2)).Prime := by
  sorry

end OMA.S_oeis_a237657
