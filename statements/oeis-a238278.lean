import Mathlib

/-!
# A238278: a(n) = |{0 < k < n: the number of primes in the interval ((k-1)*n, k*n] and the number of primes in the interval (k*n, (k+1)*n] are both prime}|.

Source: https://oeis.org/A238278
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 3.
(ii) For any integer n > 3, there is a prime p < n such that the number of primes in the
interval ((p-1)*n, p*n) is a prime.

Formalization notes:
* The number of primes in (x, y] is pi(y) - pi(x) with pi = `Nat.primeCounting`; in the open
  interval ((p-1)n, pn) it is pi(pn - 1) - pi((p-1)n).
* Controls (computed): a(1..25) = 0, 0, 0, 1, 1, 3, 3, 2, 7, 6, 8, 4, 9, 4, 9, 8, 1, 1, 3, 5, 4, 6, 3,
  4, 4, as in the entry; both parts hold for n < 150.
-/

namespace OMA.S_oeis_a238278

/-- A238278(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter fun k =>
    (Nat.primeCounting (k * n) - Nat.primeCounting ((k - 1) * n)).Prime ∧
    (Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n)).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 3 < n → 0 < a n) ∧
      ∀ n : ℕ, 3 < n → ∃ p, p.Prime ∧ p < n ∧
        (Nat.primeCounting (p * n - 1) - Nat.primeCounting ((p - 1) * n)).Prime := by
  sorry

end OMA.S_oeis_a238278
