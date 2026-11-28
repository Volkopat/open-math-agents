import Mathlib

/-!
# A364305: a(n) = (8*n)!*(5*n)!*(3*n)! / ( (6*n)!*(4*n)!^2*n!^2 ).

Source: https://oeis.org/A364305
Credit: @azmiozgen

Conjecture (Peter Bala, formula section): the supercongruences a(n*p^k) == a(n*p^(k-1))
(mod p^(3*k)) hold for all primes p >= 5 and all positive integers n and k. The entry adds
(Oct 16 2024) that this follows from Meštrović, equation 39.

Formalization notes:
* a(n) is the integer quotient of factorials in the name (offset 0); the division is exact.
* The congruence is stated in ℤ as divisibility of the difference by p^(3k).
* Controls (computed): a(0..3) = 1, 70, 17550, 5567380, as in the entry; the congruence holds
  for p = 5, 7, 11 with n*p^k ≤ 130.
-/

namespace OMA.S_oeis_a364305

/-- A364305(n) = (8n)! (5n)! (3n)! / ((6n)! (4n)!^2 n!^2). -/
def a (n : ℕ) : ℤ :=
  ((8 * n).factorial * (5 * n).factorial * (3 * n).factorial /
    ((6 * n).factorial * (4 * n).factorial ^ 2 * n.factorial ^ 2) : ℕ)

/-- The supercongruences `a(n p^k) ≡ a(n p^(k-1)) (mod p^(3k))` for primes `p ≥ 5`. -/
theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      ((p : ℤ) ^ (3 * k) ∣ a (n * p ^ k) - a (n * p ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a364305
