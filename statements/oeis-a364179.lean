import Mathlib

/-!
# A364179: a(n) = (10*n)!*(n/2)!/((5*n)!*(4*n)!*(3*n/2)!)

Source: https://oeis.org/A364179

Offset 0. Fractional factorials are x! := Gamma(1 + x). The entry says the sequence is
only conjecturally integral (that is a separate claim, not stated here). The conjecture:
the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5
and all positive integers n and r.

Formalized: a(n) is a rational number. For k odd, Gamma(1 + k/2) = k!/(2^k*((k-1)/2)!) * sqrt(pi);
since n and 3n have the same parity the factors sqrt(pi) cancel, so `hf k` is Gamma(1 + k/2)
with that factor removed. As integrality is itself conjectural, the congruence is stated
p-adically: the difference is zero or has p-adic valuation at least 3*r.
-/

namespace OMA.S_oeis_a364179

/-- Gamma(1 + k/2), divided by sqrt(pi) when k is odd. -/
def hf (k : ℕ) : ℚ :=
  if k % 2 = 0 then ((k / 2).factorial : ℚ)
  else (k.factorial : ℚ) / ((2 : ℚ) ^ k * ((k - 1) / 2).factorial)

/-- a(n) = (10n)! (n/2)! / ((5n)! (4n)! (3n/2)!). -/
def a (n : ℕ) : ℚ :=
  ((10 * n).factorial : ℚ) * hf n /
    (((5 * n).factorial : ℚ) * ((4 * n).factorial : ℚ) * hf (3 * n))

theorem main : ∀ p n r : ℕ, p.Prime → 5 ≤ p → 1 ≤ n → 1 ≤ r →
    a (n * p ^ r) - a (n * p ^ (r - 1)) = 0 ∨
      ((3 * r : ℕ) : ℤ) ≤ padicValRat p (a (n * p ^ r) - a (n * p ^ (r - 1))) := by
  sorry

end OMA.S_oeis_a364179
