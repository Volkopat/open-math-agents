import Mathlib

/-!
# A364181: a(n) = (10n)! (3n/2)! / ((5n)! (9n/2)! (2n)!)

Source: https://oeis.org/A364181

Definition: a(n) = (10*n)!*(3*n/2)!/((5*n)!*(9*n/2)!*(2*n)!), offset 0,
where fractional factorials are x! := Gamma(1 + x). The entry says the sequence is only
conjecturally an integer sequence.
Conjecture (Peter Bala, 2023): the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r))
hold for all primes p >= 5 and all positive integers n and r.

Formalized:
- a(n) is a rational number. For a natural k, (k/2)! = Gamma(1 + k/2) equals (k/2)! when k is
  even and k!! * sqrt(pi) / 2^((k+1)/2) when k is odd. Since 3n and 9n have the same parity,
  the factors sqrt(pi) cancel in the quotient (3n/2)!/(9n/2)!, so `hf k` below is
  Gamma(1 + k/2) with the factor sqrt(pi) dropped for odd k, and a(n) is exact in ℚ.
- Integrality is not assumed (it is itself conjectural), so the congruence is stated for
  rationals: a(n*p^r) - a(n*p^(r-1)) = p^(3r) * q with q a rational whose denominator is
  coprime to p (q is p-integral). For integer values this is the usual congruence.
-/

namespace OMA.S_oeis_a364181

/-- Gamma(1 + k/2), with the factor sqrt(pi) removed when k is odd. -/
def hf (k : ℕ) : ℚ :=
  if k % 2 = 0 then ((k / 2).factorial : ℚ)
  else (k.doubleFactorial : ℚ) / (2 : ℚ) ^ ((k + 1) / 2)

/-- a(n) = (10n)! (3n/2)! / ((5n)! (9n/2)! (2n)!). -/
def a (n : ℕ) : ℚ :=
  ((10 * n).factorial : ℚ) * hf (3 * n) /
    (((5 * n).factorial : ℚ) * hf (9 * n) * ((2 * n).factorial : ℚ))

theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n r : ℕ, 1 ≤ n → 1 ≤ r →
      ∃ q : ℚ, Nat.Coprime q.den p ∧
        a (n * p ^ r) - a (n * p ^ (r - 1)) = (p : ℚ) ^ (3 * r) * q := by
  sorry

end OMA.S_oeis_a364181
