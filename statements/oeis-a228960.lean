import Mathlib

/-!
# A228960: a(n) = [x^n] (1 + x + x^3 + x^4)^n

Source: https://oeis.org/A228960

Definition: a(n) is the coefficient of x^n in (1 + x + x^3 + x^4)^n; offset 1
(data 1, 1, 4, 17, 51, 136, 393, ...).
Claim (Peter Bala, Apr 15 2023, Conjecture 1): the supercongruence
a(n*p^r) == a(n*p^(r-1)) (mod p^(2*r)) holds for positive integers n and r and all
primes p >= 5. Bala's Conjecture 2 is a general meta-conjecture about other
sequences and is not part of this target.

Formalized: a(n) is an integer, defined as Polynomial.coeff of the n-th power of
the integer polynomial 1 + X + X^3 + X^4 (the definition also makes sense at n = 0,
but the claim only uses n >= 1). The congruence is Int.ModEq modulo p^(2*r) in ℤ,
for n >= 1, r >= 1, p prime with p >= 5.
-/

namespace OMA.S_oeis_a228960

open Polynomial

/-- a(n) = [x^n] (1 + x + x^3 + x^4)^n. -/
noncomputable def a (n : ℕ) : ℤ :=
  ((1 + X + X ^ 3 + X ^ 4 : ℤ[X]) ^ n).coeff n

theorem main :
    ∀ n r p : ℕ, 1 ≤ n → 1 ≤ r → p.Prime → 5 ≤ p →
      a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (2 * r))] := by
  sorry

end OMA.S_oeis_a228960
