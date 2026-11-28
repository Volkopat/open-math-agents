import Mathlib

/-!
# A172434: G.f.: Sum_{n>=0} a(n)*x^n/n!^4 = [ Sum_{n>=0} x^n/n!^4 ]^3

Source: https://oeis.org/A172434

Offset 0; data 1, 3, 51, 1785, 67635, ... The entry gives the formula
`a(n) = Sum_{k=0..n} C(n,k)^4 * Sum_{j=0..k} C(k,j)^4` (equivalent to the e.g.f.-type definition:
both equal the sum of multinomial(n; i, j, l)^4 over i + j + l = n).

Conjecture (Peter Bala, Aug 05 2026):
1. `a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k))` for primes `p >= 5` and positive integers `n`, `k`.
2. With the extension `a(-n) = Sum_{k=0..n} C(-n,k)^4 * Sum_{j=0..k} C(k,j)^4`
   (values 1, 3, 1491, 1663491, ...), the same supercongruences hold for `a(-n)`.

Formalized: `a n : ℤ` is the formula above with `Nat.choose`. The negative extension is `aneg n = a(-n)`,
with `C(-n,k)` taken as the generalized binomial coefficient `Ring.choose (-(n:ℤ)) k`.
Claim 2 is read as `a(-n*p^k) == a(-n*p^(k-1)) (mod p^(3k))` for the same `p, n, k`.
Congruences are divisibility in `ℤ`. The two claims form a conjunction in the order of the entry.
-/

namespace OMA.S_oeis_a172434

/-- `Sum_{j=0..k} C(k,j)^4` (A005260). -/
def inner (k : ℕ) : ℤ := ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℕ) : ℤ) ^ 4

/-- A172434: `a(n) = Sum_{k=0..n} C(n,k)^4 * Sum_{j=0..k} C(k,j)^4`. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℕ) : ℤ) ^ 4 * inner k

/-- The extension to negative indices: `aneg n = a(-n) = Sum_{k=0..n} C(-n,k)^4 * Sum_{j=0..k} C(k,j)^4`. -/
def aneg (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (Ring.choose (-(n : ℤ)) k) ^ 4 * inner k

theorem main :
    (∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n k : ℕ, 0 < n → 0 < k →
      ((p : ℤ) ^ (3 * k)) ∣ (a (n * p ^ k) - a (n * p ^ (k - 1)))) ∧
    (∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n k : ℕ, 0 < n → 0 < k →
      ((p : ℤ) ^ (3 * k)) ∣ (aneg (n * p ^ k) - aneg (n * p ^ (k - 1)))) := by
  sorry

end OMA.S_oeis_a172434
