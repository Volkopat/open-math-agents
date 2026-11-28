import Mathlib

/-!
# A241023: Central terms of the triangle in A102413

Source: https://oeis.org/A241023

Offset 0: 1, 4, 16, 76, 384, 2004, ...
G.f. (1+x)/sqrt(1-6*x+x^2), i.e. pairwise sums of the central Delannoy numbers A001850
(R. J. Mathar, 2020).
The Gauss congruences a(n*p^r) == a(n*p^(r-1)) (mod p^r) are stated in the entry as holding.
Conjecture (Peter Bala, Sep 18 2024): the supercongruences
a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and positive integers n and r.

Formalized: D(n) = Sum_{k=0..n} C(n,k)*C(n+k,k) (central Delannoy numbers), a(0) = 1 and
a(n) = D(n) + D(n-1) for n >= 1 (coefficients of (1+x) times the g.f. of D), as integers.
The congruence is stated in ℤ with Int.ModEq.
-/

namespace OMA.S_oeis_a241023

/-- Central Delannoy numbers A001850. -/
def D (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((n.choose k * (n + k).choose k : ℕ) : ℤ)

/-- A241023: coefficients of (1+x) * Sum D(n) x^n. -/
def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => D (n + 1) + D n

theorem main : ∀ p n r : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < r →
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r))] := by
  sorry

end OMA.S_oeis_a241023
