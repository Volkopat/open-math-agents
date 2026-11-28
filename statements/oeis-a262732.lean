import Mathlib

/-!
# A262732: a(n) = (1/n!) * (5*n)!/(5*n/2)! * (3*n/2)!/(3*n)!

Source: https://oeis.org/A262732

Offset 0. Data: 1, 8, 126, 2240, 41990, 811008, ...
Conjecture (Peter Bala, Sep 15 2021): a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k))
for prime p >= 5 and positive integers n and k.
(The case a(p) == a(1) (mod p^3) is stated in the entry as a fact; it is the
case n = k = 1 of the conjecture.)

Formalized: a(n) is defined by the entry's formula (Seiichi Manyama, 2025)
a(n) = Sum_{k=0..n} 2^k * (-1)^(n-k) * binomial(5*n,k) * binomial(2*n-k,n-k),
computed in ℤ; the natural subtractions 2*n-k and n-k have k <= n so are exact.
This reproduces the listed terms. The congruence is stated with Int.ModEq.
-/

namespace OMA.S_oeis_a262732

/-- A262732 via the binomial sum formula of the entry. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (2 : ℤ) ^ k * (-1 : ℤ) ^ (n - k) * (Nat.choose (5 * n) k : ℤ) *
      (Nat.choose (2 * n - k) (n - k) : ℤ)

theorem main : ∀ p n k : ℕ, p.Prime → 5 ≤ p → 1 ≤ n → 1 ≤ k →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := by
  sorry

end OMA.S_oeis_a262732
