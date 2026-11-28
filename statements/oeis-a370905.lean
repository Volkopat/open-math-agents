import Mathlib

/-!
# A370905: Partial sums of the alternating sum of divisors function (A206369).

Source: https://oeis.org/A370905

A206369 is defined in the OEIS by a(p^k) = p^k - p^(k-1) + p^(k-2) - ... +- 1,
extended by multiplicativity, and A370905(n) = Sum_{k=1..n} A206369(k)
(offset 1).

The entry's conjecture (comment by Michel Marcus, confirmed in the next
comment by Chai Wah Wu): A370905(n) is also the number of pairs (x, y) with
1 <= x <= y <= n such that gcd(x, y) is a perfect square.
-/

namespace OMA.S_oeis_a370905

/-- A206369: multiplicative with a(p^k) = p^k - p^(k-1) + p^(k-2) - ... +- 1. -/
def A206369 (n : ℕ) : ℤ :=
  n.factorization.prod fun p k => ∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ i * (p : ℤ) ^ (k - i)

/-- A370905(n) = Sum_{k=1..n} A206369(k). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, A206369 k

theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = (((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
      (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ IsSquare (Nat.gcd p.1 p.2))).card : ℤ) := by
  sorry

end OMA.S_oeis_a370905
