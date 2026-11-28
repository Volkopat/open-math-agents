import Mathlib

/-!
# A333565: O.g.f.: (1 + 4*x)/((1 + x)*sqrt(1 - 8*x))

Source: https://oeis.org/A333565

Offset 0. Formula from the entry:
a(n) = 2^n*binomial(2*n,n) + 3*Sum_{k=0..n-1} (-1)^(n+k+1)*2^k*binomial(2*k,k).

Conjecture (Peter Bala, comment of the entry): a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k))
for every prime p >= 3 and all positive integers n and k.
The Gauss congruences mod p^k and the case n = k = 1 are stated in the entry as known;
they are special cases and not separately stated here.

Formalized: a(n) is an integer given by the explicit binomial-sum formula of the entry;
the sign (-1)^(n+k+1) is written as (-1 : ℤ)^(n+k+1). The congruence is divisibility in ℤ
of the difference by p^(3*k), with n ≥ 1, k ≥ 1.
-/

namespace OMA.S_oeis_a333565

/-- a(n) = 2^n*C(2n,n) + 3*Sum_{k<n} (-1)^(n+k+1)*2^k*C(2k,k). -/
def a (n : ℕ) : ℤ :=
  2 ^ n * (Nat.choose (2 * n) n : ℤ) +
    3 * ∑ k ∈ Finset.range n, (-1 : ℤ) ^ (n + k + 1) * 2 ^ k * (Nat.choose (2 * k) k : ℤ)

theorem main : ∀ p : ℕ, p.Prime → 3 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    ((p : ℤ) ^ (3 * k)) ∣ (a (n * p ^ k) - a (n * p ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a333565
