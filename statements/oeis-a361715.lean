import Mathlib

/-!
# OEIS A361715: supercongruences for Sum_{k=0..n-1} binomial(n,k)^2*binomial(n+k-1,k)

Source: https://oeis.org/A361715 (OEIS Foundation, CC BY-SA 4.0).
Credit: @sntntHb (statement written by an agent on behalf of @sntntHb).

A361715(n) = Sum_{k=0..n-1} binomial(n,k)^2 * binomial(n+k-1,k), offset 0;
data 0, 1, 9, 82, 745, 6876, 64764, ...

The COMMENTS of the entry (Peter Bala) state two conjectures. Conjecture 1 (a(p) == a(1)
(mod p^5) for primes p >= 7) is marked there as proved. Conjecture 2 is still open:

Conjecture 2: for r >= 2, the supercongruence a(p^r) == a(p^(r-1)) (mod p^(3*r+3)) holds for
all primes p >= 5.

We state Conjecture 2 for every prime `p ≥ 5` and every `r ≥ 2`. Checked numerically for
(p, r) = (5, 2), (5, 3), (7, 2), (7, 3). For `n ≥ 1` the term `n + k - 1` has no truncated
subtraction; for `n = 0` the sum is empty, matching a(0) = 0.
-/

namespace OMA.S_oeis_a361715

/-- A361715: `a n = Sum_{k=0..n-1} binomial(n,k)^2 * binomial(n+k-1,k)`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (Nat.choose n k) ^ 2 * Nat.choose (n + k - 1) k

/-- Conjecture 2 (OEIS A361715): `a(p^r) ≡ a(p^(r-1)) (mod p^(3r+3))` for primes `p ≥ 5`
and `r ≥ 2`. -/
theorem main : ∀ p r : ℕ, p.Prime → 5 ≤ p → 2 ≤ r →
    a (p ^ r) ≡ a (p ^ (r - 1)) [MOD p ^ (3 * r + 3)] := by
  sorry

end OMA.S_oeis_a361715
