import Mathlib

/-!
# OEIS A364509

Square array `T(n, k) = (2*k)! / k!^2 * ((2*n*k)! * ((n + 2)*k)!) / ((n*k)! * ((n + 1)*k)!^2)`
for `n >= 0, k >= 0`.

Conjecture (Peter Bala):
All row sequences `k ↦ T(n, k)` satisfy the supercongruences
`T(n, m * p^r) ≡ T(n, m * p^(r - 1)) [MOD p^(3 * r)]`
for all `n >= 0`, all primes `p >= 5`, and all positive integers `m` and `r`.
-/

namespace OMA.S_oeis_a364509

/-- `T(n, k) = ((2*k)! * (2*n*k)! * ((n + 2)*k)!) / (k!^2 * (n*k)! * ((n + 1)*k)!^2)`. -/
def T (n k : ℕ) : ℕ :=
  ((2 * k).factorial * (2 * n * k).factorial * ((n + 2) * k).factorial) /
    (k.factorial ^ 2 * (n * k).factorial * ((n + 1) * k).factorial ^ 2)

theorem main :
    ∀ n p m r : ℕ, p.Prime → 5 ≤ p → 1 ≤ m → 1 ≤ r →
      T n (m * p ^ r) ≡ T n (m * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  sorry

end OMA.S_oeis_a364509
