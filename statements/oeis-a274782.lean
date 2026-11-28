import Mathlib

/-!
# A274782: diagonal of `1 / (1 - x - x * y - x * z - y * z)`

Source: https://oeis.org/A274782
Credit: @Bondyboy2001

The OEIS gives Peter Bala's finite-sum formula
`a(n) = ∑_{k=0}^n C(n,k) * C(n+k,k) * C(k,n-k)`. The conjecture is the supercongruence
`a(n*p^r) ≡ a(n*p^(r-1)) (mod p^(2*r))` for positive integers `n` and `r` and all primes
`p ≥ 5`.
-/

namespace OMA.S_oeis_a274782

/-- Peter Bala's finite binomial-sum formula for the diagonal sequence. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k * (n + k).choose k * k.choose (n - k)

/-- The supercongruence conjectured by Peter Bala. -/
theorem main :
    ∀ n r p : ℕ, 0 < n → 0 < r → p.Prime → 5 ≤ p →
      a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (2 * r)] := by
  sorry

end OMA.S_oeis_a274782
