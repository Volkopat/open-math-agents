import Mathlib

/-!
# Alternating binomial sums in a coupon-collecting problem

The MathOverflow question asks for an elementary proof that the two expressions
agree for positive integers n and m. We use rational arithmetic throughout.
Source: https://mathoverflow.net/questions/128291
-/

namespace OMA.S_mo_128291

theorem main : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
    (∑ s ∈ Finset.Icc 1 n, ((s:ℚ)+m)*(n.choose s : ℚ)*
      (∑ i ∈ Finset.range (s+1), (-1:ℚ)^i*(s.choose i : ℚ)*
        (((s-i:ℕ):ℚ)/n)^(s+m-1))*(s:ℚ)/n) =
    (n:ℚ)+m - ∑ k ∈ Finset.Icc 1 n,
      (k:ℚ)^(k-1)*(n.choose k : ℚ)*((n-k:ℕ):ℚ)^(n+m-k)/(n:ℚ)^(n+m-1) := by
  sorry

end OMA.S_mo_128291
