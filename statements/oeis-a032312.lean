import Mathlib

/-!
# OEIS A032312: Gauss congruences for the EGJ transform of `2, 2, 2, …`

Source: https://oeis.org/A032312
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A032312 is the EGJ (unordered, element, labeled) transform of the constant sequence `2`.
Conjecture (Bala, 2022): the Gauss congruences `a(n p^k) ≡ a(n p^(k-1)) (mod p^k)` hold for all
primes `p` and positive integers `n, k`.

Conventions:
* The EGJ transform of `b` has e.g.f. `∏_{k ≥ 1} (1 + b_k x^k/k!)` (for `b = 1` this is A007837,
  set partitions with distinct block sizes). So `a(n) = n! [xⁿ] ∏_{k=1}^{n} (1 + 2 x^k/k!)`
  (factors with `k > n` do not affect `[xⁿ]`), computed in `ℚ`; it is an integer.
-/

namespace OMA.S_oeis_a032312

open Polynomial

/-- `a(n) = n! [xⁿ] ∏_{k ≤ n} (1 + 2 x^k / k!)`. -/
noncomputable def a (n : ℕ) : ℚ :=
  n.factorial * (∏ k ∈ Finset.range n,
    (1 + C (2 / ((k + 1).factorial : ℚ)) * X ^ (k + 1) : ℚ[X])).coeff n

/-- The Gauss congruences. -/
theorem main : ∀ p n k : ℕ, p.Prime → 1 ≤ n → 1 ≤ k →
    ∃ z : ℤ, a (n * p ^ k) - a (n * p ^ (k - 1)) = (p : ℚ) ^ k * z := by
  sorry

end OMA.S_oeis_a032312
