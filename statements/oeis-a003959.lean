import Mathlib

/-!
# OEIS A003959: Euler product of the Dirichlet series

Source: https://oeis.org/A003959
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = ∏ (p_k + 1)^{e_k}` for `n = ∏ p_k^{e_k}`, `a(1) = 1`. The entry records (as
conjectured) `∑_{n>0} a(n)/n^s = ∏_{p prime} 1/(1 - p^{-s} - p^{1-s})`.

Range: the identity is stated for complex `s` with `Re s > 2`, where both sides converge
absolutely (`a(n) ≤ n σ₀(n)`-type growth; `|p^{-s} + p^{1-s}| < 1`). The product is Mathlib's
unconditional `tprod` over primes.
-/

namespace OMA.S_oeis_a003959

/-- `a(n) = ∏ (p + 1)^{e}` over the factorisation of `n`. -/
def a (n : ℕ) : ℕ := n.factorization.prod fun p e => (p + 1) ^ e

/-- The Euler product identity. -/
theorem main :
    ∀ s : ℂ, 2 < s.re →
      LSeries (fun n => (a n : ℂ)) s =
        ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s) - (p : ℂ) ^ (1 - s))⁻¹ := by
  sorry

end OMA.S_oeis_a003959
