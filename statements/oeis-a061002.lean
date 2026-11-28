import Mathlib

/-!
# OEIS A061002: Wolstenholme quotients and harmonic numbers

Source: https://oeis.org/A061002
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For primes `p ≥ 5`, A061002 gives `numerator(H(p-1))/p²` (an integer by Wolstenholme's theorem),
`H(m) = ∑_{k=1}^{m} 1/k`. Conjecture (OEIS entry): for primes `p > 3`,
`denominator(H(p)/H(p-1)) / numerator(H(p-1)/p²) = p³`.

Conventions:
* Numerators and denominators of rationals in lowest terms (`Rat.num`, `Rat.den`); the identity is
  stated multiplicatively: `denominator(H(p)/H(p-1)) = p³ · numerator(H(p-1)/p²)`.
-/

namespace OMA.S_oeis_a061002

/-- The harmonic number `H(m)`. -/
def H (m : ℕ) : ℚ := ∑ k ∈ Finset.Icc 1 m, (1 : ℚ) / k

/-- The conjectured identity for primes `p > 3`. -/
theorem main : ∀ p : ℕ, p.Prime → 3 < p →
    ((H p / H (p - 1)).den : ℤ) = (p : ℤ) ^ 3 * (H (p - 1) / (p : ℚ) ^ 2).num := by
  sorry

end OMA.S_oeis_a061002
