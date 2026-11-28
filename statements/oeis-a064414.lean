import Mathlib

/-!
# OEIS A064414: numbers that divide at least one term in every Fibonacci sequence

Source: https://oeis.org/A064414
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`m` is in the sequence iff for all `a, b > 0` the sequence `G₁ = a, G₂ = b, Gₖ = Gₖ₋₁ + Gₖ₋₂`
has some term divisible by `m`. Conjecture (Logan J. Kleinwaks, in the entry): these are exactly
the positive `j` with `j² = ∑_{d ∣ j} φ(d) α(d)`, where `α(d)` = A001177(d) is the least `k ≥ 1`
with `d ∣ F_k`.
-/

namespace OMA.S_oeis_a064414

/-- The generalized Fibonacci sequence with `G₁ = a`, `G₂ = b` (index shifted: `G (k+1)`). -/
def G (a b : ℕ) : ℕ → ℕ
  | 0 => a
  | 1 => b
  | k + 2 => G a b k + G a b (k + 1)

/-- A001177: the least `k ≥ 1` with `d ∣ F_k`. -/
noncomputable def alpha (d : ℕ) : ℕ := sInf {k | 0 < k ∧ d ∣ Nat.fib k}

/-- Kleinwaks's characterization. -/
theorem main : ∀ j : ℕ, 0 < j →
    ((∀ a b : ℕ, 0 < a → 0 < b → ∃ k, j ∣ G a b k) ↔
      j ^ 2 = ∑ d ∈ j.divisors, Nat.totient d * alpha d) := by
  sorry

end OMA.S_oeis_a064414
