import Mathlib

/-!
# OEIS A166602: Numbers k such that `∑_{i=1}^k i^2` divides `∏_{i=1}^k i^2`

Source: https://oeis.org/A166602 and https://oeis.org/A067656 (OEIS Foundation, CC BY-SA 4.0).
R. J. Mathar's conjecture (Nov 06, 2025) on OEIS A166602 states that the numbers `k ≥ 1` for
which `∑_{i=1}^k i^2` divides `∏_{i=1}^k i^2` are precisely `1` together with the terms of
OEIS A067656 (the positive integers `k` such that `k! * B_{2k}` is an integer, where `B_{2k}`
is the `2k`-th Bernoulli number).
-/

namespace OMA.S_oeis_a166602

/-- Conjecture on OEIS A166602 (R. J. Mathar, Nov 06, 2025): for every `k ≥ 1`,
`∑_{i=1}^k i^2` divides `∏_{i=1}^k i^2` if and only if `k = 1` or `k! * B_{2k}` is an integer
(i.e. `k ∈ A067656`). -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    ((∑ i ∈ Finset.Icc 1 k, i ^ 2) ∣ (∏ i ∈ Finset.Icc 1 k, i ^ 2) ↔
      k = 1 ∨ (k.factorial : ℚ) * bernoulli (2 * k) ∈ Set.range (Int.cast : ℤ → ℚ)) := by
  sorry

end OMA.S_oeis_a166602
