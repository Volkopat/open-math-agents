import Mathlib

/-!
# Simmons' inequality on binomial random variables

Source: https://mathoverflow.net/questions/384456 (asked in 2021, no answer). The same statement is
Conjecture 4.2 of Fokkink, Papavassiliou and Pelekis, arXiv 2011.11795 (Condition (S₂) there); in the
published version, On the monotonicity of tail probabilities, Probab. Math. Statist. 42 (2022), it is
Condition (L₂) of Conjecture 4.1.

Fix two positive integers `n, m` such that `n > 2 m` and `n ≥ 3`, and let `X ∼ Bin(n, m / n)`. For each
`i ∈ {1, …, m}` set `α i = P(X ≤ m - i) - P(X ≥ m + i)`. It is known that `α 1 > 0` (Simmons' inequality).
The conjecture of the source: for every `k ∈ {1, …, m}`, the sum `S k = ∑_{i=1}^{k} α i` is nonnegative.

The binomial law of `X` is given through its local probabilities
`P(X = j) = (n choose j) (m / n)^j (1 - m / n)^(n - j)`.
-/

namespace OMA.S_mo_384456

open MeasureTheory

theorem main : ∀ (n m : ℕ), 0 < m → 2 * m < n → 3 ≤ n →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℕ),
      Measurable X →
      (∀ j : ℕ, P.real {ω | X ω = j} =
        (n.choose j : ℝ) * ((m : ℝ) / n) ^ j * (1 - (m : ℝ) / n) ^ (n - j)) →
      ∀ k ∈ Finset.Icc 1 m,
        0 ≤ ∑ i ∈ Finset.Icc 1 k, (P.real {ω | X ω ≤ m - i} - P.real {ω | m + i ≤ X ω}) := by
  sorry

end OMA.S_mo_384456
