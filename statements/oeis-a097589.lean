import Mathlib

/-!
# OEIS A097589: partial sums of Fortunate numbers versus partial sums of primes

Source: https://oeis.org/A097589
`a n = ∑_{i=1}^{n} A005235(i)`, partial sums of the Fortunate numbers (`A005235(i)` is the least
`m > 1` such that `p_i# + m` is prime, `p_i#` the product of the first `i` primes). With
`F(n) = a(n) / A007504(n)` (`A007504(n)` the sum of the first `n` primes), the entry
conjectures `F(n) → π/2`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a097589

open Filter Topology Real

/-- The `i`-th Fortunate number (`i ≥ 1`). -/
noncomputable def fortunate (i : ℕ) : ℕ :=
  sInf {m | 1 < m ∧ (primorial (Nat.nth Nat.Prime (i - 1)) + m).Prime}

theorem main :
    Tendsto (fun n : ℕ =>
        (∑ i ∈ Finset.Icc 1 n, (fortunate i : ℝ)) / ∑ i ∈ Finset.range n, (Nat.nth Nat.Prime i : ℝ))
      atTop (𝓝 (π / 2)) := by
  sorry

end OMA.S_oeis_a097589
