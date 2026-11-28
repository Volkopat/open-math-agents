import Mathlib

/-!
# OEIS A074208: least k with n ∣ σ(k) - k, summatory bound

Source: https://oeis.org/A074208
`a n` is the least `k > 1` such that `n` divides `σ(k) - k` (the sum of proper divisors).
Conjecture: `∑_{k=1}^{n} a(k) = O(n^(2+ε))` for every `ε > 0`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a074208

open Filter Asymptotics

/-- A074208. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k | 1 < k ∧ n ∣ (∑ d ∈ k.divisors, d) - k}

theorem main :
    ∀ ε : ℝ, 0 < ε →
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (a k : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (2 + ε) := by
  sorry

end OMA.S_oeis_a074208
