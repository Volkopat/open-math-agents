import Mathlib

/-!
# OEIS A092843: summatory function of ∑_{k ∣ n, k > 1} φ(k - 1)

Source: https://oeis.org/A092843
`a(n) = ∑_{k ∣ n, k > 1} φ(k - 1)`. Conjecture (Kotesovec, 2024):
`∑_{k=1}^{n} a(k) ~ n² / 2`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a092843

open Filter Asymptotics

/-- A092843. -/
def a (n : ℕ) : ℕ := ∑ k ∈ n.divisors.filter (1 < ·), (k - 1).totient

theorem main :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (a k : ℝ)) ~[atTop] fun n : ℕ => (n : ℝ) ^ 2 / 2 := by
  sorry

end OMA.S_oeis_a092843
