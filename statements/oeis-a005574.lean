import Mathlib

/-!
# A005574: numbers `k` with `k² + 1` prime (Hardy–Littlewood asymptotic)

Source: https://oeis.org/A005574
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Hardy–Littlewood, listed in A005574): the number of `k ≤ n` with `k² + 1` prime is
asymptotically `c √n / log n` for some constant `c`.

Conventions:
* `c > 0` (with `c = 0` the statement would claim the count is `o(√n / log n)`, which is not the
  conjecture); "asymptotically" is `~` (the ratio tends to `1`).
* The count is over `1 ≤ k ≤ n`, as the sequence lists `k ≥ 1`.
-/

namespace OMA.S_oeis_a005574

/-- The number of `1 ≤ k ≤ n` with `k² + 1` prime. -/
def count (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter (fun k => (k ^ 2 + 1).Prime)).card

theorem main :
    ∃ c : ℝ, 0 < c ∧
      Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (count n : ℝ))
        (fun n : ℕ => c * Real.sqrt n / Real.log n) := by
  sorry

end OMA.S_oeis_a005574
