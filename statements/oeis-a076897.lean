import Mathlib

/-!
# A076897: a(1) = 1, a(n) = n - a(floor(3n/4)).

Source: https://oeis.org/A076897
Credit: @bnb9001

The sequence has offset 1 and starts 1, 1, 2, 2, 3, 4, 4, ... The recursion only ever refers to
indices `floor(3n/4) ≥ 1` for `n ≥ 2`, so the value we give at `0` is never used.

Conjecture: a(n) is asymptotic to 4n/7, and (a(n) - 4n/7)/log(n) is bounded. Robert Israel notes
that the conjecture is true. We state the asymptotic as `a(n) / n → 4/7`, and the bound for all
`n ≥ 2` (where `log n > 0`) as `|a(n) - 4n/7| ≤ C log n`.
-/

namespace OMA.S_oeis_a076897

open Filter Topology

/-- A076897: `a 1 = 1` and `a n = n - a (⌊3n/4⌋)` for `n ≥ 2` (`a 0 = 0` is a placeholder). -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => (n + 2 : ℤ) - a (3 * (n + 2) / 4)
termination_by n => n
decreasing_by omega

/-- `a n ~ 4 n / 7`, and `(a n - 4 n / 7) / log n` is bounded for `n ≥ 2`. -/
theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (4 / 7)) ∧
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → |(a n : ℝ) - 4 * n / 7| ≤ C * Real.log n := by
  sorry

end OMA.S_oeis_a076897
