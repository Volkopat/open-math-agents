import Mathlib

/-!
# OEIS A064098: a Markov-number recurrence, doubly exponential growth

Source: https://oeis.org/A064098
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n+1) = (a(n)² + a(n-1)²)/a(n-2)` with `a(1) = a(2) = a(3) = 1`. Conjecture (Giese, 2005):
`lim_{n → ∞} log(log(a(n)))/n = log((√5 + 1)/2)`.

Conventions:
* The terms are positive integers (they are Markov numbers); the division is computed in `ℕ`
  (exact). Indexing: `a 1 = a 2 = a 3 = 1`, `a 0` is a placeholder.
-/

namespace OMA.S_oeis_a064098

open Filter Topology

/-- The sequence. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | n + 4 => (a (n + 3) ^ 2 + a (n + 2) ^ 2) / a (n + 1)

/-- `log log a(n) / n → log φ`. -/
theorem main : Tendsto (fun n : ℕ => Real.log (Real.log (a n)) / n) atTop
    (𝓝 (Real.log ((Real.sqrt 5 + 1) / 2))) := by
  sorry

end OMA.S_oeis_a064098
