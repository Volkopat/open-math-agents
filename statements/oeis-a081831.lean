import Mathlib

/-!
# OEIS A081831: a nested meta-Fibonacci recursion has linear growth

Source: https://oeis.org/A081831
`a(1) = a(2) = 1`, `a(n) = a(a(n - a(n-1))) + a(n - a(n-2))`. Conjecture: `a(n)/n → C` for a
constant `C = 0.2…`. `main` states that `a(n)/n` converges to some positive constant.

Conventions. `aList` builds the values with a placeholder `a 0 = 0`; the recursion reads
earlier list entries (indices outside the list read as `0`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a081831

open Filter Topology

/-- `[a 0, a 1, …, a n]` with the placeholder `a 0 = 0`. -/
def aList : ℕ → List ℕ
  | 0 => [0]
  | 1 => [0, 1]
  | 2 => [0, 1, 1]
  | n + 3 =>
      let l := aList (n + 2)
      let g := fun i => l.getD i 0
      l ++ [g (g (n + 3 - g (n + 2))) + g (n + 3 - g (n + 1))]

/-- A081831. -/
def a (n : ℕ) : ℕ := (aList n).getD n 0

theorem main : ∃ C : ℝ, 0 < C ∧ Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 C) := by
  sorry

end OMA.S_oeis_a081831
