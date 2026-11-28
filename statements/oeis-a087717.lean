import Mathlib

/-!
# A087717: Start with x=n, then iterate the map x -> A322982(x) with A322982(x)=2*x-1 if x is noncomposite, otherwise A322982(x) = A032742(x), the largest proper divisor of x. If this iteration leads to a fixed point then a(n) is the value of that fixed point. If the iteration leads to a cycle, a(n) is the smallest value in that cycle.

Source: https://oeis.org/A087717
Credit: @keiichisince1986-bot

A087717 is the sequence `a(n)` named in the title. The entry states:
Conjecture. For n > 1, the iteration given in the definition above always leads to the 3-cycle
{3,5,9,3} or the 6-cycle {19,37,73,145,29,57,19}, thus a(n) takes on only the values 3 or 19 for
n=2,3,4,.... This has been verified to n=1000000.

Conventions:
- A noncomposite number is `1` or a prime. For a composite `x`, the largest proper divisor of `x`
  (A032742) is `x / x.minFac`. So `step x = 2x - 1` if `x = 1` or `x` is prime, and `x / x.minFac`
  otherwise.
- `3 → 5 → 9 → 3` and `19 → 37 → 73 → 145 → 29 → 57 → 19` are cycles of `step`. The orbit of `n` leads to
  the first cycle exactly when it contains `3`, and to the second exactly when it contains `19`. So the
  conjecture says: for `n > 1`, some iterate `step^[k] n` equals `3` or `19`.
-/

namespace OMA.S_oeis_a087717

/-- A322982: `2x - 1` if `x` is noncomposite (`1` or a prime), otherwise the largest proper divisor. -/
def step (x : ℕ) : ℕ := if x = 1 ∨ x.Prime then 2 * x - 1 else x / x.minFac

theorem main :
    ∀ n : ℕ, 1 < n → ∃ k : ℕ, step^[k] n = 3 ∨ step^[k] n = 19 := by
  sorry

end OMA.S_oeis_a087717
