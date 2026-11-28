import Mathlib

/-!
# A006667: no fixed point of the tripling-step count

Source: https://oeis.org/A006667
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A006667): the sequence has no fixed point, where `a(n)` is the number of
tripling steps to reach `1` from `n` in the `3x+1` problem, or `-1` if `1` is never reached.

Conventions:
* `T(x) = x/2` for even `x` and `3x + 1` for odd `x`; a tripling step is an application to an odd
  `x`. The count is over the trajectory until it first reaches `1`.
* A fixed point is `n ≥ 1` with `a(n) = n`; since `a(n) = -1 ≠ n` when `1` is never reached, the
  statement says: no `n ≥ 1` reaches `1` after exactly `n` tripling steps.
-/

namespace OMA.S_oeis_a006667

/-- The Collatz map. -/
def T (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 1

/-- Number of tripling steps among the first `s` steps from `n`. -/
def tripl (n s : ℕ) : ℕ := ((Finset.range s).filter (fun i => T^[i] n % 2 = 1)).card

theorem main :
    ∀ n s : ℕ, 1 ≤ n → T^[s] n = 1 → (∀ i < s, T^[i] n ≠ 1) → tripl n s ≠ n := by
  sorry

end OMA.S_oeis_a006667
