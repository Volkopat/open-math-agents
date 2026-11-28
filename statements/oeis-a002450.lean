import Mathlib

/-!
# A002450: a(n) = (4^n - 1)/3

Source: https://oeis.org/A002450
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

OEIS comment ("Collatz Conjecture Corollary"): except for powers of `2`, the Collatz iteration
of any positive integer must eventually reach some `a(n) = (4ⁿ - 1)/3` and hence terminate at `1`.

## Encoding

* The Collatz map is `n ↦ n / 2` for even `n` and `n ↦ 3n + 1` for odd `n`.
* "Reach `a(n)`" is read with `n ≥ 2` (so `a(n) ∈ {5, 21, 85, …}`): these are the odd numbers
  `x > 1` with `3x + 1` a power of two, i.e. the points from which a trajectory that does not
  start at a power of two enters the powers of two. (Allowing `a(1) = 1` would make the statement
  literally the Collatz conjecture.)
-/

namespace OMA.S_oeis_a002450

/-- One step of the Collatz map. -/
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

theorem main :
    ∀ n : ℕ, 0 < n → (¬ ∃ e : ℕ, n = 2 ^ e) →
      ∃ m k : ℕ, 2 ≤ k ∧ collatz^[m] n = (4 ^ k - 1) / 3 := by
  sorry

end OMA.S_oeis_a002450
