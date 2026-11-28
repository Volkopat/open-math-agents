import Mathlib

/-!
# OEIS A078441: Garner's conjecture on runs of equal Collatz height

Source: https://oeis.org/A078441
`h(k)` is the length of the Collatz trajectory `k, f(k), f(f(k)), …, 1` (up to the first `1`),
with `f(k) = k/2` for even `k` and `3k + 1` for odd `k`. Garner (1985) conjectured that there
are arbitrarily long runs of consecutive positive integers with the same height; this is what
makes `a(n)` (the start of the first run of length `n`) exist for every `n`.

Conventions. `ReachesIn k t` says that the trajectory of `k` first hits `1` after exactly `t`
steps (so `h(k) = t + 1`); integers whose trajectory never reaches `1` have no height.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a078441

/-- The Collatz map. -/
def f (k : ℕ) : ℕ := if k % 2 = 0 then k / 2 else 3 * k + 1

/-- The trajectory of `k` first reaches `1` after exactly `t` steps. -/
def ReachesIn (k t : ℕ) : Prop := f^[t] k = 1 ∧ ∀ j < t, f^[j] k ≠ 1

theorem main :
    ∀ L : ℕ, ∃ n t : ℕ, 1 ≤ n ∧ ∀ i < L, ReachesIn (n + i) t := by
  sorry

end OMA.S_oeis_a078441
