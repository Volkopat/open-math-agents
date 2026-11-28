import Mathlib

-- Is the nim-sequence of Grundy's game eventually periodic?
-- Source: https://en.wikipedia.org/wiki/Grundy%27s_game
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
Source: in Grundy's game a move splits a single heap into two heaps of different sizes (both
nonempty). By the Sprague–Grundy theorem each heap size `n` has an equivalent nim-heap size, the
nim-value `g(n)` (OEIS A002188: 0, 0, 0, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 3, 2, 1, 3, 2, 4, 3, 0, ...).
Whether this sequence is eventually periodic is open; Berlekamp, Conway and Guy conjectured that
it is, and that is the form stated here.

Conventions:
* `g(n)` is the Sprague–Grundy value: the minimal excludant (least natural number not attained)
  of `g(a) xor g(n - a)` over all splits `n = a + (n - a)` with `0 < a < n - a`; taking the
  smaller part `a` lists every unordered split into unequal nonempty heaps exactly once. Nim-sum
  is bitwise xor `^^^` on `ℕ`. The set of excluded values is cofinite, so `sInf` is the mex.
* Eventually periodic: there are `N` and a period `p > 0` with `g(n + p) = g(n)` for all `n ≥ N`.
-/

namespace OMA.S_wp_is_the_nim_sequence_of_grundy_s_game_eventually_periodic

/-- The nim-value of a heap of size `n` in Grundy's game. -/
noncomputable def grundy (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ a : ℕ, (h : 0 < a ∧ 2 * a < n) → m ≠ grundy a ^^^ grundy (n - a)}
decreasing_by all_goals omega

/-- The nim-sequence of Grundy's game is eventually periodic. -/
theorem main : ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n → grundy (n + p) = grundy n := by
  sorry

end OMA.S_wp_is_the_nim_sequence_of_grundy_s_game_eventually_periodic
