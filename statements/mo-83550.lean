import Mathlib

/-!
# Has `n² |sin n|` a limit?

Source: https://mathoverflow.net/questions/83550
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (MathOverflow): is there a subsequence `n_k` with `n_k² |sin n_k| → 0`? In other words,
does `lim n² |sin n|` exist (equal to infinity), or is there no such limit?

Conventions:
* The two readings in the source are complementary only in part; we state the "limit is
  infinity" alternative, `n² |sin n| → ∞` as `n → ∞` over the naturals. (If it holds, no
  subsequence tends to `0`; it is the yes answer to "does the limit exist".)
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_83550

theorem main :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * |Real.sin n|) Filter.atTop Filter.atTop := by
  sorry

end OMA.S_mo_83550
