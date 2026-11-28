import OMAStatements.S_oeis_a087664
import Mathlib

/-! A087664 split by the parity of `n`.

For even `n` the start `n / 4` is an integer or a half-integer `l / 2` with `l` odd, and
Lagarias and Sloane proved (Approximate squaring, Experimental Math. 13 (2004), Theorem 1)
that a half-integer start above `3 / 2` always reaches an integer: writing `l = 2 t + 1`,
one step sends `t` to `(2 t - 1)(t + 1) / 2` and lowers the 2-adic valuation of `t - 1`
by one. That is `H1`, a classical case, not progress on the conjecture.

`H2` is the genuinely open part: starts `n / 4` with `n` odd, the quarter-integer case.
-/

namespace OMA.R_oeis_a087664_R1

open OMA.S_oeis_a087664

/-- Even starts: integers and half-integers `n / 4 ≥ 2` (Lagarias and Sloane). -/
def H1 : Prop := ∀ n : ℕ, 8 ≤ n → Even n → ∃ k : ℕ, ∃ m : ℤ, b n k = (m : ℚ)

/-- Odd starts: the open quarter-integer case. -/
def H2 : Prop := ∀ n : ℕ, 8 ≤ n → Odd n → ∃ k : ℕ, ∃ m : ℤ, b n k = (m : ℚ)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a087664.main := by
  intro h1 h2 n hn
  rcases Nat.even_or_odd n with he | ho
  · exact h1 n hn he
  · exact h2 n hn ho

end OMA.R_oeis_a087664_R1
