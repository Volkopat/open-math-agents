import Mathlib

/-!
# Does every `n` occur as a digit string in some power of `2`?

Source: https://math.stackexchange.com/questions/3371305
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: given `n ∈ ℕ`, does there exist `k ∈ ℕ` such that the decimal representation of `2^k`
contains that of `n` as a (contiguous) substring? (E.g. `53` occurs in `2¹⁶ = 65536`.) `main`
states the answer yes.

Conventions:
* Decimal strings are the digit lists `Nat.digits 10` (least significant first; a contiguous
  block of the reversed list is a contiguous block of the list). For `n = 0` the string is `0`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mse_3371305

/-- Decimal digits, with `0` written as `[0]`. -/
def digs (n : ℕ) : List ℕ := if n = 0 then [0] else Nat.digits 10 n

/-- Every `n` occurs as a contiguous digit block of some `2^k`. -/
theorem main : ∀ n : ℕ, ∃ k : ℕ, digs n <:+: digs (2 ^ k) := by
  sorry

end OMA.S_mse_3371305
