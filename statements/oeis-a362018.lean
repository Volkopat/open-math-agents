import Mathlib

/-!
# A362018: Numbers k such that the digits of k^2 do not form a subsequence of the digits of 2^k.

Source: https://oeis.org/A362018
Credit: @azmiozgen

Conjecture (from the entry, see A362001): a(140) = 327 is the last term.

Formalization notes:
* "The digits of k^2 form a subsequence of the digits of 2^k" is stated with `List.Sublist` on the
  decimal digit lists `Nat.digits 10` (least significant digit first; reversing both lists does not
  change the subsequence relation). For k ≥ 1 both numbers are positive, so `Nat.digits` gives
  their usual digits.
* "327 is the last term" is stated as: 327 is a term, and every k > 327 is not a term.
* Controls (computed): among k < 3000 there are 140 terms, the last three being 263, 277, 327; the
  first ones are 0, 1, 3, 5, 6, as in the entry.
-/

namespace OMA.S_oeis_a362018

/-- `k` is a term: the digits of `k²` are not a subsequence of those of `2^k`. -/
def IsTerm (k : ℕ) : Prop := ¬ (Nat.digits 10 (k ^ 2)).Sublist (Nat.digits 10 (2 ^ k))

/-- 327 is the last term. -/
theorem main : IsTerm 327 ∧ ∀ k : ℕ, 327 < k → ¬ IsTerm k := by
  sorry

end OMA.S_oeis_a362018
