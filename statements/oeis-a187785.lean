import Mathlib

/-!
# A187785: Number of ways to write n=x+y (x,y>=0) with {6x-1,6x+1} a twin prime pair and y a triangular number.

Source: https://oeis.org/A187785
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry; verified for n up to 2*10^8): a(n) > 0 for all n > 48624
not equal to 76106. (The remark that 723662 seems to be the unique n > 76106 which needs y = 0 is
not stated here.)

Formalization notes:
* Triangular numbers are t(t+1)/2, t ≥ 0. 6x - 1 prime forces x ≥ 1.
* Controls (computed): for 48000 ≤ n < 100000 the only n without a representation are 48624 and
  76106.
-/

namespace OMA.S_oeis_a187785



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ n : ℕ, 48624 < n → n ≠ 76106 → ∃ x t : ℕ, (6 * x - 1).Prime ∧ (6 * x + 1).Prime ∧
      x + t * (t + 1) / 2 = n := by
  sorry

end OMA.S_oeis_a187785
