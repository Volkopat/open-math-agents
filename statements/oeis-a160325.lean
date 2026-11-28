import Mathlib

/-!
# A160325: Number of ways to express n=0,1,2,... as the sum of a triangular number, an even square and a pentagonal number.

Source: https://oeis.org/A160325
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, April 2009, from the entry): a(n) > 0 for every n = 0, 1, 2, 3, ...

Formalization notes:
* Triangular numbers t(t+1)/2 (t ≥ 0), even squares (2j)^2 (j ≥ 0) and pentagonal numbers
  k(3k-1)/2 (k ≥ 0). a(n) > 0 is stated as the existence of a representation.
* Controls (computed): every n < 5000 has a representation.
-/

namespace OMA.S_oeis_a160325



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ n : ℕ, ∃ t j k : ℕ, t * (t + 1) / 2 + (2 * j) ^ 2 + k * (3 * k - 1) / 2 = n := by
  sorry

end OMA.S_oeis_a160325
