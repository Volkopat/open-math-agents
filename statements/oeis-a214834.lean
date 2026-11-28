import Mathlib

/-!
# A214834

Source: https://oeis.org/A214834
Credit: @eltociear

The source (COMMENTS) writes any even number of the form 4k + 2 with k > 0 as
(4i + 3) + (4j + 3) with i + j + 1 = k, because 4(i + j + 1) + 2 = (4i + 3) + (4j + 3),
and conjectures that for every such k there is a partition for which both 4i + 3 and
4j + 3 are prime. The source reports the conjecture tested true up to n = 1000000000.

The statement below is that conjecture: for every k > 0 there are natural numbers i and j
with i + j + 1 = k such that 4i + 3 and 4j + 3 are both prime. The two parts of the
partition are themselves the terms 4i + 3 and 4j + 3, so their being of the form 4m + 3
is built into the statement.
-/

namespace OMA.S_oeis_a214834

theorem main :
    ∀ k : ℕ, 0 < k → ∃ i j : ℕ, i + j + 1 = k ∧ (4 * i + 3).Prime ∧ (4 * j + 3).Prime := by
  sorry

end OMA.S_oeis_a214834
-- ci: re-run check-proof
