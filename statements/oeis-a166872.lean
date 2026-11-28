import Mathlib

/-!
# A166872: a(n) = floor(n/2 + 2 - sqrt(17/4 + 2*n)).

Source: https://oeis.org/A166872
Credit: @Squee451

Data (offset 1): 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 8, 8, 8, 9, 9, 10, ...

The entry's comment (Robert Israel, 27 May 2016): Each nonnegative integer k occurs 2 to 6 times in
the sequence, with 0 occurring 6 times, 3 occurring 4 times, all others either 2 or 3 times.
Conjecture: The sequence of integers k which occur 3 times has the g.f.
(1 + 2*x^2 - 2*x^3 + x^6 - x^8 - x^9 + x^11)/(1 - 2*x + x^2 - x^8 + 2*x^9 - x^10).

In the data the values occurring exactly three times begin 1, 2, 5, 6, 7, 8, ..., and the series
expansion of the conjectured g.f. begins 1 + 2*x + 5*x^2 + 6*x^3 + ..., so the sequence of such k is
indexed from 0 in increasing order.

Conventions.
* The sequence has offset 1: `multiplicity k` counts the indices `n ≥ 1` with `a n = k`.
* "The sequence of integers k which occur 3 times" is the increasing enumeration `b 0 < b 1 < ...` of
  the set of `k` with multiplicity 3; the statement asserts that such an enumeration exists (so
  that set is infinite) and that its generating function is the conjectured rational function. The
  identity is written with the denominator cleared, as an identity of formal power series over ℤ
  (the denominator has constant term 1).
-/

namespace OMA.S_oeis_a166872

open PowerSeries

/-- A166872: `a n = ⌊n/2 + 2 - sqrt(17/4 + 2n)⌋`. -/
noncomputable def a (n : ℕ) : ℤ :=
  ⌊(n : ℝ) / 2 + 2 - Real.sqrt (17 / 4 + 2 * (n : ℝ))⌋

/-- The number of indices `n ≥ 1` with `a n = k`. -/
noncomputable def multiplicity (k : ℕ) : ℕ := {n : ℕ | 1 ≤ n ∧ a n = (k : ℤ)}.ncard

theorem main : ∃ b : ℕ → ℕ, StrictMono b ∧ (∀ k : ℕ, (∃ j, b j = k) ↔ multiplicity k = 3) ∧
    (PowerSeries.mk (fun j => (b j : ℤ)) * (1 - 2 * X + X ^ 2 - X ^ 8 + 2 * X ^ 9 - X ^ 10) =
      (1 + 2 * X ^ 2 - 2 * X ^ 3 + X ^ 6 - X ^ 8 - X ^ 9 + X ^ 11 : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a166872
