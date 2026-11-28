import Mathlib

/-!
# A373162: a(n) = denominator of Sum_{k>=0} cos(2k*Pi/3)/n^k.

Source: https://oeis.org/A373162
Credit: @agchua

Comments of A373162 (the entry is by Clark Kimberling, Jul 22 2024; the comments are unsigned):
  The first five fractions are 5/7, 21/26, 6/7, 55/62, 39/43; the sequence of fractions is
  strictly increasing with limit 1.
  Conjecture: the sequence of fractions is completely monotonic.

Offset 2: the fractions are x(n) = Sum_{k>=0} cos(2k*Pi/3)/n^k for n >= 2 (for n = 1 the series
diverges). A real sequence y(n), n >= 2, is completely monotonic (in the standard sense of
Hausdorff) if (-1)^j (Delta^j y)(n) >= 0 for all j >= 0 and n >= 2, where
(Delta y)(n) = y(n+1) - y(n) is the forward difference (`fwdDiff 1` in Mathlib); the j-th
difference at n uses only y(n), ..., y(n+j).
The conjecture is stated in both possible readings, as a disjunction: in the standard sense for
the fractions x(n) themselves, and, because the entry says that the fractions increase to the
limit 1 (an increasing sequence is never completely monotonic in the standard sense), in the
same sense for the numbers 1 - x(n).
-/

namespace OMA.S_oeis_a373162

/-- The fraction x(n) = Sum_{k>=0} cos(2k*Pi/3)/n^k. -/
noncomputable def x (n : ℕ) : ℝ := ∑' k : ℕ, Real.cos (2 * (k : ℝ) * Real.pi / 3) / (n : ℝ) ^ k

/-- A real sequence y(n), n >= 2, is completely monotonic: (-1)^j (Delta^j y)(n) >= 0 for all
j >= 0 and n >= 2. -/
noncomputable def CM (y : ℕ → ℝ) : Prop :=
  ∀ j n : ℕ, 2 ≤ n → 0 ≤ (-1 : ℝ) ^ j * (fwdDiff 1)^[j] y n

/-- The conjecture, in both readings: the fractions x(n), n >= 2, are completely monotonic, or
the numbers 1 - x(n), n >= 2, are completely monotonic. -/
theorem main : CM x ∨ CM (fun n => 1 - x n) := by
  sorry

end OMA.S_oeis_a373162
