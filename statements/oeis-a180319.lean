import Mathlib

/-!
# A180319: total number of knight moves on an n X 2n chessboard

Source: https://oeis.org/A180319
Credit: @xor2k

Formalizes all three OEIS A180319 conjectures (offset 1):
Conjecture: a(n) = 4*(4-9*n+4*n^2) for n>1. a(n) = 3*a(n-1)-3*a(n-2)+a(n-3) for n>4.
G.f.: 4*x^2*(2+7*x-x^2)/(1-x)^3.

Conventions:
* The board has squares `(i, j)` with `i < n` and `j < 2 * n`. `a n` counts ordered pairs
  (start square, target square) of board squares that differ by a standard knight move, i.e. the
  absolute coordinate differences are `1` and `2` in some order. This is the total number of
  possible moves of a knight placed anywhere; it matches the OEIS data for `n = 1, ..., 41`.
* The closed form and the recurrence are stated in `ℤ`, so no natural subtraction is involved
  (the indices `n - 1, n - 2, n - 3` are at least `2` for `n > 4`).
* The g.f. (offset 1) is `Σ_{n ≥ 1} a(n) x^n`, written as a power series over `ℚ` whose constant
  coefficient is `0`; the identity g.f. `= P / (1 - x) ^ 3` is stated as
  g.f. `* (1 - x) ^ 3 = P`, which is equivalent since `(1 - x) ^ 3` is invertible.
-/

namespace OMA.S_oeis_a180319

/-- The squares of an `n × 2n` board. -/
def board (n : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range n ×ˢ Finset.range (2 * n)

/-- Number of ordered pairs of squares of the `n × 2n` board that are a knight move apart. -/
def a (n : ℕ) : ℕ :=
  ((board n ×ˢ board n).filter (fun pq : (ℕ × ℕ) × (ℕ × ℕ) =>
    (((pq.1.1 : ℤ) - pq.2.1).natAbs = 1 ∧ ((pq.1.2 : ℤ) - pq.2.2).natAbs = 2) ∨
    (((pq.1.1 : ℤ) - pq.2.1).natAbs = 2 ∧ ((pq.1.2 : ℤ) - pq.2.2).natAbs = 1))).card

/-- Closed form for `n > 1`, linear recurrence for `n > 4`, and the generating function. -/
theorem main :
    (∀ n : ℕ, 1 < n → (a n : ℤ) = 4 * (4 - 9 * n + 4 * n ^ 2)) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - PowerSeries.X) ^ 3 =
      4 * PowerSeries.X ^ 2 * (2 + 7 * PowerSeries.X - PowerSeries.X ^ 2)) := by
  sorry

end OMA.S_oeis_a180319
