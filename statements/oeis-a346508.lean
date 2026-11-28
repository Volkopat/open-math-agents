import Mathlib

/-!
# A346508: the ratio of consecutive terms tends to 1

Source: https://oeis.org/A346508
Credit: @ivillar

Status: known result: the entry records that the conjecture is true (Stefano Spezia).

A346508 (offset 1) lists the positive integers k such that 10*k + 1 is equal to the product of
two integers greater than 1 and ending with 1; data 12, 23, 34, 44, 45, 56, 65, 67, 78, ...
(for example 107 is a term because 21*51 = 1071 = 107*10 + 1).

Conjecture (in the formula section of A346508): lim_{n->oo} a(n)/a(n-1) = 1.
Stefano Spezia records in the entry that the conjecture is true.

Formalization: an integer ends with 1 when its residue modulo 10 is 1. `a n` for n ≥ 1 is the
n-th term in increasing order (`Nat.nth` counts from 0). The limit is taken in ℝ along n → ∞;
the values of the quotient at n ≤ 1 do not affect it.
-/

namespace OMA.S_oeis_a346508

/-- `k` is a term of A346508: `k > 0` and `10 k + 1 = x y` with `x, y > 1` both ending with 1. -/
def IsTerm (k : ℕ) : Prop :=
  0 < k ∧ ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x % 10 = 1 ∧ y % 10 = 1 ∧ x * y = 10 * k + 1

/-- `a n`, for `n ≥ 1`, is the `n`-th term of A346508 in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- The ratio of consecutive terms tends to 1. -/
theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (a (n - 1) : ℝ)) Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a346508
