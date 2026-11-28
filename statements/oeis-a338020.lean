import Mathlib

/-!
# A338020: circles of positive integer area with radius strictly between `n - 1` and `n`

Source: https://oeis.org/A338020
Credit: @avivorly

Definition (OEIS A338020, offset 1): a(n) is the number of circles of positive integer area with radii less than n and
greater than n - 1.

Conjecture (Torlach Rush, in the entry, verbatim): Conjecture: k >= 2, each triple Tr(k) = {a(k), a(k+1), a(k+2)} gives
the sides of an integer-sided triangle, and {(a(k+2) - a(k)), (a(k+2) - a(k+1)), (a(k+1) - a(k))} is a degenerate
integer-sided triangle.

Conventions:
- A circle of radius `r > 0` has area `π r ^ 2`, so a circle of positive integer area `A` has radius `√(A / π)`, and
  `a n` counts the positive integers `A` with `n - 1 < √(A / π) < n` (radii are real numbers; both inequalities are
  strict, as in the entry). For `n ≥ 1` this is the same as `π (n - 1) ^ 2 < A < π n ^ 2` (square the inequalities,
  all sides being `≥ 0`, and multiply by `π > 0`). The entry's PARI program counts the `A ≥ 1` with `√(A / π) < n` and
  subtracts the same count for `n - 1`, i.e. it counts `π (n - 1) ^ 2 ≤ A < π n ^ 2`; this agrees with the strict
  reading since `π m ^ 2` is never a positive integer (`π` is irrational). With this definition `a 1 = 3`, `a 2 = 9`,
  `a 3 = 16`, `a 4 = 22`, matching the entry's data.
- `a` is defined for every `n : ℕ` (as a count of a finite set); the conjecture only uses `n ≥ 2`.
- Gives the sides of an integer-sided triangle: the three values `a k`, `a (k + 1)`, `a (k + 2)` are positive integers
  and satisfy the three strict triangle inequalities (each is less than the sum of the other two).
- Is a degenerate integer-sided triangle: with `x = a(k+2) - a(k)`, `y = a(k+2) - a(k+1)`, `z = a(k+1) - a(k)`, computed
  in `ℤ`, the sides `y` and `z` are positive integers and the largest side `x` equals the sum `y + z` of the other two,
  i.e. the sides are positive and one triangle inequality holds with equality. (`x = y + z` is an identity; `0 < y` and
  `0 < z` also give `0 < x` and that `x` is the largest side.)
- `k` ranges over the naturals with `k ≥ 2`, as in the conjecture.
-/

namespace OMA.S_oeis_a338020

/-- `a n` is the number of circles of positive integer area whose radius lies strictly between `n - 1` and `n`: the
number of positive integers `A` (the area) with `n - 1 < √(A / π) < n`, `√(A / π)` being the radius of a circle of
area `A`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {A : ℕ | 0 < A ∧ ((n : ℝ) - 1) < Real.sqrt ((A : ℝ) / Real.pi) ∧
    Real.sqrt ((A : ℝ) / Real.pi) < n}

theorem main :
    ∀ k : ℕ, 2 ≤ k →
      (0 < a k ∧ 0 < a (k + 1) ∧ 0 < a (k + 2) ∧
        a k < a (k + 1) + a (k + 2) ∧ a (k + 1) < a k + a (k + 2) ∧ a (k + 2) < a k + a (k + 1)) ∧
      (0 < (a (k + 2) : ℤ) - a (k + 1) ∧ 0 < (a (k + 1) : ℤ) - a k ∧
        (a (k + 2) : ℤ) - a k = ((a (k + 2) : ℤ) - a (k + 1)) + ((a (k + 1) : ℤ) - a k)) := by
  sorry

end OMA.S_oeis_a338020
