import Mathlib

/-!
# A275673: List of numbers that are in a spoke of a hexagonal spiral.

Source: https://oeis.org/A275673
Credit: @Harsha0912

The entry's comment: this sequence consists of the numbers of the form 3k^2 + bk + 1 for
nonnegative k and -2 <= b <= 3 (listed in increasing order, offset 1).

Conjectures in the entry (Colin Barker, Aug 05 2016; Luce Etienne, May 25 2017):
1. a(n) = 2*a(n-1) - a(n-2) + a(n-6) - 2*a(n-7) + a(n-8) for n > 8.
2. G.f.: x*(1-x^6+x^7) / ((1-x)^3*(1+x)*(1-x+x^2)*(1+x+x^2)).
3. a(n) = (n+4-3*floor((n+4)/6)-2)*floor((n+4)/6)+1.

Conventions:
* `S` is the set of numbers `3k^2 + bk + 1` with `k : ℕ` and integer `b` in `[-2, 3]`;
  `a n = Nat.nth S (n - 1)` is its `n`-th element in increasing order (`n >= 1`).
* The recurrence is stated in `ℤ`. The g.f. is stated by clearing the denominator in `ℤ⟦X⟧`,
  with coefficient `0` at `x^0` (offset 1) and `a n` at `x^n` for `n >= 1`.
* In the closed form, `n + 4 - 3 * ((n + 4) / 6) - 2` never truncates in `ℕ`, and it is stated
  for all `n >= 1`.
-/

namespace OMA.S_oeis_a275673

/-- The numbers `3k^2 + bk + 1` with `k >= 0` and `-2 <= b <= 3`. -/
def S : Set ℕ := {m | ∃ k : ℕ, ∃ b : ℤ, -2 ≤ b ∧ b ≤ 3 ∧ (m : ℤ) = 3 * k ^ 2 + b * k + 1}

/-- A275673 (offset 1): the `n`-th element of `S` in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth S (n - 1)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 2 * a (n - 1) - a (n - 2) + a (n - 6) - 2 * a (n - 7) + a (n - 8)) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
        ((1 - X) ^ 3 * (1 + X) * (1 - X + X ^ 2) * (1 + X + X ^ 2)) =
      X * (1 - X ^ 6 + X ^ 7)) ∧
    (∀ n : ℕ, 1 ≤ n →
      a n = (n + 4 - 3 * ((n + 4) / 6) - 2) * ((n + 4) / 6) + 1) := by
  sorry

end OMA.S_oeis_a275673

