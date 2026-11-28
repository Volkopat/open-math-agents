import Mathlib

/-!
# OEIS A203286: nondecreasing arrays of `2n` integers in `-3..3` with sum zero and balanced signs

Source: https://oeis.org/A203286
Credit: @goncalomsdias (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of arrays of `2n` nondecreasing integers in `-3..3` with sum zero and equal
numbers of entries greater than zero and less than zero, offset 1
(`4, 12, 28, 57, 104, 176, 280, 425, …`).

The formula field of the entry states, as unproved claims:
* (R. H. Hardin, "Empirical") `a(n) = 4a(n-1) - 5a(n-2) + 5a(n-4) - 4a(n-5) + a(n-6)`;
* (Colin Barker, Jun 04 2018, "Conjectures") the g.f. is
  `x (4 - 4x + 5x³ - 4x⁴ + x⁵) / ((1 - x)⁵ (1 + x))`;
* `a(n) = (48 + 80n + 52n² + 16n³ + 2n⁴)/48` for `n` even;
* `a(n) = (42 + 80n + 52n² + 16n³ + 2n⁴)/48` for `n` odd.
This file states all four, as one conjunction.

Conventions:
* An array of length `2n` is a function `Fin (2 * n) → ℤ`; "nondecreasing" is `Monotone`. The
  count is the `Set.ncard` of the (finite) set of such arrays with entries in `[-3, 3]`, sum `0`, and
  as many positive as negative entries. A brute-force count with these conventions reproduces the
  first eight terms of the entry.
* The offset is 1. The definition also makes sense at `n = 0` (the empty array, `1`), but that value
  is not a term of the sequence and is not used: the g.f. is `Σ_{n ≥ 1} a(n) xⁿ`, stated in
  `PowerSeries ℤ` with the denominator cleared (it is a unit there), the recurrence is stated for
  `n ≥ 7` (where every index is `≥ 1`), and the closed forms for `n ≥ 1`, in `ℚ`.
* An exact computation confirms all four claims on the forty terms of the entry's data.
-/

namespace OMA.S_oeis_a203286

open PowerSeries

/-- `A203286(n)`: nondecreasing `f : Fin (2n) → ℤ` with values in `[-3, 3]`, sum `0`, and as many
positive as negative entries. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {f : Fin (2 * n) → ℤ |
    Monotone f ∧ (∀ i, -3 ≤ f i ∧ f i ≤ 3) ∧ ∑ i, f i = 0 ∧
      (Finset.univ.filter fun i => 0 < f i).card = (Finset.univ.filter fun i => f i < 0).card}

/-- Hardin's empirical recurrence and Barker's conjectured g.f. and closed forms. -/
theorem main :
    (∀ n : ℕ, 7 ≤ n →
      (a n : ℤ) = 4 * a (n - 1) - 5 * a (n - 2) + 5 * a (n - 4) - 4 * a (n - 5) + a (n - 6)) ∧
    (PowerSeries.mk fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * ((1 - X) ^ 5 * (1 + X)) =
      X * (4 - 4 * X + 5 * X ^ 3 - 4 * X ^ 4 + X ^ 5) ∧
    (∀ n : ℕ, 1 ≤ n → Even n →
      (a n : ℚ) = (48 + 80 * n + 52 * n ^ 2 + 16 * n ^ 3 + 2 * n ^ 4) / 48) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n →
      (a n : ℚ) = (42 + 80 * n + 52 * n ^ 2 + 16 * n ^ 3 + 2 * n ^ 4) / 48) := by
  sorry

end OMA.S_oeis_a203286
