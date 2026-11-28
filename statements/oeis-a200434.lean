import Mathlib

/-!
# OEIS A200434: `-n..n` arrays of 7 elements with zero sum, no two or three adjacent summing to zero

Source: https://oeis.org/A200434
Credit: @goncalomsdias (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of `-n..n` arrays `x(0..6)` of 7 elements with zero sum and no two or three
adjacent elements summing to zero, offset 1 (0, 594, 9898, 67852, 293464, …).

The formula field of the entry states, as unproved claims:
* (R. H. Hardin, "Empirical") `a(n) = (5887/180)n⁶ - (5813/60)n⁵ + (6083/36)n⁴ - (2191/12)n³ + (9119/90)n² - (353/15)n`;
* (Colin Barker, May 21 2018, "Conjectures") the g.f. is `2x²(297 + 2870x + 5520x² + 2784x³ + 303x⁴) / (1 - x)⁷`;
* `a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7)` for `n > 7`.
This file states all three, as one conjunction.

Conventions:
* An array is a function `x : Fin 7 → ℤ` with every entry in `[-n, n]`. "No two adjacent elements
  summing to zero": `x i + x (i+1) ≠ 0` whenever `i + 1 < 7`; "no three": `x i + x (i+1) + x (i+2) ≠ 0`
  whenever `i + 2 < 7`. The count is the `Set.ncard` of the (finite) set of such arrays. A
  brute-force count with these conventions reproduces the first terms of the entry.
* The offset is 1: the empirical polynomial is stated for `n ≥ 1`, in `ℚ`; the g.f. is
  `Σ_{n ≥ 1} a(n) xⁿ`, in `PowerSeries ℤ` with the denominator `(1 - x)^7` cleared (a unit there);
  the recurrence for `n > 7`, in `ℤ`.
* An exact computation confirms all three claims on the 23 terms of the entry's data.
-/

namespace OMA.S_oeis_a200434

open PowerSeries

/-- `A200434(n)`: arrays `x : Fin 7 → ℤ` with entries in `[-n, n]`, zero sum, and no two or three
adjacent entries summing to zero. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : Fin 7 → ℤ |
    (∀ i, -(n : ℤ) ≤ x i ∧ x i ≤ n) ∧ ∑ i, x i = 0 ∧
      (∀ (i : ℕ) (h : i + 1 < 7), x ⟨i, by omega⟩ + x ⟨i + 1, h⟩ ≠ 0) ∧
      (∀ (i : ℕ) (h : i + 2 < 7), x ⟨i, by omega⟩ + x ⟨i + 1, by omega⟩ + x ⟨i + 2, h⟩ ≠ 0)}

/-- Hardin's empirical polynomial and Barker's conjectured g.f. and recurrence. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 5887 / 180 * n ^ 6 - 5813 / 60 * n ^ 5 + 6083 / 36 * n ^ 4 - 2191 / 12 * n ^ 3 + 9119 / 90 * n ^ 2 - 353 / 15 * n) ∧
    (PowerSeries.mk fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - X) ^ 7 =
      2 * X ^ 2 * (297 + 2870 * X + 5520 * X ^ 2 + 2784 * X ^ 3 + 303 * X ^ 4) ∧
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a200434
