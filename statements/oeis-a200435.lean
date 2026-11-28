import Mathlib

/-!
# OEIS A200435: `-n..n` arrays of 8 elements with zero sum, no two or three adjacent summing to zero

Source: https://oeis.org/A200435
Credit: @goncalomsdias (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of `-n..n` arrays `x(0..7)` of 8 elements with zero sum and no two or three
adjacent elements summing to zero, offset 1 (0, 1928, 50592, 473034, 2591502, …).

The formula field of the entry states, as unproved claims:
* (R. H. Hardin, "Empirical") `a(n) = (19328/315)n⁷ - (18373/90)n⁶ + (18602/45)n⁵ - (20887/36)n⁴ + (46687/90)n³ - (48359/180)n² + (12499/210)n`;
* (Colin Barker, May 21 2018, "Conjectures") the g.f. is `2x²(964 + 17584x + 61141x² + 57919x³ + 15963x⁴ + 1053x⁵) / (1 - x)⁸`;
* `a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8)` for `n > 8`.
This file states all three, as one conjunction.

Conventions:
* An array is a function `x : Fin 8 → ℤ` with every entry in `[-n, n]`. "No two adjacent elements
  summing to zero": `x i + x (i+1) ≠ 0` whenever `i + 1 < 8`; "no three": `x i + x (i+1) + x (i+2) ≠ 0`
  whenever `i + 2 < 8`. The count is the `Set.ncard` of the (finite) set of such arrays. A
  brute-force count with these conventions reproduces the first terms of the entry.
* The offset is 1: the empirical polynomial is stated for `n ≥ 1`, in `ℚ`; the g.f. is
  `Σ_{n ≥ 1} a(n) xⁿ`, in `PowerSeries ℤ` with the denominator `(1 - x)^8` cleared (a unit there);
  the recurrence for `n > 8`, in `ℤ`.
* An exact computation confirms all three claims on the 21 terms of the entry's data.
-/

namespace OMA.S_oeis_a200435

open PowerSeries

/-- `A200435(n)`: arrays `x : Fin 8 → ℤ` with entries in `[-n, n]`, zero sum, and no two or three
adjacent entries summing to zero. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : Fin 8 → ℤ |
    (∀ i, -(n : ℤ) ≤ x i ∧ x i ≤ n) ∧ ∑ i, x i = 0 ∧
      (∀ (i : ℕ) (h : i + 1 < 8), x ⟨i, by omega⟩ + x ⟨i + 1, h⟩ ≠ 0) ∧
      (∀ (i : ℕ) (h : i + 2 < 8), x ⟨i, by omega⟩ + x ⟨i + 1, by omega⟩ + x ⟨i + 2, h⟩ ≠ 0)}

/-- Hardin's empirical polynomial and Barker's conjectured g.f. and recurrence. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 19328 / 315 * n ^ 7 - 18373 / 90 * n ^ 6 + 18602 / 45 * n ^ 5 - 20887 / 36 * n ^ 4 + 46687 / 90 * n ^ 3 - 48359 / 180 * n ^ 2 + 12499 / 210 * n) ∧
    (PowerSeries.mk fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - X) ^ 8 =
      2 * X ^ 2 * (964 + 17584 * X + 61141 * X ^ 2 + 57919 * X ^ 3 + 15963 * X ^ 4 + 1053 * X ^ 5) ∧
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a200435
