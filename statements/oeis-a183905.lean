import Mathlib

/-!
# A183905: Number of nondecreasing arrangements of n+2 numbers in 0..2 with each number being the sum mod 3 of two others.

Source: https://oeis.org/A183905
Credit: @rickmanelius

Conjectures from Colin Barker, Apr 05 2018: G.f.: x*(1 + x + x^2 - 2*x^3) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>4.

Formalization notes:
* Offset 1. An arrangement of n+2 numbers in 0..2 is a function s : Fin (n + 2) → Fin 3
  (position ↦ number). It is nondecreasing when s i ≤ s j for all positions i ≤ j. Each number
  is the sum mod 3 of two others: for every position i there are positions j and k, different
  from each other and from i, with s i = (s j + s k) mod 3 (computed on the values in ℕ).
  `a n` is the number of such arrangements s.
* The data begin 1, 4, 10, 17, 25, 34, ..., matching the entry: n = 1, ..., 8 were checked by
  brute force over all arrangements with this definition, and the whole b-file (n = 1..200)
  against an equivalent count of the multiplicities of 0, 1 and 2. Reading the two others as
  two positions that may coincide (j = k allowed) gives other values, so the two others are
  two distinct positions.
* The g.f. is the series Sum_{n ≥ 1} a(n) x^n (offset 1), written as `PowerSeries.mk` of
  n ↦ a(n). Its coefficient at x^0 is the value of the definition at n = 0, which counts
  arrangements of 2 numbers; there each number has only one other, so that value is 0 and the
  series is exactly the sum over n ≥ 1. The identity is stated over ℤ⟦X⟧ with the denominator
  (1 - x)^3 cleared; it has constant coefficient 1, a unit, so this is equivalent to the
  quotient form of the entry.
* The recurrence is stated in ℤ for every n > 4, as in the entry; then n - 3 ≥ 2, so the
  natural-number subtractions n - 1, n - 2, n - 3 are exact.
* The empirical formula a(n) = (1/2)*n^2 + (7/2)*n - 5 for n>1 of the entry is not part of
  the conjectures quoted above and is not stated.
-/

namespace OMA.S_oeis_a183905

open PowerSeries

/-- The arrangement s of N numbers in 0..2 is nondecreasing, and each of its numbers is the
sum mod 3 of two others (at two positions different from each other and from its own). -/
abbrev Good {N : ℕ} (s : Fin N → Fin 3) : Prop :=
  (∀ i j : Fin N, i ≤ j → s i ≤ s j) ∧
    ∀ i : Fin N, ∃ j k : Fin N, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
      (s i : ℕ) = ((s j : ℕ) + (s k : ℕ)) % 3

/-- A183905: the number of nondecreasing arrangements of n+2 numbers in 0..2 with each number
being the sum mod 3 of two others. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun s : Fin (n + 2) → Fin 3 => Good s)).card

/-- Barker's conjectures on A183905: the g.f. x (1 + x + x^2 - 2x^3)/(1 - x)^3 of a(1), a(2),
..., with the denominator cleared, and the recurrence of order 3 for n > 4. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 : PowerSeries ℤ) =
      X * (1 + X + X ^ 2 - 2 * X ^ 3) ∧
    ∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a183905
