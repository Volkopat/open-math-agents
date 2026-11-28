import Mathlib

/-!
# OEIS A183690

R. H. Hardin counts arrays of height n+1 and width two over {0,1,2} in which
each pair of adjacent rows has nonzero integer determinant. The sequence
starts at index one. Colin Barker conjectured the generating function and
radical formula on April 4, 2018.

Source: https://oeis.org/A183690
Credit: @vlad-ds
-/

namespace OMA.S_oeis_a183690

abbrev Row := Fin 3 × Fin 3

def rows : List Row :=
  (List.finRange 3).flatMap fun i => (List.finRange 3).map fun j => (i, j)

def neighbors (r : Row) : List Row :=
  rows.filter fun s => r.1.val * s.2.val != r.2.val * s.1.val

/-- All ways to append n rows after r. -/
def extensions : Nat → Row → List (List Row)
  | 0, _ => [[]]
  | n + 1, r =>
    (neighbors r).flatMap fun s => (extensions n s).map (s :: ·)

def a (n : Nat) : Nat :=
  (rows.flatMap fun r => (extensions n r).map (r :: ·)).length

/-- The OEIS series starts at index one, so its constant coefficient is zero. -/
noncomputable def series : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℚ))

/-- The first equality gives the generating function by clearing its denominator,
whose constant term is one. In the second equality, division by 2^(n-1)
is the factor 2^(1-n) in Barker's formula for n ≥ 1. -/
theorem main :
    series * (1 - 5 * PowerSeries.X - 8 * PowerSeries.X ^ 2) =
      2 * PowerSeries.X * (25 + 32 * PowerSeries.X) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) =
        ((5 - Real.sqrt 57) ^ n * (-15 + 2 * Real.sqrt 57) +
          (5 + Real.sqrt 57) ^ n * (15 + 2 * Real.sqrt 57)) /
          (2 ^ (n - 1) * Real.sqrt 57) := by
  sorry

end OMA.S_oeis_a183690
