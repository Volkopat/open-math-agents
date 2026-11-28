import Mathlib

/-!
# OEIS A176542

Source: https://oeis.org/A176542 (OEIS Foundation, CC BY-SA 4.0).
Andrew Weimholt's sequence comprises the positive lengths for which a finite nonzero
number of blocks of consecutive triangular numbers have square sum. Blocks are
identified with their nonnegative starting indices, beginning at triangular number zero.
The claims of Colin Barker are proved by Sela Fried in
https://oeis.org/A176542/a176542.pdf. See also Theorem 34 and Corollary 35 of
https://arxiv.org/abs/2607.24832.
-/

namespace OMA.S_oeis_a176542

/-- The sum of the block of length `n` beginning at triangular index `j`. -/
def block (n j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (((j + k + 1).choose 2 : ℕ) : ℤ)

/-- Starting indices with a square block sum. -/
def starts (n : ℕ) : Set ℕ := {j | ∃ x : ℕ, block n j = (x : ℤ) ^ 2}

/-- The positive lengths comprising the sequence. -/
def lengths : Set ℕ := {n | 0 < n ∧ (starts n).Nonempty ∧ (starts n).Finite}

open PowerSeries in
/-- The increasing enumeration with Barker's formulas, recurrence and
denominator-cleared generating function. Coefficient zero is set to zero. -/
theorem main :
    ∃ a : ℕ → ℕ, a 0 = 0 ∧ StrictMono a ∧ lengths = a '' Set.Ioi 0 ∧
      (∀ n : ℕ, 0 < n →
        a n = if Even n then (9 * n ^ 2 + 24 * n + 16) / 2
          else (9 * n ^ 2 + 30 * n + 25) / 2) ∧
      (∀ n : ℕ, 5 < n →
        (a n : ℤ) = (a (n - 1) : ℤ) + 2 * (a (n - 2) : ℤ) -
          2 * (a (n - 3) : ℤ) - (a (n - 4) : ℤ) + (a (n - 5) : ℤ)) ∧
      (PowerSeries.mk (fun n => (a n : ℤ))) * (1 - X) ^ 3 * (1 + X) ^ 2 =
        2 * X * (4 * X ^ 4 - 3 * X ^ 3 - 8 * X ^ 2 + 9 * X + 16) := by
  sorry

end OMA.S_oeis_a176542
