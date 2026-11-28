import Mathlib

/-!
# A367396: subsets whose cardinality is a sum of two distinct members

Source: https://oeis.org/A367396
Credit: @rodolfoquint

The two conjectures attributed to Chai Wah Wu on November 21, 2023 are the
recurrence for n > 4 and the ordinary generating function of this offset-zero
sequence. The generating-function formula is stated after multiplication by
its denominator, whose constant term is -1 and hence is invertible.
-/

namespace OMA.S_oeis_a367396

/-- Count qualifying subsets of {1,...,n}, counting each subset only once. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact (((Finset.Icc 1 n).powerset).filter fun s =>
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ x + y = s.card).card

theorem main :
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 4 * (a (n - 1) : ℤ) - 5 * (a (n - 2) : ℤ) +
        4 * (a (n - 3) : ℤ) - 5 * (a (n - 4) : ℤ) + 2 * (a (n - 5) : ℤ)) ∧
    (let x : PowerSeries ℤ := PowerSeries.X
     PowerSeries.mk (fun n => (a n : ℤ)) *
       ((2 * x - 1) * (x ^ 4 - 2 * x ^ 3 + x ^ 2 - 2 * x + 1)) =
       x ^ 3 * (x - 1)) := by
  sorry

end OMA.S_oeis_a367396
