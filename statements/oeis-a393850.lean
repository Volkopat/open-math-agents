import Mathlib

namespace OMA.S_oeis_a393850

theorem main :
    ∀ a : ℕ → ℤ,
      a 0 = 1 →
      a 1 = 1 →
      (let A : PowerSeries ℤ := PowerSeries.mk a
       ∀ n : ℕ, 1 ≤ n →
         PowerSeries.coeff n (A ^ (n + 1)) =
           (n : ℤ) * ((n : ℤ) + 1) * PowerSeries.coeff (n - 1) (A ^ (n + 1))) →
      ∀ n : ℕ, 1 ≤ n →
        (Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a393850
