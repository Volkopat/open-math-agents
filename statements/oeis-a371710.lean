import Mathlib

namespace OMA.S_oeis_a371710

theorem main :
    ∀ a : ℕ → ℤ,
      a 0 = 0 →
      (∀ k : ℕ,
        let A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ))
        ∑ n ∈ Finset.range (k + 1),
          (1 / (Nat.factorial n : ℚ)) *
            PowerSeries.coeff k ((A ^ n - PowerSeries.X) ^ n) =
        if k = 0 then 1 else 0) →
      ∀ n : ℕ, 0 < n →
        a (6 * n) % 3 = 2 ∧
        a (6 * n + 1) % 3 = 0 ∧
        a (6 * n + 2) % 3 = 2 ∧
        a (6 * n + 3) % 3 = 1 ∧
        a (6 * n + 4) % 3 = 2 ∧
        a (6 * n + 5) % 3 = 2 := by
  sorry

end OMA.S_oeis_a371710
