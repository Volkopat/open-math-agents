import Mathlib

namespace OMA.S_oeis_a386648

theorem main :
    ∀ a : ℕ → ℤ,
      a 0 = 0 →
      (∀ k : ℕ,
        let A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ))
        let W : PowerSeries ℚ :=
          PowerSeries.mk (fun n => if n = 0 then 0 else -(((n : ℤ) ^ (n - 1) : ℤ) : ℚ) / (Nat.factorial n : ℚ))
        ∑ n ∈ Finset.range (k + 1),
          (1 / (Nat.factorial n : ℚ)) *
            PowerSeries.coeff k ((A ^ n + W) ^ n) =
        if k = 0 then 1 else 0) →
      ∀ n : ℕ, 6 < n →
        a n % 6 =
          if n % 6 = 1 then 2
          else if n % 6 = 2 then 3
          else if n % 6 = 3 then 4
          else if n % 6 = 4 then 3
          else if n % 6 = 5 then 2
          else 5 := by
  sorry

end OMA.S_oeis_a386648
