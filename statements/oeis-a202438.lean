import Mathlib

namespace OMA.S_oeis_a202438

theorem main :
    ∀ a : ℕ → ℤ,
      (let A : PowerSeries ℤ := PowerSeries.mk a
       let B : PowerSeries ℤ :=
         PowerSeries.mk (fun m =>
           ∑ n ∈ Finset.range (m + 1),
             if n * (n + 1) / 2 = m then
               (9 : ℤ) ^ n * (2 * (n : ℤ) + 1) * (-1 : ℤ) ^ m
             else 0)
       A ^ 3 * B = 1) →
      ∀ n : ℕ, (7 : ℤ) ∣ a (7 * n + 5) := by
  sorry

end OMA.S_oeis_a202438
