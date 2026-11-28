import Mathlib

namespace OMA.S_oeis_a205572

theorem main :
    ∀ a : ℕ → ℤ,
      (let A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ))
       let C : PowerSeries ℚ :=
         PowerSeries.mk (fun n =>
           (if 4 ∣ n then (1 : ℚ) else -1) / (Nat.factorial n : ℚ))
       A * C = 1) →
      ∀ (k n : ℕ), 1 ≤ n →
        a (2 ^ n + k) ≡ a k [ZMOD (2 ^ n : ℤ)] := by
  sorry

end OMA.S_oeis_a205572
