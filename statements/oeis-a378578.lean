import Mathlib

namespace OMA.S_oeis_a378578

/-- Removing all factors of 3 from an integer `m`: `m / 3^(v_3(m))`. -/
def removeThrees (m : ℤ) : ℤ :=
  if m = 0 then 0 else m / (3 : ℤ) ^ (padicValInt 3 m)

theorem main :
    ∀ (A : PowerSeries ℤ),
      (∀ n : ℕ, PowerSeries.coeff n A =
        removeThrees (PowerSeries.coeff n (1 + PowerSeries.X * A ^ 3))) →
      ∀ n : ℕ, PowerSeries.coeff n A % 2 = ((Nat.choose (3 * n) n / (2 * n + 1) : ℕ) : ℤ) % 2 := by
  sorry

end OMA.S_oeis_a378578
