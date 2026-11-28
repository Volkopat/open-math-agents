import Mathlib

namespace OMA.S_oeis_a245658

/-- Polynomial `P_n(x) = (∑_{k=0}^{n+1} C(n+1, k)^3 * (-x)^k)^3` defining OEIS A247031. -/
noncomputable def polyA247031 (n : ℕ) : PowerSeries ℤ :=
  (∑ k ∈ Finset.range (n + 2),
    PowerSeries.C ((Nat.choose (n + 1) k : ℤ) ^ 3 * (-1 : ℤ) ^ k) * PowerSeries.X ^ k) ^ 3

theorem main :
    ∀ (a b : ℕ → ℤ) (A B : PowerSeries ℤ),
      A = PowerSeries.mk a →
      B = PowerSeries.mk b →
      (∀ m : ℕ, (∑ n ∈ Finset.range (m + 1),
        PowerSeries.coeff m (PowerSeries.C (b n) * PowerSeries.X ^ n * polyA247031 n)) =
        if m = 0 then 1 else 0) →
      A ^ 3 = B →
      ∀ n : ℕ, (a n % 3 = 2 ↔ b (3 * n) % 3 = 2) := by
  sorry

end OMA.S_oeis_a245658
