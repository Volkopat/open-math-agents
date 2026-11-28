import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Combinatorics.Enumerative.Partition.Basic

namespace OMA.S_oeis_a356508

/-!
OEIS A356508: G.f. A(x) satisfies 2 = Product_{n>=1} (1 + x^n * A(x)) * (1 + x^(n-1) / A(x)).
For any degree r, factors with n > r + 1 have valuation >= r + 1, so the coefficient of x^r
equals that of the truncated product over n = 1..r+1.
Conjecture: a(n) == 2 (mod 4) at n = 2*k for all k > 0 that have an odd number of partitions
(A052002), otherwise a(n) == 0 (mod 4) when n > 0.
-/

theorem main : ∀ (A : PowerSeries ℤ),
    PowerSeries.constantCoeff A = 1 →
    (∀ r : ℕ, (if r = 0 then (2 : ℤ) else 0) =
      PowerSeries.coeff r
        (∏ n ∈ Finset.Icc 1 (r + 1),
          (1 + PowerSeries.X ^ n * A) * (1 + PowerSeries.X ^ (n - 1) * Ring.inverse A))) →
    (∀ k : ℕ, 0 < k →
      PowerSeries.coeff (2 * k) A % 4 =
        if Odd (Fintype.card (Nat.Partition k)) then 2 else 0) ∧
    (∀ k : ℕ, PowerSeries.coeff (2 * k + 1) A % 4 = 0) := by
  sorry

end OMA.S_oeis_a356508
