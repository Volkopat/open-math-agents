import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a222014

/-- Defining functional equation of OEIS A222014:
`A(x) = ∑_{k ≥ 0} k! * x^k * A(x)^(k^2) / ∏_{j=1..k} (1 + j * x * A(x)^k)`,
expressed via the sequence of formal power series summands `T k ∈ ℤ[[x]]`. -/
def IsA222014 (A : PowerSeries ℤ) : Prop :=
  ∃ T : ℕ → PowerSeries ℤ,
    (∀ k : ℕ,
      T k * (∏ j ∈ Finset.range k, (1 + ((j + 1 : ℕ) : PowerSeries ℤ) * PowerSeries.X * A ^ k)) =
        ((Nat.factorial k : ℕ) : PowerSeries ℤ) * PowerSeries.X ^ k * A ^ (k ^ 2)) ∧
    (∀ m : ℕ, PowerSeries.coeff m A = ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff m (T k))

/-- Conjecture on OEIS A222014: `a(n)` is odd if and only if `n = 2^k - 1` for some `k ≥ 0`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA222014 A →
      ∀ n : ℕ, PowerSeries.coeff n A % 2 = 1 ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  sorry

end OMA.S_oeis_a222014
