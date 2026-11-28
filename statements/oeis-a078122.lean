import Mathlib

namespace OMA.S_oeis_a078122

def ltMatMul (M N : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (i + 1), M i k * N k j

def ltMatPow (M : ℕ → ℕ → ℤ) : ℕ → ℕ → ℕ → ℤ
  | 0, i, j => if i = j then 1 else 0
  | m + 1, i, j => ltMatMul (ltMatPow M m) M i j

theorem main :
    ∀ M : ℕ → ℕ → ℤ,
      (∀ i j, i < j → M i j = 0) →
      (∀ i, M i 0 = 1) →
      (∀ i j, ltMatPow M 3 i j = M (i + 1) (j + 1)) →
      ∀ n k, k < n →
        M n k = PowerSeries.coeff (3 ^ n - 3 ^ (n - k))
          (∏ j ∈ Finset.range (n - k + 1),
            PowerSeries.mk (fun r => if 3 ^ j ∣ r then (1 : ℤ) else 0)) := by
  sorry

end OMA.S_oeis_a078122
