import Mathlib

/-!
# A000073 — A congruence for the Tribonacci numbers

Conjectured by Peter Bala in https://oeis.org/A000073.
The prime condition comes from https://oeis.org/A106282.
Credit: @Ciphore
-/

namespace OMA.S_oeis_a000073

def tribonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | m + 3 => tribonacci (m + 2) + tribonacci (m + 1) + tribonacci m

theorem main : ∀ (p n k : ℕ), p.Prime → 0 < n → 0 < k →
    (∀ x : ZMod p, x ^ 3 - x ^ 2 - x - 1 ≠ 0) → Nat.ModEq (p ^ k)
      (tribonacci (n * p ^ (k + 1)) + tribonacci (n * p ^ k) +
        tribonacci (n * p ^ (k - 1))) 0 := by
  sorry

end OMA.S_oeis_a000073
