import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Defs

/-!
# OEIS A002596: prime-divisibility blocks in square-root numerators

Source: https://oeis.org/A002596
This states the divisibility-block conjecture in the entry, not the separate
observations about sums of the coefficients. Indices start at zero.
-/

namespace OMA.S_oeis_a002596

/-- The coefficient of degree `n` in the formal expansion of the square
root of `1 + x`, defined by the generalized binomial recurrence. -/
def coeff : ℕ → ℚ
  | 0 => 1
  | n + 1 => coeff n * (1 / 2 - (n : ℚ)) / ((n : ℚ) + 1)

/-- A maximal block of exactly `len` consecutive numerators divisible by
`p`, with the term at index `j` immediately before the block. -/
def blockAfter (p j len : ℕ) : Prop :=
  0 < len ∧
  ¬ (p : ℤ) ∣ (coeff j).num ∧
  (∀ i : ℕ, j < i → i ≤ j + len → (p : ℤ) ∣ (coeff i).num) ∧
  ¬ (p : ℤ) ∣ (coeff (j + len + 1)).num

theorem main :
    ∀ p : ℕ, p.Prime →
      (∀ n : ℕ, (p : ℤ) ∣ (coeff n).num →
        ∃ j k : ℕ, 0 < k ∧ j < n ∧ n ≤ j + (p ^ k - 3) / 2 ∧
          blockAfter p j ((p ^ k - 3) / 2)) ∧
      (∀ j k : ℕ, 0 < k → blockAfter p j ((p ^ k - 3) / 2) →
        blockAfter p (p * j - (p - 1) / 2) ((p ^ (k + 1) - 3) / 2)) := by
  sorry

end OMA.S_oeis_a002596
