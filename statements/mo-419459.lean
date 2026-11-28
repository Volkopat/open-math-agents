import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic

/-! Source: https://mathoverflow.net/questions/419459 -/

namespace OMA.S_mo_419459

def exceptional (p M X : ℕ) : Finset ℕ :=
  (Finset.Ico 1 X).filter (fun n => ¬ p ∣ (n * M + n * M).choose (n * M))

def divisible (p M X : ℕ) : Finset ℕ :=
  (Finset.Ico 1 X).filter (fun n => p ∣ (n * M + n * M).choose (n * M))

/-- Bounds for the two populations below X, using any base-p length sufficient for M * X. -/
theorem main :
    ∀ p M X k : ℕ, p.Prime → 0 < M → 0 < X → M * X ≤ p ^ k →
      (exceptional p M X).card + 1 ≤ ((p + 1) / 2) ^ k ∧
        X ≤ ((p + 1) / 2) ^ k + (divisible p M X).card := by
  sorry

end OMA.S_mo_419459
