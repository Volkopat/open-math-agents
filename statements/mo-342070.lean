import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Source: https://mathoverflow.net/questions/342070 -/

open scoped BigOperators

namespace OMA.S_mo_342070

def mass (n k : ℕ) (p : ℝ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

def lowerTail (n k : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), mass n j p

def upperTail (n k : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc k n, mass n j p

theorem main :
    ∀ n k : ℕ, 0 < k → 2 * k ≤ n →
      ∀ δ : ℝ, 0 < δ → δ < (1 / 3 : ℝ) →
      ∀ pBig pSmall : ℝ, pBig ∈ Set.Icc 0 1 → pSmall ∈ Set.Icc 0 1 →
        lowerTail n k pBig = δ → upperTail n k pSmall = δ →
        mass n (k - 1) pBig ≤ mass n (k - 1) pSmall ∧
        mass n k pBig ≤ mass n k pSmall := by
  sorry

end OMA.S_mo_342070
