import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-! Source: https://mathoverflow.net/questions/507228 -/

open scoped BigOperators

namespace OMA.S_mo_507228

def sumWithLcm (k n : ℕ) : Prop :=
  ∃ r : ℕ, 0 < r ∧ ∃ x : Fin k → ℕ,
    (∀ i, 0 < x i) ∧ (∑ i, x i) = n ∧ Finset.univ.lcm x = ∏ i : Fin k, (r + (i : ℕ))

def sumWithProduct (k n : ℕ) : Prop :=
  ∃ r : ℕ, 0 < r ∧ ∃ x : Fin k → ℕ,
    (∀ i, 0 < x i) ∧ (∑ i, x i) = n ∧ (∏ i, x i) = ∏ i : Fin k, (r + (i : ℕ))

theorem main : ∀ k : ℕ, 2 < k →
    (∀ n : ℕ, 2 ^ k - 2 ≤ n → sumWithLcm k n) ∧
    (∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, sumWithLcm k n ↔ N ≤ n) ∧
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, M ≤ n → sumWithProduct k n := by
  sorry

end OMA.S_mo_507228
