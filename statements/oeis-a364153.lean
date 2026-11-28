import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice.Nat

namespace OMA.S_oeis_a364153

/-- A sequence `s` of length `n` taking values in `{1, ..., m}` has unique segment sums if all
nonempty contiguous subsegments `∑_{k = i}^j s(k)` (`0 ≤ i ≤ j < n`) have pairwise distinct sums. -/
def HasUniqueSegmentSums (n m : ℕ) : Prop :=
  ∃ s : ℕ → ℕ, (∀ k < n, 1 ≤ s k ∧ s k ≤ m) ∧
    ∀ i₁ j₁ i₂ j₂ : ℕ, i₁ ≤ j₁ → j₁ < n → i₂ ≤ j₂ → j₂ < n →
      (∑ k ∈ Finset.Icc i₁ j₁, s k) = (∑ k ∈ Finset.Icc i₂ j₂, s k) →
      i₁ = i₂ ∧ j₁ = j₂

/-- `a(n)` (OEIS A364153): the smallest positive integer `m` such that from `{1, ..., m}` one can
choose a sequence `(s(0), ..., s(n-1))` in which every contiguous segment has a unique sum. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ HasUniqueSegmentSums n m}

/-- Conjecture (OEIS A364153, proved by Hegyvári): there exists `C` such that `a(n) < C * n` for
every sufficiently large `n`. -/
theorem main : ∃ C : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a n < C * n := by
  sorry

end OMA.S_oeis_a364153
