import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OMA.S_mo_186663

/-- The gap after the prime at zero-based index n. -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- Erdős's binary number that records the successive strict increases in prime gaps. -/
theorem main :
    ∃ x : ℝ, Irrational x ∧
      HasSum (fun n : ℕ =>
        if primeGap n < primeGap (n + 1) then (1 : ℝ) / 2 ^ (n + 1) else 0) x := by
  sorry

end OMA.S_mo_186663
