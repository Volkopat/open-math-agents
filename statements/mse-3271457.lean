import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Source: https://math.stackexchange.com/questions/3271457 -/

open scoped BigOperators

namespace OMA.S_mse_3271457

/-- The sum of self-powers of the first n primes. -/
noncomputable def primePowerSum (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, let p := Nat.nth Nat.Prime i; p ^ p

/-- The alternating sum, with a negative first term. -/
noncomputable def alternatingPrimePowerSum (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n,
    (-1 : ℤ) ^ (i + 1) * (Nat.nth Nat.Prime i : ℤ) ^ (Nat.nth Nat.Prime i)

theorem main :
    (∀ n : ℕ, 0 < n → ((primePowerSum n).Prime ↔ n = 2 ∨ n = 4 ∨ n = 24)) ∧
      (∀ n : ℕ, 0 < n →
        ((alternatingPrimePowerSum n).toNat.Prime ↔ n = 2 ∨ n = 4)) := by
  sorry

end OMA.S_mse_3271457
