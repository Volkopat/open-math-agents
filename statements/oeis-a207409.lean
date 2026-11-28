import Mathlib

/-!
# The largest entry in a row of the prime-remainder triangle

OEIS A207409, conjecture of Mike Jones (July 12, 2024).
The rows and columns use one-based prime indices.
https://oeis.org/A207409
-/

namespace OMA.S_oeis_a207409

/-- Entry in row n, column k, for 1 ≤ k < n. -/
noncomputable def entry (n k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1) % Nat.nth Nat.Prime (k - 1)

theorem main : ∀ n : ℕ, 2 ≤ n →
    ∃ k ∈ Finset.Ico 1 n,
      (∀ j ∈ Finset.Ico 1 n, j ≠ k → entry n j < entry n k) ∧
      (2 < n → 1 < k ∧ Odd (entry n (k - 1))) := by
  sorry

end OMA.S_oeis_a207409
