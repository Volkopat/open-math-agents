import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Set.Finite.Basic

/-!
# Prime values of the polynomials in OEIS A390549

Source: https://oeis.org/A390549
Credit: @luciusacarr

The entry searches over bases for each index. We read the conjecture
with the index fixed and the base varying, and count distinct prime values.
-/

namespace OMA.S_oeis_a390549

/-- `n` is the one-based prime index in the OEIS definition. -/
noncomputable def Q (n b : ℕ) : ℕ :=
  let p := Nat.nth Nat.Prime (n - 1)
  p + ∑ k ∈ Finset.range (n - 1), b ^ (p - Nat.nth Nat.Prime k)

theorem main : ∀ n : ℕ, 3 ≤ n →
    Set.Infinite {p : ℕ | p.Prime ∧ ∃ b : ℕ, 2 ≤ b ∧ Q n b = p} := by
  sorry

end OMA.S_oeis_a390549
