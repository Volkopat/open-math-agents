import Mathlib

/-!
# The prime quotients in OEIS A090528

Source: https://oeis.org/A090528 and https://oeis.org/A090527
Credit: @laurilehtinen

A090528 records the quotient at the least prime witness for A090527. Its
first term uses the input n = 2, as in the source's generating program.
-/

namespace OMA.S_oeis_a090528

noncomputable def leastWitness (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ p : ℕ, p.Prime ∧ (n^n / p).Prime then Nat.find h else 0

noncomputable def a (i : ℕ) : ℕ := (i+1)^(i+1) / leastWitness (i+1)

theorem main : ∀ i : ℕ, 1 ≤ i → a i ≠ 0 := by
  sorry

end OMA.S_oeis_a090528
