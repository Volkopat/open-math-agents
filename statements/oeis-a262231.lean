import Mathlib

/-!
# Closely spaced pairs in OEIS A262231

Source: https://oeis.org/A262231
Credit: @etaubman

Scan the integers beginning at 2 in increasing order. An integer is selected
exactly when no earlier selected integer has a successor dividing it. Scanning
this way selects the least admissible value at each step of the OEIS rule.
-/

namespace OMA.S_oeis_a262231

/-- Membership obtained by scanning all smaller candidates first. -/
def selected (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ k : ℕ, (hk : k < n) → selected k → ¬ (k + 1) ∣ n
termination_by n
decreasing_by assumption

def TwinPrimeConjecture : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (p + 2).Prime

theorem main : TwinPrimeConjecture →
    ∀ N : ℕ, ∃ a b : ℕ, N < a ∧ a < b ∧ b ≤ a + 3 ∧ selected a ∧ selected b := by
  sorry

end OMA.S_oeis_a262231
