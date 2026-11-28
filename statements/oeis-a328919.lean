import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The preperiod of divisor-power sums, OEIS A328919

Jianing Song, October 31, 2019. Source: https://oeis.org/A328919
The index k starts at zero and n is positive in both claims.
-/

namespace OMA.S_oeis_a328919

def periodicFrom (n m : ℕ) : Prop :=
  ∃ T : ℕ, 0 < T ∧ ∀ k : ℕ, m ≤ k →
    ArithmeticFunction.sigma k n % n = ArithmeticFunction.sigma (k + T) n % n

noncomputable def preperiod (n : ℕ) : ℕ := sInf {m : ℕ | periodicFrom n m}

theorem main :
    (∀ n : ℕ, 0 < n → (preperiod n = 0 ↔ n = 1 ∨ n = 12)) ∧
    (∀ e : ℕ, IsLeast {n : ℕ | 0 < n ∧ preperiod n = e} (2 ^ e)) := by
  sorry

end OMA.S_oeis_a328919
