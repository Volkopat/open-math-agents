import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Finite.Basic

namespace OMA.S_mo_330781

/-- Remove repetitions of the prime factors two and three, preserving every
other factor with its multiplicity. -/
def restrictedRadical (n : ℕ) : ℕ :=
  n / (2 ^ n.factorization 2 * 3 ^ n.factorization 3) *
    (if 2 ∣ n then 2 else 1) * (if 3 ∣ n then 3 else 1)

/-- The mini-abc finiteness conjecture with only two and three reduced in the radical. -/
theorem main :
    ∀ ε : ℝ, 0 < ε →
      {t : ℕ × ℕ × ℕ |
        0 < t.1 ∧ 0 < t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧
          Nat.Coprime t.1 t.2.1 ∧
            1 + ε < Real.log (t.2.2 : ℝ) /
              Real.log (restrictedRadical (t.1 * t.2.1 * t.2.2) : ℝ)}.Finite := by
  sorry

end OMA.S_mo_330781
