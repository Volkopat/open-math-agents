import Mathlib

/-!
# Erdős Problem 796

Source: https://www.erdosproblems.com/796
Credit: @willperacchio

The strict inequality between the two factors counts each unordered pair of distinct
elements once. The function tending to zero represents the error in the coefficient
of the second term of the stated asymptotic expansion.
-/

open Filter
open scoped Topology

namespace OMA.S_erdos_796

def factorPairs (A : Finset ℕ) (m : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun p => p.1 < p.2 ∧ p.1 * p.2 = m

noncomputable def g (k n : ℕ) : ℕ :=
  sSup {a : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ A.card = a ∧
    ∀ m : ℕ, (factorPairs A m).card < k}

theorem main :
    ∃ (c : ℝ) (ε : ℕ → ℝ), Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        (g 3 n : ℝ) =
          Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) * (n : ℝ) +
            (c + ε n) * ((n : ℝ) / Real.log (n : ℝ)) := by
  sorry

end OMA.S_erdos_796
