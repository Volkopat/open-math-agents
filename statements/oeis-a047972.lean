import Mathlib

/-!
# OEIS A047972: Distance from a prime to its nearest square

Source: https://oeis.org/A047972
Credit: @gblacher2

Ya-Ping Lu's conjecture bounds the distance by the square root of the prime
and specifies the limit of their ratio.
-/

open scoped Topology

namespace OMA.S_oeis_a047972

/-- Subtract one to convert the OEIS prime index to a zero-based index. -/
noncomputable def primeAt (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- The nearest square is one of the two consecutive squares bracketing m. -/
def distanceToSquare (m : ℕ) : ℕ :=
  let r := m.sqrt
  min (m - r ^ 2) ((r + 1) ^ 2 - m)

noncomputable def a (n : ℕ) : ℕ :=
  distanceToSquare (primeAt n)

theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) < Real.sqrt (primeAt n : ℝ)) ∧
      Filter.Tendsto (fun n : ℕ => (a n : ℝ) / Real.sqrt (primeAt n : ℝ))
        Filter.atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a047972
