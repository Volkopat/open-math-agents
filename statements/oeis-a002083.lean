import Mathlib

/-!
# The normalized limit of the Narayana–Zidek–Capell numbers

Sources: https://oeis.org/A002083 and https://oeis.org/A242729
Credit: @kyka776

The auxiliary recurrence comes from the program in A242729 for the
Atkinson–Negro–Santoro constant. Its positive-index normalized values
decrease to their infimum.
-/

open Filter
open scoped Topology

namespace OMA.S_oeis_a002083

/-- The integers in A002083, with zero at the unused index zero as in the PARI program. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => 2 * a (n + 2) - (if (n + 2) % 2 = 0 then a ((n + 2) / 2) else 0)
termination_by n => n
decreasing_by all_goals omega

/-- The auxiliary integers from the program in A242729. -/
def u : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * u (n + 1) - u (n / 2)
termination_by n => n
decreasing_by all_goals omega

noncomputable def normalizedU (n : ℕ) : ℝ := (u (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)

noncomputable def atkinsonNegroSantoro : ℝ := ⨅ n, normalizedU n

theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / (2 : ℝ) ^ (n - 3))
    atTop (𝓝 (2 * atkinsonNegroSantoro)) := by
  sorry

end OMA.S_oeis_a002083

