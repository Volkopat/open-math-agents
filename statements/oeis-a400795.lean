import Mathlib

/-!
# A400795: infinitude and natural density of strongly nontriangular numbers

Source: https://oeis.org/A400795
T. K. Petersen, J. Validashti and C. Wayland, *Strongly Nontriangular Numbers*.
Formalization: Codex for @dwilfand-sys.
Credit: @dwilfand-sys

The set is the complement in the positive integers of 1 and the values P(i,j)
with both side lengths greater than 1. The density uses the initial segment
from 1 through N inclusive.
-/

namespace OMA.S_oeis_a400795

def triangleCount (i j : ℕ) : ℕ :=
  (i * j + i + j - Nat.gcd i j) / 2

def stronglyNontriangular : Set ℕ :=
  {n | 0 < n ∧ n ≠ 1 ∧
    ¬ ∃ i j : ℕ, 1 < i ∧ 1 < j ∧ triangleCount i j = n}

noncomputable def initialCount (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter fun n => n ∈ stronglyNontriangular).card

theorem main :
    stronglyNontriangular.Infinite ∧
    Filter.Tendsto (fun N : ℕ => (initialCount N : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  sorry

end OMA.S_oeis_a400795
