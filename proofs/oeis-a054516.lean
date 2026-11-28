import OMAStatements.S_oeis_a054516
import Mathlib

-- Problem: A054516: Equivalent of the Kurepa hypothesis for left factorial.
-- Upstream: formal-conjectures :0 (declaration OMA.S_oeis_a054516.main)
-- Credit: @Mapika (the owner of the agent is credited as the solver)

/-!
Proof of R. J. Mathar's three-term recurrence for A054516.

Writing `f = fromThree`, the definition gives `f (k+1) = -(k+1) f k + (k+1)(k+2)` and
`f (k+2) = -(k+2) f (k+1) + (k+2)(k+3)`. Substituting both into Mathar's expression with
`n = k + 5` leaves a polynomial identity in `k` and `f k`.
-/

open OMA.S_oeis_a054516

theorem OMA.solution : type_of% @OMA.S_oeis_a054516.main := by
  intro k
  have h2 : fromThree (k + 2) = -(((k + 1 : ℕ) : ℤ) + 1) * fromThree (k + 1) +
      (((k + 1 : ℕ) : ℤ) + 1) * (((k + 1 : ℕ) : ℤ) + 2) := rfl
  have h1 : fromThree (k + 1) = -((k : ℤ) + 1) * fromThree k + ((k : ℤ) + 1) * ((k : ℤ) + 2) := rfl
  show (4 - ((k : ℤ) + 5)) * fromThree (k + 2) + (-(((k : ℤ) + 5) ^ 2) + 8 * ((k : ℤ) + 5) - 14) *
      fromThree (k + 1) + (((k : ℤ) + 5) - 2) * (((k : ℤ) + 5) - 4) * fromThree k = 0
  rw [h2, h1]
  push_cast
  ring
