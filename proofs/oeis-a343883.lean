import OMAStatements.S_oeis_a343883
import Mathlib

/-!
# OEIS A343883: disproof of the statement as formalised

The statement parses as `∀ k, ((1 ≤ k → a340179 k ∣ a023896 k) ↔ k ∈ {3, 4, 6, 8, 10, 16, 30, 54})`
because `→` binds tighter than `↔`. At `k = 0` the left side holds vacuously while
`0` is not in the finite set, so the statement is false.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a343883.main) := by
  intro h
  have h0 := (h 0).mp (fun hk => absurd hk (by decide))
  revert h0
  decide
