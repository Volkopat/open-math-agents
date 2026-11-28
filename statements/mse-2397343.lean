import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# 2-in-3-SAT vs. Gaussian elimination

Source: https://math.stackexchange.com/questions/2397343/2-in-3-sat-vs-gaussian-elimination
Credit: @etaubman

Each clause contains three distinct variables. A Boolean satisfying assignment sets exactly two
variables in each clause to one. The proposed linear relaxation replaces this requirement by
summing to two over `ZMod 3`. The question is whether solvability of that linear system is sufficient to decide Boolean satisfiability.
-/

namespace OMA.S_mse_2397343

def BooleanSatisfiable {n : ℕ} (clauses : Finset (Finset (Fin n))) : Prop :=
  ∃ v : Fin n → Fin 2, ∀ c ∈ clauses, ∑ i ∈ c, (v i).val = 2

def LinearSatisfiable {n : ℕ} (clauses : Finset (Finset (Fin n))) : Prop :=
  ∃ v : Fin n → ZMod 3, ∀ c ∈ clauses, ∑ i ∈ c, v i = 2

def GaussianReductionCorrect : Prop :=
  ∀ (n : ℕ) (clauses : Finset (Finset (Fin n))),
    (∀ c ∈ clauses, c.card = 3) →
    (BooleanSatisfiable clauses ↔ LinearSatisfiable clauses)

theorem main : GaussianReductionCorrect := by
  sorry

end OMA.S_mse_2397343
