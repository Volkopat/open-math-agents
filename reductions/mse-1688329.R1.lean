import OMAStatements.S_mse_1688329

-- Reduction mse-1688329.R1 of the Erdos-Gyarfas power-of-two cycle conjecture.
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1 is the classical dense case: under Dirac's condition 2 deg v >= n every graph with minimum
-- degree at least 3 has a 4-cycle (two non-adjacent vertices have at least two common neighbours
-- by inclusion-exclusion; a complete graph on at least 4 vertices has a 4-cycle outright).
-- H2 is the open rest: graphs with some vertex of degree below n / 2.

namespace OMA.R_mse_1688329_R1

open OMA.S_mse_1688329

/-- Dirac-dense graphs (`n ≤ 2 deg v` for every vertex) of minimum degree at least 3 contain a
cycle of length `4 = 2^2`. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, 3 ≤ G.degree v) → (∀ v, Fintype.card V ≤ 2 * G.degree v) → HasPowerOfTwoCycle G

/-- The open core: minimum degree at least 3 and some vertex of degree below `n / 2`. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, 3 ≤ G.degree v) → (∃ v, 2 * G.degree v < Fintype.card V) → HasPowerOfTwoCycle G

theorem main : H1 → H2 → type_of% @OMA.S_mse_1688329.main := by
  intro h1 h2 V _ _ _ G _ h3
  by_cases h : ∀ v, Fintype.card V ≤ 2 * G.degree v
  · exact h1 V G h3 h
  · push_neg at h
    exact h2 V G h3 h

end OMA.R_mse_1688329_R1
