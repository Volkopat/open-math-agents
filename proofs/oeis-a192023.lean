import OMAStatements.S_oeis_a192023

-- Problem: A192023: The Wiener index of the comb-shaped graph |_|_|...|_| with 2n (n>=1) nodes. The Wiener index of a connected graph is the sum of the distances between all unordered pairs of vertices in the graph.
-- Upstream: formal-conjectures statements/oeis-a192023.lean:0 (declaration OMA.S_oeis_a192023.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: n = 3. The 2 X 2 matrices with entries in {1, 2, 3} and determinant 6 are
-- [[3, 1], [3, 3]] and [[3, 3], [1, 3]] (a*d <= 9 forces a = d = 3 and b*c = 3), so there are 2.
-- But A192023(1) = 1: the comb with 2 nodes is a single edge, so the ordered distance sum is
-- 0 + 1 + 1 + 0 = 2 and its half is 1.

open OMA.S_oeis_a192023 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a192023.main) := by
  intro H
  have hc : count 3 = 2 := by decide
  have hadj : (comb 1).Adj (0, 0) (0, 1) := by
    unfold comb
    rw [SimpleGraph.fromRel_adj]
    decide
  have h01 : (comb 1).dist (0, 0) (0, 1) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  have h10 : (comb 1).dist (0, 1) (0, 0) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
  have hsum : (∑ x : Fin 1 × Fin 2, ∑ y : Fin 1 × Fin 2, (comb 1).dist x y) = 0 + 1 + (1 + 0) := by
    simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two, SimpleGraph.dist_self,
      h01, h10]
  have hw2 : wiener 1 = (0 + 1 + (1 + 0)) / 2 := by
    unfold wiener
    rw [hsum]
  have hw : wiener 1 = 1 := hw2.trans (by norm_num)
  have h := H 3 (by norm_num)
  rw [hc, show (3 : ℕ) - 2 = 1 from rfl, hw] at h
  omega
