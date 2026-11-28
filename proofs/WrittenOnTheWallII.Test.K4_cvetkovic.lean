import FormalConjectures.WrittenOnTheWallII.Test

-- Problem: Testing Graph Invariants — K4 cvetkovic
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/Test.lean:284 (declaration WrittenOnTheWallII.Test.K4_cvetkovic)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial

theorem OMA.K4_charpoly :
    ((SimpleGraph.completeGraph (Fin 4)).adjMatrix ℝ).charpoly = (X - C 3) * (X - C (-1)) ^ 3 := by
  have h : ((SimpleGraph.completeGraph (Fin 4)).adjMatrix ℝ).charmatrix =
      !![X, -1, -1, -1; -1, X, -1, -1; -1, -1, X, -1; -1, -1, -1, X] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  unfold Matrix.charpoly
  rw [h, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  rw [show (C (3 : ℝ)) = (3 : ℝ[X]) from map_ofNat C 3]
  ring

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.K4_cvetkovic := by
  unfold SimpleGraph.cvetkovic
  rw [OMA.K4_charpoly, roots_mul ((monic_X_sub_C _).mul ((monic_X_sub_C _).pow 3)).ne_zero,
    roots_pow, roots_X_sub_C, roots_X_sub_C]
  norm_num [Multiset.countP_eq_card_filter, Multiset.filter_nsmul, Multiset.filter_singleton]
