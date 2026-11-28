import OMAStatements.S_mo_265886
import Mathlib

/-!
# MathOverflow 265886: disproof

The bound `T` is allowed to be negative, which makes the lower bounds on `c, d`
vacuous while `T ^ 2` stays positive. Take `m = 2`, `T = -1`, `c = d = (1, 1)`,
`e = (2, 3)`, `f = (3, 2)` and `v = (1, 0, -1)`. The rows of the first matrix are
`(1, -1, 0), (0, 1, -1)` and of the second `(2, -3, 0), (0, 3, -2)`; `v` is the sum of
the first pair and half the sum of the second pair, yet no `|v i|` exceeds `T ^ 2 = 1`.
-/

namespace OMA.MO265886

open OMA.S_mo_265886

lemma indep (c d : Fin 2 → ℤ) (hc : c 0 ≠ 0) (hd : d 1 ≠ 0) :
    LinearIndependent ℝ (bidiagonalRows c d) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg 0
  have h2 := congrFun hg 2
  simp [bidiagonalRows, Fin.sum_univ_two] at h0 h2
  intro i
  fin_cases i
  · exact h0.resolve_right hc
  · exact h2.resolve_right hd

end OMA.MO265886

open OMA.S_mo_265886 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_265886.main) := by
  intro h
  have key := h 2 (-1) ![1, 1] ![1, 1] ![2, 3] ![3, 2]
    (OMA.MO265886.indep _ _ (by decide) (by decide))
    (OMA.MO265886.indep _ _ (by decide) (by decide))
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> decide)
    (by decide)
    ![1, 0, -1]
    (by intro hv; have := congrFun hv 0; simp at this)
    (by
      have e : (fun i => ((![1, 0, -1] : Fin 3 → ℤ) i : ℝ))
          = bidiagonalRows ![1, 1] ![1, 1] 0 + bidiagonalRows ![1, 1] ![1, 1] 1 := by
        funext i
        fin_cases i <;> simp [bidiagonalRows]
      rw [e]
      exact add_mem (Submodule.subset_span ⟨0, rfl⟩) (Submodule.subset_span ⟨1, rfl⟩))
    (by
      have e : (fun i => ((![1, 0, -1] : Fin 3 → ℤ) i : ℝ))
          = (1 / 2 : ℝ) • bidiagonalRows ![2, 3] ![3, 2] 0
            + (1 / 2 : ℝ) • bidiagonalRows ![2, 3] ![3, 2] 1 := by
        funext i
        fin_cases i <;> simp [bidiagonalRows]
      rw [e]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
  obtain ⟨i, hi⟩ := key
  fin_cases i <;> norm_num at hi
