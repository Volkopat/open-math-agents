import OMAStatements.S_mo_295663
import Mathlib

-- Problem mo-295663: integer vectors C and R of length n are the column sums and the row sums of some integer
-- n x n matrix if and only if the entries of C and of R have the same total.
-- Upstream: statements/mo-295663.lean (declaration OMA.S_mo_295663.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: if M has column sums C and row sums R, both totals equal the sum of all entries of M. Conversely, for
-- n = 0 the empty matrix works. For n = k + 1 put C_j in row 0 for j >= 1, put R_i in column 0 for i >= 1,
-- put R_0 - (C_1 + ... + C_k) in the corner, and 0 elsewhere. All row sums and the column sums for j >= 1 are
-- right by construction, and column 0 sums to R_0 - (C_1 + ... + C_k) + (R_1 + ... + R_k) = C_0 because the
-- totals agree.

open OMA.S_mo_295663

theorem OMA.solution : type_of% @OMA.S_mo_295663.main := by
  intro n C R
  unfold Representable
  constructor
  · rintro ⟨M, hC, hR⟩
    calc ∑ i, C i = ∑ j, ∑ i, M i j := by
          apply Finset.sum_congr rfl
          intro j _
          exact (hC j).symm
      _ = ∑ i, ∑ j, M i j := Finset.sum_comm
      _ = ∑ i, R i := by
          apply Finset.sum_congr rfl
          intro i _
          exact hR i
  · intro hsum
    cases n with
    | zero => exact ⟨0, fun j => Fin.elim0 j, fun i => Fin.elim0 i⟩
    | succ k =>
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hsum
      refine ⟨Matrix.of fun i j =>
        Fin.cases (Fin.cases (R 0 - ∑ j' : Fin k, C j'.succ) (fun j' => C j'.succ) j)
          (fun i' => Fin.cases (R i'.succ) (fun _ => 0) j) i, ?_, ?_⟩
      · intro j
        rw [Fin.sum_univ_succ]
        refine Fin.cases ?_ (fun j' => ?_) j
        · simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
          linarith
        · simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
          simp
      · intro i
        rw [Fin.sum_univ_succ]
        refine Fin.cases ?_ (fun i' => ?_) i
        · simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
          ring
        · simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
          simp
