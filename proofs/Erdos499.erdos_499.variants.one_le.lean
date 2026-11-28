import FormalConjectures.ErdosProblems.«499»
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Convex.Birkhoff

open Finset

theorem OMA.solution : type_of% @Erdos499.erdos_499.variants.one_le := by
  classical
  intro n hn M hM
  obtain ⟨w, hw, h1, hd⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  have e (i j : Fin n) : M i j = ∑ σ : Equiv.Perm (Fin n), if σ i = j then w σ else 0 := by
    rw [← hd]
    simp [Matrix.sum_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, mul_ite]
  have key : ∑ σ, w σ * ∑ i, M i (σ i) = ∑ i, ∑ j, M i j ^ 2 := by
    simp_rw [sq, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    conv_rhs => enter [2, j, 2]; rw [e]
    simp_rw [mul_sum, mul_ite, mul_zero]
    rw [sum_comm]
    simp [mul_comm]
  have sq1 : 1 ≤ ∑ i, ∑ j, M i j ^ 2 := by
    have := sum_le_sum fun i (_ : i ∈ univ) =>
      sum_row_of_mem_doublyStochastic hM i ▸ sq_sum_le_card_mul_sum_sq (s := univ) (f := M i)
    simp [← mul_sum] at this
    by_contra! h
    nlinarith [(by exact_mod_cast hn : (0 : ℝ) < n)]
  obtain ⟨σ, hσ, hd1⟩ : ∃ σ, 0 < w σ ∧ 1 ≤ ∑ i, M i (σ i) := by
    by_contra! h
    obtain ⟨τ, -, hτ⟩ := exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℝ)) (g := w)
      (by simp [h1])
    have := sum_lt_sum (s := univ) (f := fun σ => w σ * ∑ i, M i (σ i)) (g := w)
      (fun σ _ => (hw σ).eq_or_lt.elim (fun h0 => by simp [← h0])
        fun hp => (mul_lt_of_lt_one_right hp (h σ hp)).le)
      ⟨τ, mem_univ _, mul_lt_of_lt_one_right hτ (h τ hτ)⟩
    linarith
  refine ⟨σ, fun i => (hσ.trans_le ?_).ne', hd1⟩
  rw [e]
  calc w σ = if σ i = σ i then w σ else 0 := by simp
    _ ≤ _ := single_le_sum (f := fun τ : Equiv.Perm (Fin n) => if τ i = σ i then w τ else 0)
      (fun τ _ => by split <;> simp [hw]) (mem_univ σ)
