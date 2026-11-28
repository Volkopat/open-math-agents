import OMAStatements.S_mo_451340
import Mathlib
open OMA.S_mo_451340

open Polynomial Finset

/-- The `n`-th forward difference of `x ↦ x^(n+1)` on `ℤ`. -/
def gd (n : ℕ) : ℤ → ℤ := (fwdDiff (1 : ℤ))^[n] (fun x : ℤ => x ^ (n + 1))

lemma gd_step (n : ℕ) (x : ℤ) : gd n (x + 1) = gd n x + (n + 1).factorial := by
  have h := congrFun (fwdDiff_iter_eq_factorial (R := ℤ) (n := n + 1)) x
  rw [Function.iterate_succ_apply'] at h
  simp only [fwdDiff, Pi.natCast_apply] at h
  unfold gd
  linarith

lemma gd_lin (n : ℕ) (x : ℤ) : gd n x = gd n 0 + (n + 1).factorial * x := by
  induction x using Int.induction_on with
  | zero => simp
  | succ i ih => rw [gd_step, ih]; ring
  | pred i ih =>
    have := gd_step n (-(i : ℤ) - 1)
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring, ih] at this
    linarith

lemma gd_sum (n : ℕ) (x : ℤ) :
    gd n x = ∑ j ∈ range (n + 1), ((-1 : ℤ) ^ (n - j) * n.choose j) * (x + j) ^ (n + 1) := by
  unfold gd
  rw [fwdDiff_iter_eq_sum_shift]
  apply sum_congr rfl
  intro j _
  simp [smul_eq_mul]

theorem OMA.solution : type_of% @OMA.S_mo_451340.main := by
  intro k hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  refine ⟨n + 1, fun j => (-1 : ℤ) ^ (n - (j : ℕ)) * n.choose j, fun j => (j : ℕ),
    (n + 1).factorial, gd n 0, by positivity, ?_⟩
  apply Polynomial.funext
  intro x
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_add, eval_X]
  rw [Fin.sum_univ_eq_sum_range (fun j => ((-1 : ℤ) ^ (n - j) * n.choose j) * (x + (j : ℤ)) ^ (n + 1))
    (n + 1)]
  rw [← gd_sum, gd_lin]
  ring
