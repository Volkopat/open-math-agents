import OMAStatements.S_mo_161728
import Mathlib

-- Retains @AkiRA-COM-FP's stochastic-matrix estimate from PR #15115,
-- head 27a71bad362f5cfe30b8ef37e7c736fae4d386b9. The existing entry bound
-- now gives the norm bound directly, followed by the scalar squeeze theorem.

open Finset Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise

open OMA.S_mo_161728

private theorem stochastic_mul {d : ℕ} {A B : RealMatrix d}
    (hA : RowStochastic A) (hB : RowStochastic B) : RowStochastic (A * B) := by
  constructor
  · intro i j
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hA.1 i k) (hB.1 k j))
  · intro i
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [←Finset.mul_sum, hB.2, mul_one]
    exact hA.2 i

private theorem stochastic_pow {d : ℕ} {A : RealMatrix d} (hA : RowStochastic A) (k : ℕ) :
    RowStochastic (A^k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    refine ⟨fun i j => ?_,fun i => ?_⟩
    · simp only [Matrix.one_apply]
      split <;> norm_num
    · simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ']
    exact stochastic_mul hA ih

private theorem stochastic_entry_le_one {d : ℕ} {B : RealMatrix d} (hB : RowStochastic B) (i j : Fin d) :
    B i j ≤ 1 := by
  rw [←hB.2 i]
  exact Finset.single_le_sum (fun k _ => hB.1 i k) (Finset.mem_univ j)

private theorem bound_pow_difference {d : ℕ} {A B : RealMatrix d} (hA : RowStochastic A)
    (hB : RowStochastic B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hAB : ∀ i j, |A i j-B i j| ≤ δ) (k : ℕ) :
    ∀ i j, |(A^k-B^k) i j| ≤ (k : ℝ)*(d : ℝ)*δ := by
  induction k with
  | zero => intro i j; simp
  | succ k ih =>
    intro i j
    let F : Fin d → ℝ := fun r => A i r * (A^k-B^k) r j
    let H : Fin d → ℝ := fun r => (A i r-B i r)*(B^k) r j
    have he : (A^(k+1)-B^(k+1)) i j = (∑ r, F r) + ∑ r, H r := by
      simp only [pow_succ',Matrix.sub_apply,Matrix.mul_apply,←Finset.sum_sub_distrib,
        ←Finset.sum_add_distrib,F,H]
      apply Finset.sum_congr rfl
      intro r _
      ring
    have hFirst : ∑ r, |F r| ≤ (k : ℝ)*(d : ℝ)*δ := by
      calc
        _ ≤ ∑ r, A i r * ((k : ℝ)*(d : ℝ)*δ) := by
          apply Finset.sum_le_sum
          intro r _
          rw [abs_mul,abs_of_nonneg (hA.1 i r)]
          exact mul_le_mul_of_nonneg_left (ih r j) (hA.1 i r)
        _ = _ := by rw [←Finset.sum_mul,hA.2,one_mul]
    have hPow := stochastic_pow hB k
    have hSecond : ∑ r, |H r| ≤ (d : ℝ)*δ := by
      calc
        _ ≤ ∑ _ : Fin d, δ := by
          apply Finset.sum_le_sum
          intro r _
          rw [abs_mul,abs_of_nonneg (hPow.1 r j)]
          calc
            _ ≤ δ * 1 := mul_le_mul (hAB i r) (stochastic_entry_le_one hPow r j)
              (hPow.1 r j) hδ
            _ = _ := mul_one _
        _ = _ := by simp [nsmul_eq_mul]
    rw [he]
    calc
      _ ≤ |∑ r, F r| + |∑ r, H r| := abs_add_le _ _
      _ ≤ (∑ r, |F r|) + ∑ r, |H r| :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ (k : ℝ)*(d : ℝ)*δ + (d : ℝ)*δ := add_le_add hFirst hSecond
      _ = _ := by push_cast; ring

theorem OMA.solution : type_of% @OMA.S_mo_161728.main := by
  intro d α hα hα' M seq hM hSeq hRate
  have hNorm : ‖α‖ < 1 := by simpa [Real.norm_eq_abs,abs_of_pos hα] using hα'
  have hBasic := (hasSum_coe_mul_geometric_of_norm_lt_one hNorm).summable.tendsto_atTop_zero
  have hBound : Tendsto (fun n : ℕ => (n : ℝ)*(d : ℝ)*α^n) atTop (𝓝 0) := by
    have ht := hBasic.mul_const (d : ℝ)
    simpa [mul_right_comm] using ht
  have hRate' (n : ℕ) (i j : Fin d) : |seq n i j-M i j| ≤ α^n := by
    have h := (Matrix.norm_le_iff (pow_nonneg hα.le n)).mp (hRate n) i j
    simpa [Real.norm_eq_abs] using h
  apply squeeze_zero (fun _ => norm_nonneg _) _ hBound
  intro n
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  simpa only [Real.norm_eq_abs] using
    bound_pow_difference (hSeq n) hM (pow_nonneg hα.le n) (hRate' n) n i j
