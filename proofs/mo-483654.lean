import OMAStatements.S_mo_483654
import Mathlib

open Finset
open scoped Matrix

private theorem amgm_three {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a*b*c=1) : 3 ≤ a+b+c := by
  have hg := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := 1/3) (w₂ := 1/3) (w₃ := 1/3)
    (by norm_num) (by norm_num) (by norm_num) ha hb hc (by norm_num)
  rw [← Real.mul_rpow ha hb, ← Real.mul_rpow (mul_nonneg ha hb) hc, h, Real.one_rpow] at hg
  linarith

private theorem sum_normalized_le {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, f i j/(∑ k, f i k)) ≤ (n : ℝ) := by
  calc
    _ ≤ ∑ _i : Fin n, (1:ℝ) := by
      apply sum_le_sum
      intro i _
      rw [← Finset.sum_div]
      by_cases h : (∑ k, f i k)=0
      · simp [h]
      · rw [div_self h]
    _ = _ := by simp

theorem OMA.solution : type_of% @OMA.S_mo_483654.main := by
  intro n A hA
  let R : Fin n → ℝ := fun i => ∑ j, A i j
  let C : Fin n → ℝ := fun j => ∑ i, A i j
  let S : ℝ := ∑ i, R i
  let B : ℝ := ∑ i, ∑ j, A i j * R i * C j
  have hr (i : Fin n) : 0 ≤ R i := sum_nonneg (fun j _ => hA i j)
  have hc (j : Fin n) : 0 ≤ C j := sum_nonneg (fun i _ => hA i j)
  have hs0 : 0 ≤ S := sum_nonneg (fun i _ => hr i)
  have hb0 : 0 ≤ B := sum_nonneg (fun i _ => sum_nonneg
    (fun j _ => mul_nonneg (mul_nonneg (hA i j) (hr i)) (hc j)))
  have hS : (1 : Fin n → ℝ) ⬝ᵥ (A *ᵥ 1) = S := by
    simp [dotProduct,Matrix.mulVec,S,R]
  have hB : (1 : Fin n → ℝ) ⬝ᵥ ((Aᵀ * A * Aᵀ) *ᵥ 1) = B := by
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
    simp only [dotProduct,Matrix.mulVec,Pi.one_apply,mul_one,Matrix.transpose_apply,B,R,C]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [hS,hB]
  by_cases hz : S=0
  · rw [hz]
    simpa using mul_nonneg (sq_nonneg (n:ℝ)) hb0
  have hs : 0 < S := lt_of_le_of_ne hs0 (Ne.symm hz)
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    exact hz (by simp [S])
  have hn : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  let L : ℝ := (n:ℝ)^2/S^2
  let V : ℝ := S/n
  have hv : 0 ≤ V := div_nonneg hs.le hn.le
  have hsumR : (∑ i, ∑ j, A i j/R i) ≤ (n:ℝ) := sum_normalized_le A
  have hsumC : (∑ i, ∑ j, A i j/C j) ≤ (n:ℝ) := by
    rw [Finset.sum_comm]
    exact sum_normalized_le (fun j i => A i j)
  have cell (i j : Fin n) :
      3*A i j ≤ L*(A i j*R i*C j) + V*(A i j/R i) + V*(A i j/C j) := by
    by_cases he : A i j=0
    · simp [he]
    have hp : 0 < A i j := lt_of_le_of_ne (hA i j) (Ne.symm he)
    have hri : 0 < R i := hp.trans_le (Finset.single_le_sum (fun k _ => hA i k) (mem_univ j))
    have hcj : 0 < C j := hp.trans_le (Finset.single_le_sum (fun k _ => hA k j) (mem_univ i))
    have hprod : (L*R i*C j)*(V/R i)*(V/C j)=1 := by
      dsimp [L,V]
      field_simp [hz,hn.ne',hri.ne',hcj.ne']
    have h := amgm_three
      (mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg (n:ℝ)) (sq_nonneg S)) hri.le) hcj.le)
      (div_nonneg hv hri.le) (div_nonneg hv hcj.le) hprod
    calc
      3*A i j = A i j*3 := mul_comm _ _
      _ ≤ A i j*(L*R i*C j+V/R i+V/C j) := mul_le_mul_of_nonneg_left h hp.le
      _ = _ := by ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin n))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) => cell i j))
  simp_rw [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  change 3*S ≤ L*B+V*(∑ i, ∑ j, A i j/R i)+V*(∑ i, ∑ j, A i j/C j) at hsum
  have hVR := mul_le_mul_of_nonneg_left hsumR hv
  have hVC := mul_le_mul_of_nonneg_left hsumC hv
  have hVn : V*(n:ℝ) = S := div_mul_cancel₀ _ hn.ne'
  have h : S ≤ L*B := by linarith
  have he : L*B = (n:ℝ)^2*B/S^2 := by dsimp [L]; ring
  rw [he] at h
  have ht := (le_div_iff₀ (sq_pos_of_ne_zero hz)).mp h
  nlinarith only [ht]