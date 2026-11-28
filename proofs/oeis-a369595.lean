import OMAStatements.S_oeis_a369595
import Mathlib

/-!
# OEIS A369595: A(n,0) = A135920(n+1) for every n

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. Define c(0,1) = 1, c(0,j) = 0 for j > 1, c(n,0) = 0 and c(n+1,j) = j^2*c(n,j) + c(n,j-1). (1) A(n,k)
= Sum_{j>=1} c(n,j)*j^k for all k, by induction on n: the term A(n,k+2) contributes Sum j^2 c(n,j)
j^k and the binomial sum contributes Sum c(n,j)(j+1)^k = Sum c(n,j-1) j^k. (2) The series C_j(x) =
Sum_n c(n,j) x^n satisfy C_1 = 1/(1-x) and (1 - j^2 x) C_j = x C_{j-1}, so C_j = x^(j-1) /
Prod_{h=1..j} (1 - h^2 x). (3) A(n,0) = Sum_j c(n,j) is the coefficient of x^n in Sum_{j>=1}
x^(j-1)/Prod_{h=1..j}(1 - h^2 x), i.e. the coefficient of x^(n+1) in Sum_{j>=0} x^j/Prod_{h=0..j}(1
- h^2 x) (the h = 0 factor is 1 and the j = 0 term contributes nothing in degree n+1 >= 1).
-/

open OMA.S_oeis_a369595

namespace OMA.A369595Proof

def c : ℕ → ℕ → ℕ
  | 0, j => if j = 1 then 1 else 0
  | _ + 1, 0 => 0
  | n + 1, j + 1 => (j + 1) ^ 2 * c n (j + 1) + c n j

@[simp] lemma c_zero (n : ℕ) : c n 0 = 0 := by
  cases n <;> simp [c]

@[simp] lemma c_one (n : ℕ) : c n 1 = 1 := by
  induction n with
  | zero => simp [c]
  | succ n ih => simpa [c] using ih

lemma c_support (n j : ℕ) (h : n + 1 < j) : c n j = 0 := by
  induction n generalizing j with
  | zero => simp [c, show j ≠ 1 by omega]
  | succ n ih =>
    cases j with
    | zero => simp
    | succ j => simp [c, ih (j + 1) (by omega), ih j (by omega)]

lemma binomial_moment (k j : ℕ) :
    ∑ h ∈ Finset.range (k + 1), k.choose h * j ^ h = (j + 1) ^ k := by
  simpa [mul_comm] using (add_pow j 1 k).symm

lemma moment_step (n k : ℕ) :
    ∑ j ∈ Finset.range (n + 1 + 2), c (n + 1) j * j ^ k =
      (∑ j ∈ Finset.range (n + 2), j ^ 2 * c n j * j ^ k) +
      ∑ j ∈ Finset.range (n + 2), c n j * (j + 1) ^ k := by
  have shift :
      ∑ j ∈ Finset.range (n + 2), (j + 1) ^ 2 * c n (j + 1) * (j + 1) ^ k =
      ∑ j ∈ Finset.range (n + 2), j ^ 2 * c n j * j ^ k := by
    have hs := Finset.sum_range_succ' (fun j => j ^ 2 * c n j * j ^ k) (n + 2)
    rw [Finset.sum_range_succ] at hs
    simpa [c_support n (n + 2) (by omega)] using hs.symm
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, Finset.sum_range_succ']
  simp only [c, zero_mul, add_zero, add_mul, Finset.sum_add_distrib]
  rw [shift]

lemma array_moment (n k : ℕ) :
    A n k = ∑ j ∈ Finset.range (n + 2), c n j * j ^ k := by
  induction n generalizing k with
  | zero => simp [A, c]
  | succ n ih =>
    have hb :
        (∑ h ∈ Finset.range (k + 1), k.choose h *
          ∑ j ∈ Finset.range (n + 2), c n j * j ^ h) =
        ∑ j ∈ Finset.range (n + 2), c n j * (j + 1) ^ k := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← binomial_moment, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    simp only [A, ih]
    rw [moment_step, hb]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_add]
    ring

open PowerSeries

def Cs (j : ℕ) : PowerSeries ℚ := PowerSeries.mk (fun n => (c n j : ℚ))

lemma series_one : (1 - X : PowerSeries ℚ) * Cs 1 = 1 := by
  ext n
  cases n with
  | zero => simp [sub_mul, Cs, coeff_zero_eq_constantCoeff]
  | succ n => simp [sub_mul, Cs, coeff_one]

lemma series_step (j : ℕ) (hj : 1 ≤ j) :
    (1 - C (((j + 1 : ℕ) : ℚ) ^ 2) * X) * Cs (j + 1) = X * Cs j := by
  ext n
  cases n with
  | zero =>
    simp [sub_mul, Cs, coeff_zero_eq_constantCoeff, c, show j ≠ 0 by omega]
  | succ n =>
    simp only [sub_mul, one_mul, map_sub, mul_assoc,
      coeff_C_mul, coeff_succ_X_mul, Cs, coeff_mk, c,
      Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]
    ring

lemma series_product (j : ℕ) :
    Cs (j + 1) = (X : PowerSeries ℚ) ^ j *
      ∏ k ∈ Finset.range (j + 2), (1 - C ((k : ℚ) ^ 2) * X)⁻¹ := by
  induction j with
  | zero =>
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
      Nat.cast_one, zero_pow (by decide : 2 ≠ 0), one_pow, map_zero, map_one,
      zero_mul, sub_zero, inv_one, one_mul, pow_zero]
    rw [← one_mul ((1 - X : PowerSeries ℚ)⁻¹)]
    apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp)).2
    simpa [mul_comm] using series_one
  | succ j ih =>
    have hs : Cs (j + 1 + 1) = (X * Cs (j + 1)) *
        (1 - C (((j + 2 : ℕ) : ℚ) ^ 2) * X)⁻¹ := by
      apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp)).2
      simpa only [mul_comm, Nat.add_assoc] using series_step (j + 1) (by omega)
    rw [hs, ih, Finset.prod_range_succ
      (fun k => (1 - C ((k : ℚ) ^ 2) * X : PowerSeries ℚ)⁻¹) (j + 2), pow_succ]
    ring

lemma summand_coeff (n j : ℕ) :
    coeff (n + 1) ((X : PowerSeries ℚ) ^ j *
      ∏ k ∈ Finset.range (j + 1), (1 - C ((k : ℚ) ^ 2) * X)⁻¹) = (c n j : ℚ) := by
  cases j with
  | zero => simp [coeff_one]
  | succ j =>
    have hs : (X : PowerSeries ℚ) ^ (j + 1) *
        (∏ k ∈ Finset.range (j + 1 + 1), (1 - C ((k : ℚ) ^ 2) * X)⁻¹) =
        X * Cs (j + 1) := by
      rw [series_product, pow_succ]
      ring
    rw [hs, coeff_succ_X_mul]
    simp [Cs]

end OMA.A369595Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a369595.main := by
  intro n
  rw [OMA.A369595Proof.array_moment]
  simp only [pow_zero, mul_one, Nat.cast_sum]
  unfold A135920
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (OMA.A369595Proof.summand_coeff n j).symm

