import OMAStatements.S_oeis_a136576
import Mathlib

/-!
# Proof of Shifted Hankel Determinants of OEIS A136576

We prove that the shifted Hankel determinants of OEIS A136576 satisfy
`hankel n = closedForm n` for every `n : ℕ`.

The proof proceeds in five steps:
1. Encode `moment` as the formal power series `B` and establish the quadratic
   functional equation `(1 + 2 * X) * B - 1 = 2 * X ^ 2 * B ^ 2`.
2. Define unit lower-triangular orthogonal polynomials `P k j` via the three-term
   recurrence `P (k + 2) j = 2 * P (k + 1) j + P (k + 1) (j - 1) - 2 * P k j`.
3. Show that the shifted moment transforms `W k` satisfy `W k = (2 * X) ^ k * B ^ (k + 1)`,
   yielding exact evaluations of `w k m` for `m ≤ k + 1`.
4. Deduce the congruence `L n * H n * (L n)ᵀ = T n` with `L n` unit lower triangular
   and `T n` symmetric tridiagonal, hence `hankel n = (T n).det`.
5. Expand `(T (n + 2)).det` along the last row and column to obtain the recurrence
   `(T (n + 2)).det = 2 ^ (n + 2) * (T (n + 1)).det - 4 ^ (n + 1) * (T n).det`,
   and match it against `closedForm`.
-/

namespace OMA.A136576Proof

open OMA.S_oeis_a136576
open PowerSeries
open scoped Matrix

private lemma moment_zero : moment 0 = 1 := by
  simp [moment]

private lemma moment_one : moment 1 = -2 := by
  simp [moment]

private lemma moment_add_two (t : ℕ) :
    moment (t + 2) = -2 * moment (t + 1) +
      2 * ∑ i : Fin (t + 1), moment i.val * moment (t - i.val) := by
  rw [moment]

private noncomputable def B : PowerSeries ℚ :=
  PowerSeries.mk moment

private lemma coeff_B (n : ℕ) : PowerSeries.coeff n B = moment n := by
  simp [B]

private lemma coeff_B_sq (t : ℕ) :
    PowerSeries.coeff t (B ^ 2) =
      ∑ i : Fin (t + 1), moment i.val * moment (t - i.val) := by
  rw [sq, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b =>
    PowerSeries.coeff a B * PowerSeries.coeff b B)]
  rw [← Fin.sum_univ_eq_sum_range]
  simp [coeff_B]

private lemma coeff_X_mul_eq (n : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff (n + 1) (X * f) = PowerSeries.coeff n f := by
  simp [PowerSeries.coeff_succ_X_mul]

private lemma coeff_X_mul_zero (f : PowerSeries ℚ) :
    PowerSeries.coeff 0 (X * f) = 0 := by
  simp

private lemma cancel_X {f g : PowerSeries ℚ} (h : X * f = X * g) : f = g := by
  ext n
  have hn := congrArg (PowerSeries.coeff (n + 1)) h
  simpa [coeff_X_mul_eq] using hn

private lemma C_two : (C (2 : ℚ) : PowerSeries ℚ) = 2 := by
  rw [show (2 : ℚ) = 1 + 1 by norm_num, map_add, map_one]
  ring

private lemma C_two_pow (k : ℕ) : (C ((2 : ℚ) ^ k) : PowerSeries ℚ) = (2 : PowerSeries ℚ) ^ k := by
  rw [map_pow, C_two]

private lemma constantCoeff_B : PowerSeries.constantCoeff B = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_B, moment_zero]

private lemma B_eq : (1 + 2 * X) * B - 1 = 2 * X ^ 2 * B ^ 2 := by
  have hL : (1 + 2 * X) * B - 1 = B + C 2 * (X * B) - 1 := by
    rw [C_two]
    ring
  have hR : 2 * X ^ 2 * B ^ 2 = C 2 * (X * (X * B ^ 2)) := by
    rw [C_two]
    ring
  ext t
  rcases t with _ | _ | t
  · simp [constantCoeff_B, add_mul, sq, mul_assoc]
  · rw [hL, hR, map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
      coeff_X_mul_eq, coeff_X_mul_eq, coeff_X_mul_zero, coeff_B, coeff_B, PowerSeries.coeff_one]
    simp [moment_zero, moment_one]
  · have h1 : PowerSeries.coeff (t + 2) ((1 + 2 * X) * B - 1) =
        moment (t + 2) + 2 * moment (t + 1) := by
      rw [hL, map_sub, map_add, PowerSeries.coeff_C_mul, coeff_X_mul_eq,
        PowerSeries.coeff_one, coeff_B, coeff_B]
      simp
    have h2 : PowerSeries.coeff (t + 2) (2 * X ^ 2 * B ^ 2) =
        2 * ∑ i : Fin (t + 1), moment i.val * moment (t - i.val) := by
      rw [hR, PowerSeries.coeff_C_mul, coeff_X_mul_eq, coeff_X_mul_eq, coeff_B_sq]
    rw [h1, h2, moment_add_two]
    ring

private def P : ℕ → ℕ → ℚ
  | 0, j => if j = 0 then 1 else 0
  | 1, j => if j = 0 then 2 else if j = 1 then 1 else 0
  | k + 2, j => 2 * P (k + 1) j + (if j = 0 then 0 else P (k + 1) (j - 1)) - 2 * P k j

private lemma P_zero_of_gt : ∀ k j : ℕ, k < j → P k j = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro j hj
    rcases k with _ | _ | k
    · simp [P, show j ≠ 0 by omega]
    · simp [P, show j ≠ 0 by omega, show j ≠ 1 by omega]
    · simp only [P]
      have h1 : P (k + 1) j = 0 := ih (k + 1) (by omega) j (by omega)
      have h2 : P (k + 1) (j - 1) = 0 := ih (k + 1) (by omega) (j - 1) (by omega)
      have h3 : P k j = 0 := ih k (by omega) j (by omega)
      have hj0 : j ≠ 0 := by omega
      simp [h1, h2, h3, hj0]

private lemma P_diag : ∀ k : ℕ, P k k = 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | k
    · simp [P]
    · simp [P]
    · simp only [P]
      have h1 : P (k + 1) (k + 2) = 0 := P_zero_of_gt (k + 1) (k + 2) (by omega)
      have h2 : P (k + 1) (k + 1) = 1 := ih (k + 1) (by omega)
      have h3 : P k (k + 2) = 0 := P_zero_of_gt k (k + 2) (by omega)
      simp [h1, h2, h3]

private lemma P_subdiag : ∀ k : ℕ, P (k + 1) k = 2 * ((k : ℚ) + 1) := by
  intro k
  induction k with
  | zero => simp [P]
  | succ k ih =>
    simp only [P]
    have h1 : P (k + 1) (k + 1) = 1 := P_diag (k + 1)
    have h3 : P k (k + 1) = 0 := P_zero_of_gt k (k + 1) (by omega)
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, h1, h3, ih]
    push_cast
    ring

private def w (k m : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (k + 1), P k j * moment (j + m)

private lemma w_eq_sum_range (k m N : ℕ) (hN : k ≤ N) :
    w k m = ∑ j ∈ Finset.range (N + 1), P k j * moment (j + m) := by
  unfold w
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j _ hj
  have hlt : k < j := by
    simp only [Finset.mem_range] at hj
    omega
  simp [P_zero_of_gt k j hlt]

private lemma w_zero (m : ℕ) : w 0 m = moment m := by
  simp [w, P]

private lemma w_one (m : ℕ) : w 1 m = 2 * moment m + moment (m + 1) := by
  simp [w, Finset.sum_range_succ, P, add_comm]

private lemma w_add_two (k m : ℕ) :
    w (k + 2) m = 2 * w (k + 1) m + w (k + 1) (m + 1) - 2 * w k m := by
  have hsum :
      w (k + 2) m =
        (∑ j ∈ Finset.range (k + 3), 2 * (P (k + 1) j * moment (j + m))) +
        (∑ j ∈ Finset.range (k + 3),
          (if j = 0 then 0 else P (k + 1) (j - 1)) * moment (j + m)) -
        (∑ j ∈ Finset.range (k + 3), 2 * (P k j * moment (j + m))) := by
    unfold w
    simp only [P, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_assoc]
  have hA :
      (∑ j ∈ Finset.range (k + 3), 2 * (P (k + 1) j * moment (j + m))) = 2 * w (k + 1) m := by
    rw [← Finset.mul_sum, ← w_eq_sum_range (k + 1) m (k + 2) (by omega)]
  have hC :
      (∑ j ∈ Finset.range (k + 3), 2 * (P k j * moment (j + m))) = 2 * w k m := by
    rw [← Finset.mul_sum, ← w_eq_sum_range k m (k + 2) (by omega)]
  have hB :
      (∑ j ∈ Finset.range (k + 3),
        (if j = 0 then 0 else P (k + 1) (j - 1)) * moment (j + m)) = w (k + 1) (m + 1) := by
    rw [Finset.sum_range_succ']
    simp only [↓reduceIte, zero_mul, add_zero, Nat.succ_ne_zero, Nat.add_sub_cancel]
    unfold w
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    omega
  rw [hsum, hA, hB, hC]

private noncomputable def W (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (w k)

private lemma coeff_W (k m : ℕ) : PowerSeries.coeff m (W k) = w k m := by
  simp [W]

private lemma W_eq : ∀ k : ℕ, W k = (2 * X) ^ k * B ^ (k + 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | k
    · ext m
      simp [coeff_W, coeff_B, w_zero]
    · apply cancel_X
      have hXW1 : X * W 1 = (1 + 2 * X) * B - 1 := by
        ext m
        rcases m with _ | m
        · simp [constantCoeff_B, add_mul, mul_assoc]
        · have hmul : (1 + 2 * X) * B - 1 = B + C 2 * (X * B) - 1 := by
            rw [C_two]
            ring
          rw [coeff_X_mul_eq, coeff_W, w_one, hmul, map_sub, map_add,
            PowerSeries.coeff_C_mul, coeff_X_mul_eq, coeff_B, coeff_B, PowerSeries.coeff_one]
          simp [add_comm]
      rw [hXW1, B_eq]
      ring
    · have ih0 : W k = (2 * X) ^ k * B ^ (k + 1) := ih k (by omega)
      have ih1 : W (k + 1) = (2 * X) ^ (k + 1) * B ^ (k + 2) := ih (k + 1) (by omega)
      have hw0 : w (k + 1) 0 = 0 := by
        rw [← coeff_W, ih1]
        have hfac : (2 * X) ^ (k + 1) * B ^ (k + 2) =
            X * (2 * (2 * X) ^ k * B ^ (k + 2)) := by ring
        rw [hfac, coeff_X_mul_zero]
      have hrec : X * W (k + 2) = (1 + 2 * X) * W (k + 1) - 2 * X * W k := by
        have hmul : (1 + 2 * X) * W (k + 1) - 2 * X * W k =
            W (k + 1) + C 2 * (X * W (k + 1)) - C 2 * (X * W k) := by
          rw [C_two]
          ring
        ext m
        rcases m with _ | m
        · rw [coeff_X_mul_zero, hmul, map_sub, map_add,
            PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
            coeff_X_mul_zero, coeff_X_mul_zero, coeff_W, hw0]
          ring
        · rw [coeff_X_mul_eq, coeff_W, w_add_two, hmul, map_sub, map_add,
            PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
            coeff_X_mul_eq, coeff_X_mul_eq, coeff_W, coeff_W, coeff_W]
          ring
      apply cancel_X
      calc
        X * W (k + 2)
            = (1 + 2 * X) * ((2 * X) ^ (k + 1) * B ^ (k + 2)) -
                2 * X * ((2 * X) ^ k * B ^ (k + 1)) := by rw [hrec, ih0, ih1]
        _ = (2 * X) ^ (k + 1) * B ^ (k + 1) * ((1 + 2 * X) * B - 1) := by ring
        _ = (2 * X) ^ (k + 1) * B ^ (k + 1) * (2 * X ^ 2 * B ^ 2) := by rw [B_eq]
        _ = X * ((2 * X) ^ (k + 2) * B ^ (k + 3)) := by ring

private lemma coeff_X_pow_mul_lt (k m : ℕ) (h : m < k) (f : PowerSeries ℚ) :
    PowerSeries.coeff m (X ^ k * f) = 0 := by
  induction k generalizing m with
  | zero => omega
  | succ k ih =>
    rcases m with _ | m
    · rw [pow_succ', mul_assoc, coeff_X_mul_zero]
    · rw [pow_succ', mul_assoc, coeff_X_mul_eq]
      exact ih m (by omega)

private lemma coeff_X_pow_mul_add (k d : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff (k + d) (X ^ k * f) = PowerSeries.coeff d f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + d = (k + d) + 1 by omega, pow_succ', mul_assoc, coeff_X_mul_eq, ih]

private lemma coeff_zero_B_pow (n : ℕ) : PowerSeries.coeff 0 (B ^ n) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_B, one_pow]

private lemma coeff_one_B_pow (n : ℕ) : PowerSeries.coeff 1 (B ^ n) = -2 * (n : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a (B ^ n) * PowerSeries.coeff b B)]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      Nat.sub_zero, Nat.sub_self, coeff_zero_B_pow, coeff_B, moment_zero, moment_one, ih]
    push_cast
    ring

private lemma w_eq_zero_of_lt (k m : ℕ) (h : m < k) : w k m = 0 := by
  rw [← coeff_W, W_eq]
  have hfac : (2 * X) ^ k * B ^ (k + 1) = C ((2 : ℚ) ^ k) * (X ^ k * B ^ (k + 1)) := by
    rw [mul_pow, C_two_pow]
    ring
  rw [hfac, PowerSeries.coeff_C_mul, coeff_X_pow_mul_lt k m h, mul_zero]

private lemma w_diag (k : ℕ) : w k k = (2 : ℚ) ^ k := by
  rw [← coeff_W, W_eq]
  have hfac : (2 * X) ^ k * B ^ (k + 1) = C ((2 : ℚ) ^ k) * (X ^ k * B ^ (k + 1)) := by
    rw [mul_pow, C_two_pow]
    ring
  have hk := coeff_X_pow_mul_add k 0 (B ^ (k + 1))
  simp only [add_zero] at hk
  rw [hfac, PowerSeries.coeff_C_mul, hk, coeff_zero_B_pow, mul_one]

private lemma w_succ (k : ℕ) : w k (k + 1) = -2 * ((k : ℚ) + 1) * (2 : ℚ) ^ k := by
  rw [← coeff_W, W_eq]
  have hfac : (2 * X) ^ k * B ^ (k + 1) = C ((2 : ℚ) ^ k) * (X ^ k * B ^ (k + 1)) := by
    rw [mul_pow, C_two_pow]
    ring
  rw [hfac, PowerSeries.coeff_C_mul, coeff_X_pow_mul_add k 1, coeff_one_B_pow]
  push_cast
  ring

private def H (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  Matrix.of fun i j => -(moment (i.val + j.val + 1)) / 2

private def L (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  Matrix.of fun i j => P i.val j.val

private def T (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  Matrix.of fun i j =>
    if i = j then (2 : ℚ) ^ i.val
    else if i.val + 1 = j.val then -((2 : ℚ) ^ i.val)
    else if j.val + 1 = i.val then -((2 : ℚ) ^ j.val)
    else 0

private lemma L_det (n : ℕ) : (L n).det = 1 := by
  have htri : (L n).BlockTriangular OrderDual.toDual := by
    intro i j hij
    change P i.val j.val = 0
    exact P_zero_of_gt i.val j.val hij
  rw [Matrix.det_of_isLowerTriangular (L n) htri]
  apply Finset.prod_eq_one
  intro i _
  exact P_diag i.val

private lemma H_transpose (n : ℕ) : (H n)ᵀ = H n := by
  ext i j
  simp [H, add_comm]

private lemma T_transpose (n : ℕ) : (T n)ᵀ = T n := by
  ext i j
  simp only [Matrix.transpose_apply, T, Matrix.of_apply]
  by_cases h1 : j = i
  · subst h1; simp
  · have h1' : i ≠ j := Ne.symm h1
    simp only [h1, h1', ↓reduceIte]
    by_cases h2 : j.val + 1 = i.val
    · have h3 : i.val + 1 ≠ j.val := by omega
      simp [h2, h3]
    · by_cases h3 : i.val + 1 = j.val
      · simp [h2, h3]
      · simp [h2, h3]

private lemma LHL_entry_of_le (n : ℕ) (i j : Fin (n + 1)) (hji : j.val ≤ i.val) :
    (L n * H n * (L n)ᵀ) i j = T n i j := by
  have h1 : (L n * H n * (L n)ᵀ) i j =
      -(1 / 2 : ℚ) * ∑ b ∈ Finset.range (j.val + 1), P j.val b * w i.val (b + 1) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, L, H, Matrix.of_apply]
    have hinner : ∀ b : Fin (n + 1),
        (∑ a : Fin (n + 1), P i.val a.val * (-(moment (a.val + b.val + 1)) / 2)) * P j.val b.val =
          -(1 / 2 : ℚ) * (P j.val b.val * w i.val (b.val + 1)) := by
      intro b
      have hw : w i.val (b.val + 1) =
          ∑ a : Fin (n + 1), P i.val a.val * moment (a.val + (b.val + 1)) := by
        rw [w_eq_sum_range i.val (b.val + 1) n (by omega), ← Fin.sum_univ_eq_sum_range]
      rw [hw, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [show a.val + b.val + 1 = a.val + (b.val + 1) by omega]
      ring
    simp_rw [hinner, ← Finset.mul_sum]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun b => P j.val b * w i.val (b + 1))]
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro b _ hb
    have hlt : j.val < b := by
      simp only [Finset.mem_range] at hb
      omega
    simp [P_zero_of_gt j.val b hlt]
  rw [h1]
  by_cases hij : i = j
  · subst hij
    simp only [T, Matrix.of_apply, ↓reduceIte]
    rcases hi : i.val with _ | m
    · simp [P, w_succ]
    · rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hzero : ∑ b ∈ Finset.range m, P (m + 1) b * w (m + 1) (b + 1) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        rw [Finset.mem_range] at hb
        rw [w_eq_zero_of_lt (m + 1) (b + 1) (by omega), mul_zero]
      rw [hzero, zero_add, P_subdiag m, P_diag (m + 1), w_diag (m + 1), w_succ (m + 1)]
      push_cast
      ring
  · by_cases hsub : j.val + 1 = i.val
    · have hne1 : i.val + 1 ≠ j.val := by omega
      simp only [T, Matrix.of_apply, hij, hne1, hsub, ↓reduceIte]
      rw [← hsub, Finset.sum_range_succ]
      have hzero : ∑ b ∈ Finset.range j.val, P j.val b * w (j.val + 1) (b + 1) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        rw [Finset.mem_range] at hb
        rw [w_eq_zero_of_lt (j.val + 1) (b + 1) (by omega), mul_zero]
      rw [hzero, zero_add, P_diag j.val, w_diag (j.val + 1), pow_succ]
      ring
    · have hlt : j.val + 1 < i.val := by
        have : j.val ≠ i.val := fun h => hij (Fin.ext h.symm)
        omega
      have hne1 : i.val + 1 ≠ j.val := by omega
      simp only [T, Matrix.of_apply, hij, hne1, hsub, ↓reduceIte]
      have hzero : ∑ b ∈ Finset.range (j.val + 1), P j.val b * w i.val (b + 1) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        rw [Finset.mem_range] at hb
        rw [w_eq_zero_of_lt i.val (b + 1) (by omega), mul_zero]
      rw [hzero, mul_zero]

private lemma LHL_eq_T (n : ℕ) : L n * H n * (L n)ᵀ = T n := by
  ext i j
  by_cases hji : j.val ≤ i.val
  · exact LHL_entry_of_le n i j hji
  · have hij : i.val ≤ j.val := by omega
    have hsym : (L n * H n * (L n)ᵀ)ᵀ = L n * H n * (L n)ᵀ := by
      simp [Matrix.transpose_mul, H_transpose, Matrix.mul_assoc]
    have h1 : (L n * H n * (L n)ᵀ) i j = (L n * H n * (L n)ᵀ) j i := by
      simpa [Matrix.transpose_apply] using congrArg (fun M => M j i) hsym
    have h2 : T n j i = T n i j := by
      simpa [Matrix.transpose_apply] using congrArg (fun M => M i j) (T_transpose n)
    rw [h1, LHL_entry_of_le n j i hij, h2]

private lemma hankel_eq_T_det (n : ℕ) : hankel n = (T n).det := by
  have h : (T n).det = (H n).det := by
    rw [← LHL_eq_T, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, L_det]
    ring
  rw [h]
  rfl

private lemma T_det_zero : (T 0).det = 1 := by
  simp [T]

private lemma T_det_one : (T 1).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [T]
  norm_num

private lemma T_det_rec (n : ℕ) :
    (T (n + 2)).det = (2 : ℚ) ^ (n + 2) * (T (n + 1)).det - (4 : ℚ) ^ (n + 1) * (T n).det := by
  let last2 : Fin (n + 3) := Fin.last (n + 2)
  let prev2 : Fin (n + 3) := (Fin.last (n + 1)).castSucc
  rw [Matrix.det_succ_row (T (n + 2)) last2]
  have hsum :
      (∑ j : Fin (n + 3),
        (-1 : ℚ) ^ (last2.val + j.val) * T (n + 2) last2 j *
          ((T (n + 2)).submatrix last2.succAbove j.succAbove).det) =
      (-1 : ℚ) ^ (last2.val + last2.val) * T (n + 2) last2 last2 *
        ((T (n + 2)).submatrix last2.succAbove last2.succAbove).det +
      (-1 : ℚ) ^ (last2.val + prev2.val) * T (n + 2) last2 prev2 *
        ((T (n + 2)).submatrix last2.succAbove prev2.succAbove).det := by
    have hne : last2 ≠ prev2 := by
      intro h
      have := congrArg Fin.val h
      simp [last2, prev2] at this
    rw [← Finset.sum_subset (s₁ := {last2, prev2}) (Finset.subset_univ _)]
    · rw [Finset.sum_pair hne]
    · intro j _ hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      have hj1 : last2 ≠ j := fun h => hj.1 h.symm
      have hj2 : last2.val + 1 ≠ j.val := by
        simp [last2]; omega
      have hj3 : j.val + 1 ≠ last2.val := by
        intro h
        apply hj.2
        ext
        simp [last2, prev2] at h ⊢
        omega
      have hentry : T (n + 2) last2 j = 0 := by
        simp [T, hj1, hj2, hj3]
      simp [hentry]
  rw [hsum]
  have hsub1 : (T (n + 2)).submatrix last2.succAbove last2.succAbove = T (n + 1) := by
    ext i j
    simp only [Matrix.submatrix_apply, last2, Fin.succAbove_last, T, Matrix.of_apply,
      Fin.val_castSucc]
    simp [Fin.castSucc_inj]
  have hM :
      ((T (n + 2)).submatrix last2.succAbove prev2.succAbove).det =
        -((2 : ℚ) ^ (n + 1)) * (T n).det := by
    let M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ :=
      (T (n + 2)).submatrix last2.succAbove prev2.succAbove
    let last1 : Fin (n + 2) := Fin.last (n + 1)
    change M.det = -((2 : ℚ) ^ (n + 1)) * (T n).det
    rw [Matrix.det_succ_column M last1]
    have hcol :
        (∑ i : Fin (n + 2),
          (-1 : ℚ) ^ (i.val + last1.val) * M i last1 *
            (M.submatrix i.succAbove last1.succAbove).det) =
        (-1 : ℚ) ^ (last1.val + last1.val) * M last1 last1 *
          (M.submatrix last1.succAbove last1.succAbove).det := by
      rw [Finset.sum_eq_single last1]
      · intro i _ hi
        have hlt : i.val < n + 1 := by
          have := i.isLt
          have : i.val ≠ n + 1 := fun h => hi (Fin.ext h)
          omega
        have hprev_last : prev2.succAbove last1 = last2 := by
          ext
          simp only [prev2, last1, last2, Fin.succAbove]
          split_ifs with h
          · exfalso
            have : (Fin.last (n + 1)).castSucc.val ≤ (Fin.last (n + 1)).castSucc.val := le_rfl
            have h' : (Fin.last (n + 1)).castSucc.val < (Fin.last (n + 1)).castSucc.val := h
            omega
          · simp
        have hMentry : M i last1 = 0 := by
          simp only [M, Matrix.submatrix_apply, last2, Fin.succAbove_last, hprev_last, T,
            Matrix.of_apply, Fin.val_castSucc, Fin.val_last]
          have h1 : i.castSucc ≠ Fin.last (n + 2) := by
            intro h
            have := congrArg Fin.val h
            simp at this
            omega
          have h2 : i.val ≠ n + 1 := by omega
          have h3 : n + 2 + 1 ≠ i.val := by omega
          simp [h1, h2, h3]
        simp [hMentry]
      · intro h; exact absurd (Finset.mem_univ last1) h
    rw [hcol]
    have hprev_last : prev2.succAbove last1 = last2 := by
      ext
      simp only [prev2, last1, last2, Fin.succAbove]
      split_ifs with h
      · exfalso
        have h' : (Fin.last (n + 1)).castSucc.val < (Fin.last (n + 1)).castSucc.val := h
        omega
      · simp
    have hMlast : M last1 last1 = -((2 : ℚ) ^ (n + 1)) := by
      simp only [M, Matrix.submatrix_apply, last2, Fin.succAbove_last, hprev_last, T,
        Matrix.of_apply, Fin.val_castSucc, Fin.val_last]
      have h1 : (last1.castSucc : Fin (n + 3)) ≠ Fin.last (n + 2) := by
        intro h
        have := congrArg Fin.val h
        simp [last1] at this
      simp [last1, h1]
    have hMsub : M.submatrix last1.succAbove last1.succAbove = T n := by
      ext i j
      have hpj : prev2.succAbove (last1.succAbove j) = j.castSucc.castSucc := by
        have hl : last1.succAbove j = j.castSucc := congrFun (Fin.succAbove_last) j
        rw [hl]
        simp only [prev2, Fin.succAbove]
        rw [if_pos]
        change j.val < n + 1
        omega
      simp only [M, Matrix.submatrix_apply]
      rw [hpj]
      simp only [last2, last1, Fin.succAbove_last, T, Matrix.of_apply, Fin.val_castSucc,
        Fin.castSucc_inj]
    have hsign : (-1 : ℚ) ^ (last1.val + last1.val) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    rw [hsign, hMlast, hMsub, one_mul]
  have hs1 : (-1 : ℚ) ^ (last2.val + last2.val) = 1 := by
    rw [← two_mul, pow_mul]
    norm_num
  have hs2 : (-1 : ℚ) ^ (last2.val + prev2.val) = -1 := by
    have heq : last2.val + prev2.val = 2 * (n + 1) + 1 := by
      simp [last2, prev2]
      omega
    rw [heq, pow_succ, pow_mul]
    norm_num
  have hT1 : T (n + 2) last2 last2 = (2 : ℚ) ^ (n + 2) := by
    simp [T, last2]
  have hT2 : T (n + 2) last2 prev2 = -((2 : ℚ) ^ (n + 1)) := by
    have hne : last2 ≠ prev2 := by
      intro h
      have := congrArg Fin.val h
      simp [last2, prev2] at this
    simp [T, hne, last2, prev2]
  rw [hs1, hs2, hT1, hT2, hsub1, hM]
  have h4 : (4 : ℚ) ^ (n + 1) = (2 : ℚ) ^ (n + 1) * (2 : ℚ) ^ (n + 1) := by
    rw [← mul_pow]
    norm_num
  rw [h4]
  ring

private lemma closedForm_zero : closedForm 0 = 1 := by
  norm_num [closedForm]

private lemma closedForm_one : closedForm 1 = 1 := by
  norm_num [closedForm]

private lemma closedForm_rec (n : ℕ) :
    closedForm (n + 2) =
      (2 : ℚ) ^ (n + 2) * closedForm (n + 1) - (4 : ℚ) ^ (n + 1) * closedForm n := by
  set q := n / 4
  have hrem : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hrem with hr | hr | hr | hr
  · have hn : n = 4 * q := by omega
    rw [hn]
    have hmod0 : (4 * q + 2) % 4 ≠ 0 := by omega
    have hmod1 : (4 * q + 1 + 2) % 4 ≠ 0 := by omega
    have hmod2 : (4 * q + 2 + 2) % 4 = 0 := by omega
    have hd0 : (4 * q) ^ 2 / 4 = 4 * q ^ 2 := by
      have : (4 * q) ^ 2 = 4 * (4 * q ^ 2) := by ring
      omega
    have hd1 : (4 * q + 1) ^ 2 / 4 = 4 * q ^ 2 + 2 * q := by
      have : (4 * q + 1) ^ 2 = 4 * (4 * q ^ 2 + 2 * q) + 1 := by ring
      omega
    have hs0 : (4 * q + 2) / 4 = q := by omega
    have hs1 : (4 * q + 1 + 2) / 4 = q := by omega
    simp only [closedForm, hmod0, hmod1, hmod2, ↓reduceIte, hd0, hd1, hs0, hs1]
    have h2 : (2 : ℚ) ^ (4 * q + 2) = (4 : ℚ) ^ (2 * q + 1) := by
      rw [show 4 * q + 2 = 2 * (2 * q + 1) by omega, pow_mul]
      norm_num
    rw [h2, ← mul_assoc, ← pow_add, ← mul_assoc, ← pow_add]
    have hexp : 2 * q + 1 + (4 * q ^ 2 + 2 * q) = 4 * q + 1 + 4 * q ^ 2 := by ring
    rw [hexp, sub_self]
  · have hn : n = 4 * q + 1 := by omega
    rw [hn]
    have hmod0 : (4 * q + 1 + 2) % 4 ≠ 0 := by omega
    have hmod1 : (4 * q + 1 + 1 + 2) % 4 = 0 := by omega
    have hmod2 : (4 * q + 1 + 2 + 2) % 4 ≠ 0 := by omega
    have hd0 : (4 * q + 1) ^ 2 / 4 = 4 * q ^ 2 + 2 * q := by
      have : (4 * q + 1) ^ 2 = 4 * (4 * q ^ 2 + 2 * q) + 1 := by ring
      omega
    have hd2 : (4 * q + 1 + 2) ^ 2 / 4 = 4 * q ^ 2 + 6 * q + 2 := by
      have : (4 * q + 1 + 2) ^ 2 = 4 * (4 * q ^ 2 + 6 * q + 2) + 1 := by ring
      omega
    have hs0 : (4 * q + 1 + 2) / 4 = q := by omega
    have hs2 : (4 * q + 1 + 2 + 2) / 4 = q + 1 := by omega
    simp only [closedForm, hmod0, hmod1, hmod2, ↓reduceIte, hd0, hd2, hs0, hs2]
    rw [mul_zero, zero_sub, ← mul_assoc, ← pow_add, pow_succ]
    have hexp : 4 * q + 1 + 1 + (4 * q ^ 2 + 2 * q) = 4 * q ^ 2 + 6 * q + 2 := by ring
    rw [hexp]
    ring
  · have hn : n = 4 * q + 2 := by omega
    rw [hn]
    have hmod0 : (4 * q + 2 + 2) % 4 = 0 := by omega
    have hmod1 : (4 * q + 2 + 1 + 2) % 4 ≠ 0 := by omega
    have hmod2 : (4 * q + 2 + 2 + 2) % 4 ≠ 0 := by omega
    have hd1 : (4 * q + 2 + 1) ^ 2 / 4 = 4 * q ^ 2 + 6 * q + 2 := by
      have : (4 * q + 2 + 1) ^ 2 = 4 * (4 * q ^ 2 + 6 * q + 2) + 1 := by ring
      omega
    have hd2 : (4 * q + 2 + 2) ^ 2 / 4 = 4 * q ^ 2 + 8 * q + 4 := by
      have : (4 * q + 2 + 2) ^ 2 = 4 * (4 * q ^ 2 + 8 * q + 4) := by ring
      omega
    have hs1 : (4 * q + 2 + 1 + 2) / 4 = q + 1 := by omega
    have hs2 : (4 * q + 2 + 2 + 2) / 4 = q + 1 := by omega
    simp only [closedForm, hmod0, hmod1, hmod2, ↓reduceIte, hd1, hd2, hs1, hs2]
    have h2 : (2 : ℚ) ^ (4 * q + 2 + 2) = (4 : ℚ) ^ (2 * q + 2) := by
      rw [show 4 * q + 2 + 2 = 2 * (2 * q + 2) by omega, pow_mul]
      norm_num
    rw [h2, mul_zero, sub_zero, ← mul_assoc, ← pow_add]
    have hexp : 2 * q + 2 + (4 * q ^ 2 + 6 * q + 2) = 4 * q ^ 2 + 8 * q + 4 := by ring
    rw [hexp]
  · have hn : n = 4 * q + 3 := by omega
    rw [hn]
    have hmod0 : (4 * q + 3 + 2) % 4 ≠ 0 := by omega
    have hmod1 : (4 * q + 3 + 1 + 2) % 4 ≠ 0 := by omega
    have hmod2 : (4 * q + 3 + 2 + 2) % 4 ≠ 0 := by omega
    have hd0 : (4 * q + 3) ^ 2 / 4 = 4 * q ^ 2 + 6 * q + 2 := by
      have : (4 * q + 3) ^ 2 = 4 * (4 * q ^ 2 + 6 * q + 2) + 1 := by ring
      omega
    have hd1 : (4 * q + 3 + 1) ^ 2 / 4 = 4 * q ^ 2 + 8 * q + 4 := by
      have : (4 * q + 3 + 1) ^ 2 = 4 * (4 * q ^ 2 + 8 * q + 4) := by ring
      omega
    have hd2 : (4 * q + 3 + 2) ^ 2 / 4 = 4 * q ^ 2 + 10 * q + 6 := by
      have : (4 * q + 3 + 2) ^ 2 = 4 * (4 * q ^ 2 + 10 * q + 6) + 1 := by ring
      omega
    have hs0 : (4 * q + 3 + 2) / 4 = q + 1 := by omega
    have hs1 : (4 * q + 3 + 1 + 2) / 4 = q + 1 := by omega
    have hs2 : (4 * q + 3 + 2 + 2) / 4 = q + 1 := by omega
    simp only [closedForm, hmod0, hmod1, hmod2, ↓reduceIte, hd0, hd1, hd2, hs0, hs1, hs2]
    have h2 : (2 : ℚ) ^ (4 * q + 3 + 2) = 2 * (4 : ℚ) ^ (2 * q + 2) := by
      rw [show 4 * q + 3 + 2 = 2 * (2 * q + 2) + 1 by omega, pow_succ, pow_mul]
      norm_num
      ring
    rw [h2]
    have hA : 2 * (4 : ℚ) ^ (2 * q + 2) * ((4 : ℚ) ^ (4 * q ^ 2 + 8 * q + 4) * (-1) ^ (q + 1)) =
        2 * ((4 : ℚ) ^ (4 * q ^ 2 + 10 * q + 6) * (-1) ^ (q + 1)) := by
      have hexp : 2 * q + 2 + (4 * q ^ 2 + 8 * q + 4) = 4 * q ^ 2 + 10 * q + 6 := by ring
      rw [← hexp, pow_add]
      ring
    have hB : (4 : ℚ) ^ (4 * q + 3 + 1) * ((4 : ℚ) ^ (4 * q ^ 2 + 6 * q + 2) * (-1) ^ (q + 1)) =
        (4 : ℚ) ^ (4 * q ^ 2 + 10 * q + 6) * (-1) ^ (q + 1) := by
      have hexp : 4 * q + 3 + 1 + (4 * q ^ 2 + 6 * q + 2) = 4 * q ^ 2 + 10 * q + 6 := by ring
      rw [← mul_assoc, ← pow_add, hexp]
    rw [hA, hB]
    ring

private theorem T_det_eq_closedForm : ∀ n : ℕ, (T n).det = closedForm n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rw [T_det_zero, closedForm_zero]
    · rw [T_det_one, closedForm_one]
    · rw [T_det_rec, closedForm_rec, ih (n + 1) (by omega), ih n (by omega)]

private theorem main_proof : ∀ n : ℕ, hankel n = closedForm n := by
  intro n
  rw [hankel_eq_T_det, T_det_eq_closedForm]

end OMA.A136576Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a136576.main :=
  OMA.A136576Proof.main_proof
