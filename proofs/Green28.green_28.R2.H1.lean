import OMAReductions.R_Green28_green_28_R2
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Degree-five factor binary criterion for Green's Problem 28 (`Green28.green_28.R2.H1`).
-/

open scoped Polynomial
open Polynomial

namespace OMA.Green28Deg5

private theorem conv_one (P Q : ℝ[X]) (p0 : P.coeff 0 = 1) (q0 : Q.coeff 0 = 1) :
    (P * Q).coeff 1 = P.coeff 1 + Q.coeff 1 := by
  rw [Polynomial.coeff_mul]
  have hset : Finset.HasAntidiagonal.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
  rw [hset, Finset.sum_pair (by decide), p0, q0, one_mul, mul_one, add_comm]

private theorem conv_two (P Q : ℝ[X]) (p0 : P.coeff 0 = 1) (q0 : Q.coeff 0 = 1) :
    (P * Q).coeff 2 = P.coeff 2 + P.coeff 1 * Q.coeff 1 + Q.coeff 2 := by
  rw [Polynomial.coeff_mul]
  have hset : Finset.HasAntidiagonal.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
  rw [hset, Finset.sum_insert (by decide), Finset.sum_pair (by decide), p0, q0, one_mul, mul_one]
  ring

private theorem conv_three (P Q : ℝ[X]) (p0 : P.coeff 0 = 1) (q0 : Q.coeff 0 = 1) :
    (P * Q).coeff 3 =
      P.coeff 3 + P.coeff 2 * Q.coeff 1 + P.coeff 1 * Q.coeff 2 + Q.coeff 3 := by
  rw [Polynomial.coeff_mul]
  have hset : Finset.HasAntidiagonal.antidiagonal 3 = {(0, 3), (1, 2), (2, 1), (3, 0)} := by
    decide
  rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_pair (by decide), p0, q0, one_mul, mul_one]
  ring

private theorem conv_four (P Q : ℝ[X]) (p0 : P.coeff 0 = 1) (q0 : Q.coeff 0 = 1) :
    (P * Q).coeff 4 =
      P.coeff 4 + P.coeff 3 * Q.coeff 1 + P.coeff 2 * Q.coeff 2 +
        P.coeff 1 * Q.coeff 3 + Q.coeff 4 := by
  rw [Polynomial.coeff_mul]
  have hset :
      Finset.HasAntidiagonal.antidiagonal 4 =
        {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} := by decide
  rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_pair (by decide), p0, q0, one_mul, mul_one]
  ring

private theorem r1_pos {x : ℝ} (h : x = 0 ∨ x = 1) (hx : 0 < x) : x = 1 :=
  h.resolve_left hx.ne'

private theorem rf_forbid {x : ℝ} (h : x = 0 ∨ x = 1) (h0 : 0 < x) (h1 : x < 1) : False :=
  h1.ne (r1_pos h h0)

private theorem eq_one_sub_of_pos {x b : ℝ} (h : x + b = 0 ∨ x + b = 1)
    (hx : 0 ≤ x) (hb : 0 < b) : x = 1 - b := by
  rcases h with h0 | h1 <;> linarith

private theorem absurd_of_gt_one {x b : ℝ} (h : x + b = 0 ∨ x + b = 1)
    (hx : 0 ≤ x) (hb : 1 < b) : False := by
  rcases h with h0 | h1 <;> linarith

private theorem saturated_deg5 {P Q : ℝ[X]} (mp : P.Monic) (q0 : Q.coeff 0 = 1)
    (hp : ∀ i, 0 ≤ P.coeff i) (hq : ∀ i, 0 ≤ Q.coeff i)
    (hb : ∀ i, (P * Q).coeff i = 0 ∨ (P * Q).coeff i = 1)
    (d5 : P.natDegree = 5) (i j : ℕ) (hs : i + j = 5) (hj : 0 < j) :
    P.coeff i * Q.coeff j = 0 := by
  have hl := GreenFactorBounds.coeff_product_two_lower P Q hp hq (P.natDegree, 0) (i, j)
    (Nat.add_zero _) (by rw [d5, hs]) (fun h => (Nat.ne_of_gt hj) (congrArg Prod.snd h).symm)
  change P.coeff P.natDegree * Q.coeff 0 + P.coeff i * Q.coeff j ≤ _ at hl
  rw [mp.coeff_natDegree, q0, one_mul] at hl
  have hu : (P * Q).coeff P.natDegree ≤ 1 := by rcases hb _ with h0 | h1 <;> linarith
  exact le_antisymm (by linarith) (mul_nonneg (hp i) (hq j))

private theorem reverseFacts (P : ℝ[X]) (mp : P.Monic) (hp : ∀ i, 0 ≤ P.coeff i)
    (p0 : P.coeff 0 = 1) :
    P.reverse.Monic ∧ (∀ i, 0 ≤ P.reverse.coeff i) ∧
      P.reverse.coeff 0 = 1 ∧ P.reverse.natDegree = P.natDegree := by
  have ht : P.natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by rw [p0]; exact one_ne_zero))
  have hc : P.trailingCoeff = 1 := by rw [Polynomial.trailingCoeff, ht, p0]
  refine ⟨by change _ = 1; rw [Polynomial.reverse_leadingCoeff, hc],
    fun i => by rw [Polynomial.coeff_reverse]; exact hp _, ?_, ?_⟩
  · rw [Polynomial.coeff_zero_reverse, mp.leadingCoeff]
  · rw [Polynomial.reverse_natDegree, ht, Nat.sub_zero]

private theorem reverse_mul_binary {P Q : ℝ[X]}
    (hb : ∀ i, (P * Q).coeff i = 0 ∨ (P * Q).coeff i = 1) :
    ∀ i, (P.reverse * Q.reverse).coeff i = 0 ∨ (P.reverse * Q.reverse).coeff i = 1 := by
  intro i
  rw [← Polynomial.reverse_mul_of_domain, Polynomial.coeff_reverse]
  exact hb _

private theorem first_binary_deg5 {P Q : ℝ[X]} (mp : P.Monic) (mq : Q.Monic)
    (hp : ∀ i, 0 ≤ P.coeff i) (hq : ∀ i, 0 ≤ Q.coeff i)
    (p0 : P.coeff 0 = 1) (q0 : Q.coeff 0 = 1) (d5 : P.natDegree = 5)
    (hb : ∀ i, (P * Q).coeff i = 0 ∨ (P * Q).coeff i = 1) :
    P.coeff 1 = 0 ∨ P.coeff 1 = 1 := by
  by_cases ha0 : P.coeff 1 = 0
  · exact Or.inl ha0
  by_cases ha1 : P.coeff 1 = 1
  · exact Or.inr ha1
  exfalso
  have hp1_pos : 0 < P.coeff 1 := lt_of_le_of_ne (hp 1) (Ne.symm ha0)
  have hp1_lt : P.coeff 1 < 1 :=
    lt_of_le_of_ne (GreenFactorBounds.factor_coeff_upper P Q hp hq mq hb 1) ha1
  have hr1 : P.coeff 1 + Q.coeff 1 = 1 := by
    have h1 := conv_one P Q p0 q0
    exact h1.symm.trans (r1_pos (hb 1) (by rw [h1]; linarith [hq 1]))
  have hq1_pos : 0 < Q.coeff 1 := by linarith
  have hq1_lt : Q.coeff 1 < 1 := by linarith
  have hpp : 0 < P.coeff 1 * Q.coeff 1 := mul_pos hp1_pos hq1_pos
  have hpt : P.coeff 1 * Q.coeff 1 < 1 :=
    (mul_le_of_le_one_right hp1_pos.le hq1_lt.le).trans_lt hp1_lt
  have m41 := saturated_deg5 mp q0 hp hq hb d5 4 1 (by decide) (by decide)
  have m14 := saturated_deg5 mp q0 hp hq hb d5 1 4 (by decide) (by decide)
  have m32 := saturated_deg5 mp q0 hp hq hb d5 3 2 (by decide) (by decide)
  have m23 := saturated_deg5 mp q0 hp hq hb d5 2 3 (by decide) (by decide)
  have hp4 : P.coeff 4 = 0 := (mul_eq_zero.mp m41).resolve_right hq1_pos.ne'
  have hq4 : Q.coeff 4 = 0 := (mul_eq_zero.mp m14).resolve_left hp1_pos.ne'
  have h2sum : P.coeff 2 + Q.coeff 2 = 1 - P.coeff 1 * Q.coeff 1 := by
    have h2 := conv_two P Q p0 q0
    have h2one : (P * Q).coeff 2 = 1 :=
      r1_pos (hb 2) (by rw [h2]; linarith [hp 2, hq 2])
    linarith
  have h3eq := conv_three P Q p0 q0
  have h4eq := conv_four P Q p0 q0
  rw [hp4, hq4, zero_add, add_zero] at h4eq
  rcases mul_eq_zero.mp m32 with hp3 | hq2 <;> rcases mul_eq_zero.mp m23 with hp2 | hq3
  · have hq2_pos : 0 < Q.coeff 2 := by rw [hp2, zero_add] at h2sum; linarith
    have hq2_lt : Q.coeff 2 < 1 := by rw [hp2, zero_add] at h2sum; linarith
    rw [hp3, hp2, zero_mul, zero_mul, zero_add, zero_add] at h4eq
    have hbSwap : ∀ i, (Q * P).coeff i = 0 ∨ (Q * P).coeff i = 1 := fun i => by
      simpa only [mul_comm Q P] using hb i
    have hq3_le : Q.coeff 3 ≤ 1 := GreenFactorBounds.factor_coeff_upper Q P hq hp mp hbSwap 3
    have h4lt : P.coeff 1 * Q.coeff 3 < 1 :=
      (mul_le_of_le_one_right hp1_pos.le hq3_le).trans_lt hp1_lt
    have hp1q3 : P.coeff 1 * Q.coeff 3 = 0 := by
      rw [← h4eq]
      exact (hb 4).resolve_right (by rw [h4eq]; exact h4lt.ne)
    have hq3 : Q.coeff 3 = 0 := (mul_eq_zero.mp hp1q3).resolve_left hp1_pos.ne'
    rw [hp3, hp2, hq3, zero_mul, zero_add, zero_add, add_zero] at h3eq
    have hlt := (mul_le_of_le_one_left hq2_pos.le hp1_lt.le).trans_lt hq2_lt
    exact rf_forbid (hb 3) (h3eq.symm ▸ mul_pos hp1_pos hq2_pos) (h3eq.symm ▸ hlt)
  · rw [hp3, hq3, zero_mul, mul_zero, zero_add, add_zero] at h4eq
    have hp2_lt : P.coeff 2 < 1 := by linarith [hq 2]
    have hq2_lt : Q.coeff 2 < 1 := by linarith [hp 2]
    have h4lt : P.coeff 2 * Q.coeff 2 < 1 :=
      (mul_le_of_le_one_right (hp 2) hq2_lt.le).trans_lt hp2_lt
    have hp2q2 : P.coeff 2 * Q.coeff 2 = 0 := by
      rw [← h4eq]
      exact (hb 4).resolve_right (by rw [h4eq]; exact h4lt.ne)
    rcases mul_eq_zero.mp hp2q2 with hp2 | hq2
    · have hq2_pos : 0 < Q.coeff 2 := by rw [hp2, zero_add] at h2sum; linarith
      rw [hp3, hp2, hq3, zero_mul, zero_add, zero_add, add_zero] at h3eq
      have hlt := (mul_le_of_le_one_left hq2_pos.le hp1_lt.le).trans_lt hq2_lt
      exact rf_forbid (hb 3) (h3eq.symm ▸ mul_pos hp1_pos hq2_pos) (h3eq.symm ▸ hlt)
    · have hp2_pos : 0 < P.coeff 2 := by rw [hq2, add_zero] at h2sum; linarith
      rw [hp3, hq2, hq3, mul_zero, zero_add, add_zero, add_zero] at h3eq
      have hlt := (mul_le_of_le_one_right hp2_pos.le hq1_lt.le).trans_lt hp2_lt
      exact rf_forbid (hb 3) (h3eq.symm ▸ mul_pos hp2_pos hq1_pos) (h3eq.symm ▸ hlt)
  · rw [hp2, hq2, zero_add] at h2sum
    linarith
  · have hp2_pos : 0 < P.coeff 2 := by rw [hq2, add_zero] at h2sum; linarith
    have hp2_lt : P.coeff 2 < 1 := by rw [hq2, add_zero] at h2sum; linarith
    rw [hq2, hq3, mul_zero, mul_zero, add_zero, add_zero] at h4eq
    have hp3_le : P.coeff 3 ≤ 1 := GreenFactorBounds.factor_coeff_upper P Q hp hq mq hb 3
    have h4lt : P.coeff 3 * Q.coeff 1 < 1 :=
      (mul_le_of_le_one_left hq1_pos.le hp3_le).trans_lt hq1_lt
    have hp3q1 : P.coeff 3 * Q.coeff 1 = 0 := by
      rw [← h4eq]
      exact (hb 4).resolve_right (by rw [h4eq]; exact h4lt.ne)
    have hp3 : P.coeff 3 = 0 := (mul_eq_zero.mp hp3q1).resolve_right hq1_pos.ne'
    rw [hp3, hq2, hq3, mul_zero, zero_add, add_zero, add_zero] at h3eq
    have hlt := (mul_le_of_le_one_right hp2_pos.le hq1_lt.le).trans_lt hp2_lt
    exact rf_forbid (hb 3) (h3eq.symm ▸ mul_pos hp2_pos hq1_pos) (h3eq.symm ▸ hlt)

private theorem coeff_mul_trinomial (a : ℝ) (j : ℕ) (Q : ℝ[X]) (k : ℕ) :
    ((1 + C a * X ^ j + X ^ 5) * Q).coeff k =
      Q.coeff k + (if j ≤ k then a * Q.coeff (k - j) else 0) +
        (if 5 ≤ k then Q.coeff (k - 5) else 0) := by
  rw [add_mul, add_mul, one_mul, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  split_ifs <;> ring

private theorem no_fwd_gt_two_fifths {a : ℝ} (ha : 2 / 5 < a) (ha1 : a < 1)
    {Q : ℝ[X]} (hq : ∀ i, 0 ≤ Q.coeff i) (q0 : Q.coeff 0 = 1)
    (hb : ∀ k, ((1 + C a * X ^ 2 + X ^ 5) * Q).coeff k = 0 ∨
      ((1 + C a * X ^ 2 + X ^ 5) * Q).coeff k = 1) : False := by
  let q : ℕ → ℝ := Q.coeff
  have hq0 : q 0 = 1 := q0
  have step (k : ℕ) (hk : 5 ≤ k) :
      q k + (a * q (k - 2) + q (k - 5)) = 0 ∨ q k + (a * q (k - 2) + q (k - 5)) = 1 := by
    have hk2 : 2 ≤ k := by omega
    have h := hb k
    rw [coeff_mul_trinomial, if_pos hk2, if_pos hk, add_assoc] at h
    exact h
  have ha0 : 0 < a := by linarith
  have hk5 : q 5 + (a * q 3 + q 0) = 0 ∨ q 5 + (a * q 3 + q 0) = 1 := step 5 (by decide)
  rw [hq0] at hk5
  have hq5 : q 5 = 0 := by rcases hk5 with h | h <;> nlinarith [hq 5, hq 3]
  have haq3 : a * q 3 = 0 := by rcases hk5 with h | h <;> nlinarith [hq 5, hq 3]
  have hq3 : q 3 = 0 := (mul_eq_zero.mp haq3).resolve_left ha0.ne'
  have hk2 : q 2 + a * q 0 = 0 ∨ q 2 + a * q 0 = 1 := by
    simpa only [q, coeff_mul_trinomial, if_pos (by decide : 2 ≤ 2),
      if_neg (by decide : ¬ (5 ≤ 2)), add_zero] using hb 2
  rw [hq0, mul_one] at hk2
  have hq2 : q 2 = 1 - a := eq_one_sub_of_pos hk2 (hq 2) ha0
  have hk1 : q 1 = 0 ∨ q 1 = 1 := by
    simpa only [q, coeff_mul_trinomial, if_neg (by decide : ¬ (2 ≤ 1)),
      if_neg (by decide : ¬ (5 ≤ 1)), add_zero] using hb 1
  have hk3 : a * q 1 = 0 ∨ a * q 1 = 1 := by
    have h3 := hb 3
    rw [coeff_mul_trinomial, if_pos (by decide : 2 ≤ 3), if_neg (by decide : ¬ (5 ≤ 3))] at h3
    simpa only [q, hq3, zero_add, add_zero] using h3
  have hq1 : q 1 = 0 := by
    rcases hk1 with h | h
    · exact h
    · exfalso
      rw [h, mul_one] at hk3
      rcases hk3 with h0 | h1 <;> linarith
  have hk4 : q 4 + a * (1 - a) = 0 ∨ q 4 + a * (1 - a) = 1 := by
    have h4 := hb 4
    rw [coeff_mul_trinomial, if_pos (by decide : 2 ≤ 4), if_neg (by decide : ¬ (5 ≤ 4))] at h4
    simpa only [q, hq2, add_zero] using h4
  have hq4 : q 4 = 1 - a + a ^ 2 := by
    have h := eq_one_sub_of_pos hk4 (hq 4) (mul_pos ha0 (by linarith))
    linarith
  have hq7 : q 7 = a := by
    have h7 := step 7 (by decide)
    rw [hq5, hq2, mul_zero, zero_add] at h7
    have h := eq_one_sub_of_pos h7 (hq 7) (by linarith)
    linarith
  by_cases ha_half : 1 / 2 < a
  · have h9 := step 9 (by decide)
    rw [hq7, hq4] at h9
    have hb9 : 1 < a * a + (1 - a + a ^ 2) := by nlinarith
    exact absurd_of_gt_one h9 (hq 9) hb9
  · obtain ⟨u, v, hu, hv, hu_eq, hv_eq⟩ :
        ∃ u v : ℝ, 0 < u ∧ 0 ≤ v ∧ u = a - 2 / 5 ∧ v = 1 / 2 - a :=
      ⟨a - 2 / 5, 1 / 2 - a, by linarith, by linarith, rfl, rfl⟩
    have hb6 : 0 < a * q 4 + q 1 := by
      have hid : a * q 4 + q 1 =
          304 * v ^ 3 + 980 * u * v ^ 2 + 1050 * u ^ 2 * v + 375 * u ^ 3 := by
        rw [hq4, hq1, hu_eq, hv_eq]; ring
      rw [hid]; positivity
    have hq6 : q 6 = 1 - a + a ^ 2 - a ^ 3 := by
      have h := eq_one_sub_of_pos (step 6 (by decide)) (hq 6) hb6
      rw [h, hq4, hq1]; ring
    have hb8 : 0 < a * q 6 + q 3 := by
      have hid : a * q 6 + q 3 =
          2784 * v ^ 4 + 11560 * u * v ^ 3 + 17900 * u ^ 2 * v ^ 2 +
            12250 * u ^ 3 * v + 3125 * u ^ 4 := by
        rw [hq6, hq3, hu_eq, hv_eq]; ring
      rw [hid]; positivity
    have hq8 : q 8 = 1 - a + a ^ 2 - a ^ 3 + a ^ 4 := by
      have h := eq_one_sub_of_pos (step 8 (by decide)) (hq 8) hb8
      rw [h, hq6, hq3]; ring
    have hb9 : 0 < a * q 7 + q 4 := by
      have hid : a * q 7 + q 4 = 92 * v ^ 2 + 190 * u * v + 100 * u ^ 2 := by
        rw [hq7, hq4, hu_eq, hv_eq]; ring
      rw [hid]; positivity
    have hq9 : q 9 = a - 2 * a ^ 2 := by
      have h := eq_one_sub_of_pos (step 9 (by decide)) (hq 9) hb9
      rw [h, hq7, hq4]; ring
    have hb10 : 0 < a * q 8 + q 5 := by
      have hid : a * q 8 + q 5 =
          28864 * v ^ 5 + 149840 * u * v ^ 4 + 310600 * u ^ 2 * v ^ 3 +
            321500 * u ^ 3 * v ^ 2 + 166250 * u ^ 4 * v + 34375 * u ^ 5 := by
        rw [hq8, hq5, hu_eq, hv_eq]; ring
      rw [hid]; positivity
    have hq10 : q 10 = 1 - a + a ^ 2 - a ^ 3 + a ^ 4 - a ^ 5 := by
      have h := eq_one_sub_of_pos (step 10 (by decide)) (hq 10) hb10
      rw [h, hq8, hq5]; ring
    have hb11 : 0 < a * q 9 + q 6 := by
      have hid : a * q 9 + q 6 =
          728 * v ^ 3 + 2100 * u * v ^ 2 + 2000 * u ^ 2 * v + 625 * u ^ 3 := by
        rw [hq9, hq6, hu_eq, hv_eq]; ring
      rw [hid]; positivity
    have hq11 : q 11 = a - 2 * a ^ 2 + 3 * a ^ 3 := by
      have h := eq_one_sub_of_pos (step 11 (by decide)) (hq 11) hb11
      rw [h, hq9, hq6]; ring
    have hb12 : 0 < a * q 10 + q 7 := by
      have hid : a * q 10 + q 7 =
          684544 * v ^ 6 + 4256320 * u * v ^ 5 + 11008400 * u ^ 2 * v ^ 4 +
            15161000 * u ^ 3 * v ^ 3 + 11727500 * u ^ 4 * v ^ 2 +
            4831250 * u ^ 5 * v + 828125 * u ^ 6 := by
        rw [hq10, hq7, hu_eq, hv_eq]; ring
      rw [hid]; positivity
    have hq12 : q 12 = 1 - 2 * a + a ^ 2 - a ^ 3 + a ^ 4 - a ^ 5 + a ^ 6 := by
      have h := eq_one_sub_of_pos (step 12 (by decide)) (hq 12) hb12
      rw [h, hq10, hq7]; ring
    have hb13 : 0 < a * q 11 + q 8 := by
      have hid : a * q 11 + q 8 =
          8304 * v ^ 4 + 33400 * u * v ^ 3 + 50600 * u ^ 2 * v ^ 2 +
            34250 * u ^ 3 * v + 8750 * u ^ 4 := by
        rw [hq11, hq8, hu_eq, hv_eq]; ring
      rw [hid]; positivity
    have hq13 : q 13 = a - 2 * a ^ 2 + 3 * a ^ 3 - 4 * a ^ 4 := by
      have h := eq_one_sub_of_pos (step 13 (by decide)) (hq 13) hb13
      rw [h, hq11, hq8]; ring
    have hb14 : 0 < a * q 12 + q 9 := by
      have hid : a * q 12 + q 9 =
          2061824 * v ^ 7 + 13552000 * u * v ^ 6 + 37684800 * u ^ 2 * v ^ 5 +
            57314000 * u ^ 3 * v ^ 4 + 51285000 * u ^ 4 * v ^ 3 +
            26837500 * u ^ 5 * v ^ 2 + 7531250 * u ^ 6 * v + 859375 * u ^ 7 := by
        rw [hq12, hq9, hu_eq, hv_eq]; ring
      rw [hid]; positivity
    have hq14 : q 14 = 1 - 2 * a + 4 * a ^ 2 - a ^ 3 + a ^ 4 - a ^ 5 + a ^ 6 - a ^ 7 := by
      have h := eq_one_sub_of_pos (step 14 (by decide)) (hq 14) hb14
      rw [h, hq12, hq9]; ring
    have hb15 : 0 < a * q 13 + q 10 := by
      have hid : a * q 13 + q 10 =
          77920 * v ^ 5 + 385040 * u * v ^ 4 + 760000 * u ^ 2 * v ^ 3 +
            748500 * u ^ 3 * v ^ 2 + 367500 * u ^ 4 * v + 71875 * u ^ 5 := by
        rw [hq13, hq10, hu_eq, hv_eq]; ring
      rw [hid]; positivity
    have hq15 : q 15 = a - 2 * a ^ 2 + 3 * a ^ 3 - 4 * a ^ 4 + 5 * a ^ 5 := by
      have h := eq_one_sub_of_pos (step 15 (by decide)) (hq 15) hb15
      rw [h, hq13, hq10]; ring
    have hb17 : 0 < a * q 15 + q 12 := by
      have hid : a * q 15 + q 12 =
          403776 * v ^ 6 + 2313920 * u * v ^ 5 + 5526400 * u ^ 2 * v ^ 4 +
            7045000 * u ^ 3 * v ^ 3 + 5060000 * u ^ 4 * v ^ 2 +
            1943750 * u ^ 5 * v + 312500 * u ^ 6 := by
        rw [hq15, hq12, hu_eq, hv_eq]; ring
      rw [hid]; positivity
    have hq17 :
        q 17 = 2 * a - 2 * a ^ 2 + 3 * a ^ 3 - 4 * a ^ 4 + 5 * a ^ 5 - 6 * a ^ 6 := by
      have h := eq_one_sub_of_pos (step 17 (by decide)) (hq 17) hb17
      rw [h, hq15, hq12]; ring
    have h19 := step 19 (by decide)
    have hpos19 :
        0 < -2 + 6 * a - 3 * a ^ 2 + 4 * a ^ 3 - 5 * a ^ 4 + 6 * a ^ 5 - 7 * a ^ 6 := by
      have hid19 :
          -2 + 6 * a - 3 * a ^ 2 + 4 * a ^ 3 - 5 * a ^ 4 + 6 * a ^ 5 - 7 * a ^ 6 =
            80768 * v ^ 6 + 942400 * u * v ^ 5 + 3482000 * u ^ 2 * v ^ 4 +
              6116000 * u ^ 3 * v ^ 3 + 5667500 * u ^ 4 * v ^ 2 +
              2687500 * u ^ 5 * v + 515625 * u ^ 6 := by
        rw [hu_eq, hv_eq]; ring
      rw [hid19]; positivity
    have hdiff19 :
        a * q 17 + q 14 - 1 =
          a * (-2 + 6 * a - 3 * a ^ 2 + 4 * a ^ 3 - 5 * a ^ 4 + 6 * a ^ 5 - 7 * a ^ 6) := by
      rw [hq17, hq14]; ring
    have hgt19 : 1 < a * q 17 + q 14 := by
      have hm := mul_pos ha0 hpos19
      linarith only [hdiff19, hm]
    exact absurd_of_gt_one h19 (hq 19) hgt19

private theorem no_rev_le_two_fifths {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 2 / 5)
    {R : ℝ[X]} (hr : ∀ i, 0 ≤ R.coeff i) (r0 : R.coeff 0 = 1)
    (hb : ∀ k, ((1 + C a * X ^ 3 + X ^ 5) * R).coeff k = 0 ∨
      ((1 + C a * X ^ 3 + X ^ 5) * R).coeff k = 1) : False := by
  let r : ℕ → ℝ := R.coeff
  have hr0 : r 0 = 1 := r0
  have step (k : ℕ) (hk : 5 ≤ k) :
      r k + (a * r (k - 3) + r (k - 5)) = 0 ∨ r k + (a * r (k - 3) + r (k - 5)) = 1 := by
    have hk3 : 3 ≤ k := by omega
    have h := hb k
    rw [coeff_mul_trinomial, if_pos hk3, if_pos hk, add_assoc] at h
    exact h
  have ha1 : a < 1 := by linarith
  have hk5 : r 5 + (a * r 2 + r 0) = 0 ∨ r 5 + (a * r 2 + r 0) = 1 := step 5 (by decide)
  rw [hr0] at hk5
  have hr5 : r 5 = 0 := by rcases hk5 with h | h <;> nlinarith [hr 5, hr 2]
  have har2 : a * r 2 = 0 := by rcases hk5 with h | h <;> nlinarith [hr 5, hr 2]
  have hr2 : r 2 = 0 := (mul_eq_zero.mp har2).resolve_left ha0.ne'
  have hk3 : r 3 + a * r 0 = 0 ∨ r 3 + a * r 0 = 1 := by
    simpa only [r, coeff_mul_trinomial, if_pos (by decide : 3 ≤ 3),
      if_neg (by decide : ¬ (5 ≤ 3)), add_zero] using hb 3
  rw [hr0, mul_one] at hk3
  have hr3 : r 3 = 1 - a := eq_one_sub_of_pos hk3 (hr 3) ha0
  have hk1 : r 1 = 0 ∨ r 1 = 1 := by
    simpa only [r, coeff_mul_trinomial, if_neg (by decide : ¬ (3 ≤ 1)),
      if_neg (by decide : ¬ (5 ≤ 1)), add_zero] using hb 1
  have hb6 : 0 < a * (1 - a) := mul_pos ha0 (by linarith)
  have hr1 : r 1 = 0 := by
    rcases hk1 with h | h
    · exact h
    · exfalso
      have h6 := step 6 (by decide)
      rw [hr3, h] at h6
      exact absurd_of_gt_one h6 (hr 6) (by linarith)
  have hr6 : r 6 = 1 - a + a ^ 2 := by
    have h := eq_one_sub_of_pos (step 6 (by decide)) (hr 6) (by rw [hr3, hr1, add_zero]; exact hb6)
    rw [hr3, hr1] at h
    linarith
  have hk4 : r 4 = 0 ∨ r 4 = 1 := by
    have h4 := hb 4
    rw [coeff_mul_trinomial, if_pos (by decide : 3 ≤ 4), if_neg (by decide : ¬ (5 ≤ 4))] at h4
    simpa only [r, hr1, mul_zero, add_zero] using h4
  have hb9 : 0 < a * (1 - a + a ^ 2) := by
    have hp : 0 < 1 - a + a ^ 2 := by nlinarith
    exact mul_pos ha0 hp
  have hr4 : r 4 = 0 := by
    rcases hk4 with h | h
    · exact h
    · exfalso
      have h9 := step 9 (by decide)
      rw [hr6, h] at h9
      exact absurd_of_gt_one h9 (hr 9) (by linarith)
  have hr9 : r 9 = 1 - a + a ^ 2 - a ^ 3 := by
    have h := eq_one_sub_of_pos (step 9 (by decide)) (hr 9) (by rw [hr6, hr4, add_zero]; exact hb9)
    rw [hr6, hr4] at h
    linarith
  have hr8 : r 8 = a := by
    have h8 := step 8 (by decide)
    rw [hr5, hr3, mul_zero, zero_add] at h8
    have h := eq_one_sub_of_pos h8 (hr 8) (by linarith)
    linarith
  have hb11 : 0 < a * r 8 + r 6 := by
    rw [hr8, hr6]
    nlinarith
  have hr11 : r 11 = a - 2 * a ^ 2 := by
    have h := eq_one_sub_of_pos (step 11 (by decide)) (hr 11) hb11
    rw [hr8, hr6] at h
    linarith
  have hk7 : r 7 = 0 ∨ r 7 = 1 := by
    have h7 := step 7 (by decide)
    simpa only [hr4, hr2, mul_zero, add_zero] using h7
  have hb12 : 0 < a * (1 - a + a ^ 2 - a ^ 3) := by
    have hid : 1 - a + a ^ 2 - a ^ 3 = (1 - a) * (1 + a ^ 2) := by ring
    rw [hid]
    exact mul_pos ha0 (mul_pos (by linarith) (by positivity))
  have hr7 : r 7 = 0 := by
    rcases hk7 with h | h
    · exact h
    · exfalso
      have h12 := step 12 (by decide)
      rw [hr9, h] at h12
      exact absurd_of_gt_one h12 (hr 12) (by linarith)
  have hr12 : r 12 = 1 - a + a ^ 2 - a ^ 3 + a ^ 4 := by
    have h :=
      eq_one_sub_of_pos (step 12 (by decide)) (hr 12) (by rw [hr9, hr7, add_zero]; exact hb12)
    rw [hr9, hr7] at h
    linarith
  have hk10 : r 10 = 0 ∨ r 10 = 1 := by
    have h10 := step 10 (by decide)
    simpa only [hr7, hr5, mul_zero, add_zero] using h10
  have hb15 : 0 < a * (1 - a + a ^ 2 - a ^ 3 + a ^ 4) := by
    have hid : 1 - a + a ^ 2 - a ^ 3 + a ^ 4 = (1 - a) + a ^ 2 * (1 - a) + a ^ 4 := by ring
    rw [hid]
    exact mul_pos ha0 (by nlinarith)
  have hr10 : r 10 = 0 := by
    rcases hk10 with h | h
    · exact h
    · exfalso
      have h15 := step 15 (by decide)
      rw [hr12, h] at h15
      exact absurd_of_gt_one h15 (hr 15) (by linarith)
  have hr15 : r 15 = 1 - a + a ^ 2 - a ^ 3 + a ^ 4 - a ^ 5 := by
    have h :=
      eq_one_sub_of_pos (step 15 (by decide)) (hr 15) (by rw [hr12, hr10, add_zero]; exact hb15)
    rw [hr12, hr10] at h
    linarith
  obtain ⟨u, v, hu, hv, hu_eq, hv_eq⟩ :
      ∃ u v : ℝ, 0 < u ∧ 0 ≤ v ∧ u = a ∧ v = 2 / 5 - a :=
    ⟨a, 2 / 5 - a, ha0, by linarith only [ha], rfl, rfl⟩
  have hr13 : r 13 = 1 - a := by
    have hb13 : 0 < a * r 10 + r 8 := by rw [hr10, hr8]; linarith only [ha0]
    have h := eq_one_sub_of_pos (step 13 (by decide)) (hr 13) hb13
    rw [h, hr10, hr8]; ring
  have hb14 : 0 < a * r 11 + r 9 := by
    have hid : 8 * (a * r 11 + r 9) =
        125 * v ^ 3 + 325 * u * v ^ 2 + 315 * u ^ 2 * v + 91 * u ^ 3 := by
      rw [hr11, hr9, hu_eq, hv_eq]; ring
    linarith only [show 0 < 8 * (a * r 11 + r 9) by rw [hid]; positivity]
  have hr14 : r 14 = a - 2 * a ^ 2 + 3 * a ^ 3 := by
    have h := eq_one_sub_of_pos (step 14 (by decide)) (hr 14) hb14
    rw [h, hr11, hr9]; ring
  have hb16 : 0 < a * r 13 + r 11 := by
    rw [hr13, hr11]
    have hid : a * (1 - a) + (a - 2 * a ^ 2) = a * (2 - 3 * a) := by ring
    rw [hid]
    exact mul_pos ha0 (by linarith only [ha])
  have hr16 : r 16 = 1 - 2 * a + 3 * a ^ 2 := by
    have h := eq_one_sub_of_pos (step 16 (by decide)) (hr 16) hb16
    rw [h, hr13, hr11]; ring
  have hb17 : 0 < a * r 14 + r 12 := by
    have hid : 16 * (a * r 14 + r 12) =
        625 * v ^ 4 + 2250 * u * v ^ 3 + 3200 * u ^ 2 * v ^ 2 +
          2030 * u ^ 3 * v + 519 * u ^ 4 := by
      rw [hr14, hr12, hu_eq, hv_eq]; ring
    linarith only [show 0 < 16 * (a * r 14 + r 12) by rw [hid]; positivity]
  have hr17 : r 17 = a - 2 * a ^ 2 + 3 * a ^ 3 - 4 * a ^ 4 := by
    have h := eq_one_sub_of_pos (step 17 (by decide)) (hr 17) hb17
    rw [h, hr14, hr12]; ring
  have hb18 : 0 < a * r 15 + r 13 := by
    have hid : 64 * (a * r 15 + r 13) =
        15625 * v ^ 6 + 93750 * u * v ^ 5 + 231875 * u ^ 2 * v ^ 4 +
          303500 * u ^ 3 * v ^ 3 + 221975 * u ^ 4 * v ^ 2 +
          86110 * u ^ 5 * v + 13821 * u ^ 6 := by
      rw [hr15, hr13, hu_eq, hv_eq]; ring
    linarith only [show 0 < 64 * (a * r 15 + r 13) by rw [hid]; positivity]
  have hr18 : r 18 = a ^ 2 - a ^ 3 + a ^ 4 - a ^ 5 + a ^ 6 := by
    have h := eq_one_sub_of_pos (step 18 (by decide)) (hr 18) hb18
    rw [h, hr15, hr13]; ring
  have hb19 : 0 < a * r 16 + r 14 := by
    have hpos : 0 < 2 - 4 * a + 6 * a ^ 2 := by
      have hid : 2 * (2 - 4 * a + 6 * a ^ 2) = 25 * v ^ 2 + 30 * u * v + 17 * u ^ 2 := by
        rw [hu_eq, hv_eq]; ring
      linarith only [show 0 < 2 * (2 - 4 * a + 6 * a ^ 2) by rw [hid]; positivity]
    have hid' : a * r 16 + r 14 = a * (2 - 4 * a + 6 * a ^ 2) := by
      rw [hr16, hr14]; ring
    rw [hid']
    exact mul_pos ha0 hpos
  have hr19 : r 19 = 1 - 2 * a + 4 * a ^ 2 - 6 * a ^ 3 := by
    have h := eq_one_sub_of_pos (step 19 (by decide)) (hr 19) hb19
    rw [h, hr16, hr14]; ring
  have hb20 : 0 < a * r 17 + r 15 := by
    have hid : 32 * (a * r 17 + r 15) =
        3125 * v ^ 5 + 14375 * u * v ^ 4 + 27250 * u ^ 2 * v ^ 3 +
          26150 * u ^ 3 * v ^ 2 + 12745 * u ^ 4 * v + 2435 * u ^ 5 := by
      rw [hr17, hr15, hu_eq, hv_eq]; ring
    linarith only [show 0 < 32 * (a * r 17 + r 15) by rw [hid]; positivity]
  have hr20 : r 20 = a - 2 * a ^ 2 + 3 * a ^ 3 - 4 * a ^ 4 + 5 * a ^ 5 := by
    have h := eq_one_sub_of_pos (step 20 (by decide)) (hr 20) hb20
    rw [h, hr17, hr15]; ring
  have hb22 : 0 < a * r 19 + r 17 := by
    have hpos : 0 < 2 - 4 * a + 7 * a ^ 2 - 10 * a ^ 3 := by
      have hid : 4 * (2 - 4 * a + 7 * a ^ 2 - 10 * a ^ 3) =
          125 * v ^ 3 + 275 * u * v ^ 2 + 245 * u ^ 2 * v + 55 * u ^ 3 := by
        rw [hu_eq, hv_eq]; ring
      linarith only [show 0 < 4 * (2 - 4 * a + 7 * a ^ 2 - 10 * a ^ 3) by rw [hid]; positivity]
    have hid' : a * r 19 + r 17 = a * (2 - 4 * a + 7 * a ^ 2 - 10 * a ^ 3) := by
      rw [hr19, hr17]; ring
    rw [hid']
    exact mul_pos ha0 hpos
  have hr22 : r 22 = 1 - 2 * a + 4 * a ^ 2 - 7 * a ^ 3 + 10 * a ^ 4 := by
    have h := eq_one_sub_of_pos (step 22 (by decide)) (hr 22) hb22
    rw [h, hr19, hr17]; ring
  have hb23 : 0 < a * r 20 + r 18 := by
    have hpos : 0 < 2 - 3 * a + 4 * a ^ 2 - 5 * a ^ 3 + 6 * a ^ 4 := by
      have hid : 8 * (2 - 3 * a + 4 * a ^ 2 - 5 * a ^ 3 + 6 * a ^ 4) =
          625 * v ^ 4 + 2125 * u * v ^ 3 + 2825 * u ^ 2 * v ^ 2 +
            1675 * u ^ 3 * v + 398 * u ^ 4 := by
        rw [hu_eq, hv_eq]; ring
      linarith only [show 0 < 8 * (2 - 3 * a + 4 * a ^ 2 - 5 * a ^ 3 + 6 * a ^ 4) by
        rw [hid]; positivity]
    have hid' : a * r 20 + r 18 =
        a ^ 2 * (2 - 3 * a + 4 * a ^ 2 - 5 * a ^ 3 + 6 * a ^ 4) := by
      rw [hr20, hr18]; ring
    rw [hid']
    exact mul_pos (sq_pos_of_pos ha0) hpos
  have hr23 : r 23 = 1 - 2 * a ^ 2 + 3 * a ^ 3 - 4 * a ^ 4 + 5 * a ^ 5 - 6 * a ^ 6 := by
    have h := eq_one_sub_of_pos (step 23 (by decide)) (hr 23) hb23
    rw [h, hr20, hr18]; ring
  have hb25 : 0 < a * r 22 + r 20 := by
    have hpos : 0 < 2 - 4 * a + 7 * a ^ 2 - 11 * a ^ 3 + 15 * a ^ 4 := by
      have hid : 8 * (2 - 4 * a + 7 * a ^ 2 - 11 * a ^ 3 + 15 * a ^ 4) =
          625 * v ^ 4 + 2000 * u * v ^ 3 + 2600 * u ^ 2 * v ^ 2 +
            1480 * u ^ 3 * v + 375 * u ^ 4 := by
        rw [hu_eq, hv_eq]; ring
      linarith only [show 0 < 8 * (2 - 4 * a + 7 * a ^ 2 - 11 * a ^ 3 + 15 * a ^ 4) by
        rw [hid]; positivity]
    have hid' : a * r 22 + r 20 =
        a * (2 - 4 * a + 7 * a ^ 2 - 11 * a ^ 3 + 15 * a ^ 4) := by
      rw [hr22, hr20]; ring
    rw [hid']
    exact mul_pos ha0 hpos
  have hr25 : r 25 = 1 - 2 * a + 4 * a ^ 2 - 7 * a ^ 3 + 11 * a ^ 4 - 15 * a ^ 5 := by
    have h := eq_one_sub_of_pos (step 25 (by decide)) (hr 25) hb25
    rw [h, hr22, hr20]; ring
  have h28 := step 28 (by decide)
  have hpos28 : 0 < 1 - 4 * a + 7 * a ^ 2 - 11 * a ^ 3 + 16 * a ^ 4 - 21 * a ^ 5 := by
    have hid28 : 32 * (1 - 4 * a + 7 * a ^ 2 - 11 * a ^ 3 + 16 * a ^ 4 - 21 * a ^ 5) =
        3125 * v ^ 5 + 10625 * u * v ^ 4 + 14750 * u ^ 2 * v ^ 3 +
          9550 * u ^ 3 * v ^ 2 + 3005 * u ^ 4 * v + 33 * u ^ 5 := by
      rw [hu_eq, hv_eq]; ring
    linarith only [show 0 < 32 * (1 - 4 * a + 7 * a ^ 2 - 11 * a ^ 3 + 16 * a ^ 4 - 21 * a ^ 5) by
      rw [hid28]; positivity]
  have hdiff28 : a * r 25 + r 23 - 1 =
      a * (1 - 4 * a + 7 * a ^ 2 - 11 * a ^ 3 + 16 * a ^ 4 - 21 * a ^ 5) := by
    rw [hr25, hr23]; ring
  have hgt28 : 1 < a * r 25 + r 23 := by
    have hm := mul_pos ha0 hpos28
    linarith only [hdiff28, hm]
  exact absurd_of_gt_one h28 (hr 28) hgt28

private theorem second_binary_deg5 {P Q : ℝ[X]} (mp : P.Monic) (mq : Q.Monic)
    (hp : ∀ i, 0 ≤ P.coeff i) (hq : ∀ i, 0 ≤ Q.coeff i)
    (p0 : P.coeff 0 = 1) (q0 : Q.coeff 0 = 1) (d5 : P.natDegree = 5)
    (hb : ∀ i, (P * Q).coeff i = 0 ∨ (P * Q).coeff i = 1)
    (first : P.coeff 1 = 0 ∨ P.coeff 1 = 1)
    (fourth : P.coeff 4 = 0 ∨ P.coeff 4 = 1) :
    P.coeff 2 = 0 ∨ P.coeff 2 = 1 := by
  by_cases ha0 : P.coeff 2 = 0
  · exact Or.inl ha0
  by_cases ha1 : P.coeff 2 = 1
  · exact Or.inr ha1
  exfalso
  set a : ℝ := P.coeff 2
  have ha_pos : 0 < a := lt_of_le_of_ne (hp 2) (Ne.symm ha0)
  have ha_lt : a < 1 :=
    lt_of_le_of_ne (GreenFactorBounds.factor_coeff_upper P Q hp hq mq hb 2) ha1
  have hp1q1 : P.coeff 1 * Q.coeff 1 = 0 := by
    rcases first with h1 | h1
    · rw [h1, zero_mul]
    · rw [h1, one_mul]
      have hc1 := conv_one P Q p0 q0
      have hu1 : (P * Q).coeff 1 ≤ 1 := by rcases hb 1 with h | h <;> linarith
      linarith [hq 1]
  have hq2 : Q.coeff 2 = 1 - a := by
    have hc2 := conv_two P Q p0 q0
    rw [hp1q1, add_zero] at hc2
    have hc2b := hb 2
    rw [hc2, add_comm a (Q.coeff 2)] at hc2b
    have h := eq_one_sub_of_pos hc2b (hq 2) ha_pos
    linarith
  have hq2_pos : 0 < Q.coeff 2 := by rw [hq2]; linarith
  have m32 := saturated_deg5 mp q0 hp hq hb d5 3 2 (by decide) (by decide)
  have m23 := saturated_deg5 mp q0 hp hq hb d5 2 3 (by decide) (by decide)
  have hp3 : P.coeff 3 = 0 := (mul_eq_zero.mp m32).resolve_right hq2_pos.ne'
  have hq3 : Q.coeff 3 = 0 := (mul_eq_zero.mp m23).resolve_left ha_pos.ne'
  have h4eq := conv_four P Q p0 q0
  rw [hp3, hq3, zero_mul, mul_zero, add_zero, add_zero] at h4eq
  have haq2_pos : 0 < a * Q.coeff 2 := mul_pos ha_pos hq2_pos
  have hp4 : P.coeff 4 = 0 := by
    rcases fourth with h | h
    · exact h
    · exfalso
      have hb4 := hb 4
      rw [h4eq, h] at hb4
      rcases hb4 with z | z <;> linarith [hq 4]
  have hq4_pos : 0 < Q.coeff 4 := by
    have hb4 := hb 4
    rw [h4eq, hp4, zero_add] at hb4
    have haq2_lt : a * Q.coeff 2 < 1 := by
      have hq2_lt : Q.coeff 2 < 1 := by rw [hq2]; linarith
      exact (mul_le_of_le_one_right ha_pos.le hq2_lt.le).trans_lt ha_lt
    have h4val : a * Q.coeff 2 + Q.coeff 4 = 1 := by
      rcases hb4 with z | z <;> linarith [hq 4]
    linarith
  have m14 := saturated_deg5 mp q0 hp hq hb d5 1 4 (by decide) (by decide)
  have hp1 : P.coeff 1 = 0 := (mul_eq_zero.mp m14).resolve_right hq4_pos.ne'
  have hP_eq : P = 1 + C a * X ^ 2 + X ^ 5 := by
    ext k
    simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
    rcases Nat.lt_trichotomy k 5 with hk | rfl | hk
    · have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl
      · simp [p0]
      · simp [hp1]
      · simp [a]
      · simp [hp3]
      · simp [hp4]
    · have htop : P.coeff 5 = 1 := by simpa only [d5] using mp.coeff_natDegree
      simp [htop]
    · have hzero : P.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < k)
      have hn0 : k ≠ 0 := by omega
      have hn2 : k ≠ 2 := by omega
      have hn5 : k ≠ 5 := by omega
      simp [hzero, hn0, hn2, hn5]
  by_cases ha_le : a ≤ 2 / 5
  · obtain ⟨mqr, hqr, q0r, _⟩ := reverseFacts Q mq hq q0
    have hP_rev : P.reverse = 1 + C a * X ^ 3 + X ^ 5 := by
      have hdeg := (reverseFacts P mp hp p0).2.2.2
      ext k
      simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow]
      rcases Nat.lt_trichotomy k 5 with hk | rfl | hk
      · rw [Polynomial.coeff_reverse, Polynomial.revAt_le (by rw [d5]; omega), d5]
        have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
        rcases hcases with rfl | rfl | rfl | rfl | rfl
        · have htop : P.coeff 5 = 1 := by simpa only [d5] using mp.coeff_natDegree
          simp [htop]
        · simp [hp4]
        · simp [hp3]
        · simp [a]
        · simp [hp1]
      · rw [Polynomial.coeff_reverse, Polynomial.revAt_le (d5 ▸ le_rfl)]
        simp [d5, p0]
      · have hzero : P.reverse.coeff k = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.reverse.natDegree < k)
        have hn0 : k ≠ 0 := by omega
        have hn3 : k ≠ 3 := by omega
        have hn5 : k ≠ 5 := by omega
        simp [hzero, hn0, hn3, hn5]
    have hbrev := reverse_mul_binary hb
    rw [hP_rev] at hbrev
    exact no_rev_le_two_fifths ha_pos ha_le hqr q0r hbrev
  · have ha_gt : 2 / 5 < a := lt_of_not_ge ha_le
    have hbfwd := hb
    rw [hP_eq] at hbfwd
    exact no_fwd_gt_two_fifths ha_gt ha_lt hq q0 hbfwd

theorem deg5_binary {P Q : ℝ[X]} (mp : P.Monic) (mq : Q.Monic)
    (hp : ∀ i, 0 ≤ P.coeff i) (hq : ∀ i, 0 ≤ Q.coeff i)
    (p0 : P.coeff 0 = 1) (q0 : Q.coeff 0 = 1) (d5 : P.natDegree = 5)
    (hb : ∀ i, (P * Q).coeff i = 0 ∨ (P * Q).coeff i = 1) :
    ∀ i, P.coeff i = 0 ∨ P.coeff i = 1 := by
  have first := first_binary_deg5 mp mq hp hq p0 q0 d5 hb
  obtain ⟨mpr, hpr, p0r, pdeg⟩ := reverseFacts P mp hp p0
  obtain ⟨mqr, hqr, q0r, _⟩ := reverseFacts Q mq hq q0
  have d5r : P.reverse.natDegree = 5 := pdeg.trans d5
  have hbr := reverse_mul_binary hb
  have fourth_rev := first_binary_deg5 mpr mqr hpr hqr p0r q0r d5r hbr
  have fourth : P.coeff 4 = 0 ∨ P.coeff 4 = 1 := by
    rwa [Polynomial.coeff_reverse, Polynomial.revAt_le (by rw [d5]; omega), d5] at fourth_rev
  have first_rev : P.reverse.coeff 1 = 0 ∨ P.reverse.coeff 1 = 1 := by
    rw [Polynomial.coeff_reverse, Polynomial.revAt_le (by rw [d5]; omega), d5]
    exact fourth
  have fourth_rev' : P.reverse.coeff 4 = 0 ∨ P.reverse.coeff 4 = 1 := by
    rw [Polynomial.coeff_reverse, Polynomial.revAt_le (by rw [d5]; omega), d5]
    exact first
  have second := second_binary_deg5 mp mq hp hq p0 q0 d5 hb first fourth
  have third_rev := second_binary_deg5 mpr mqr hpr hqr p0r q0r d5r hbr first_rev fourth_rev'
  have third : P.coeff 3 = 0 ∨ P.coeff 3 = 1 := by
    rwa [Polynomial.coeff_reverse, Polynomial.revAt_le (by rw [d5]; omega), d5] at third_rev
  intro i
  by_cases hi : P.natDegree < i
  · exact Or.inl (Polynomial.coeff_eq_zero_of_natDegree_lt hi)
  · have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = P.natDegree := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr p0
    · exact first
    · exact second
    · exact third
    · exact fourth
    · exact Or.inr mp.coeff_natDegree

end OMA.Green28Deg5

theorem OMA.solution : OMA.R_Green28_green_28_R2.H1 := by
  intro P Q mp mq hp hq p0 q0 d5 _ _ hb
  exact OMA.Green28Deg5.deg5_binary mp mq hp hq p0 q0 d5 hb
