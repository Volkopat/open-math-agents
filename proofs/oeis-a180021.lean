import OMAStatements.S_oeis_a180021
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace A180021Proof

open OMA.S_oeis_a180021

lemma neg_log_one_sub_ge {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t + t ^ 2 / 2 + t ^ 3 / 3 ≤ -Real.log (1 - t) := by
  let h : ℝ → ℝ := fun x => -Real.log (1 - x) - x - x ^ 2 / 2 - x ^ 3 / 3
  have hderiv : ∀ x ∈ Set.Ico (0 : ℝ) 1, HasDerivAt h (x ^ 3 / (1 - x)) x := by
    intro x hx
    have h1x : 1 - x ≠ 0 := by linarith [hx.2]
    have hd1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    have hdlog : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - x)) x :=
      hd1.log h1x
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) ((2 : ℝ) * x ^ (2 - 1) / 2) x :=
      (hasDerivAt_pow 2 x).div_const 2
    have h3 : HasDerivAt (fun x : ℝ => x ^ 3 / 3) ((3 : ℝ) * x ^ (3 - 1) / 3) x :=
      (hasDerivAt_pow 3 x).div_const 3
    have hd_all : HasDerivAt h
        (-(-1 / (1 - x)) - 1 - (2 : ℝ) * x ^ (2 - 1) / 2 - (3 : ℝ) * x ^ (3 - 1) / 3) x :=
      ((hdlog.neg.sub (hasDerivAt_id x)).sub h2).sub h3
    convert hd_all using 1
    field_simp
    ring
  have hmono : MonotoneOn h (Set.Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Set.Ico (0 : ℝ) 1 := interior_subset hx
      rw [(hderiv x hx').deriv]
      have hpos : 0 < 1 - x := by linarith [hx'.2]
      have hx0 : 0 ≤ x := hx'.1
      positivity
  have h0 : h 0 ≤ h t := hmono ⟨le_refl 0, by norm_num⟩ ⟨ht0, ht1⟩ ht0
  have hz : h 0 = 0 := by simp [h]
  dsimp only [h] at h0 hz
  linarith

lemma neg_log_one_sub_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    -Real.log (1 - t) ≤ t + t ^ 2 / 2 + t ^ 3 / (3 * (1 - t)) := by
  let f : ℝ → ℝ := fun x => x + x ^ 2 / 2 + x ^ 3 / (3 * (1 - x)) + Real.log (1 - x)
  have hderiv : ∀ x ∈ Set.Ico (0 : ℝ) 1, HasDerivAt f (x ^ 3 / (3 * (1 - x) ^ 2)) x := by
    intro x hx
    have h1x : 1 - x ≠ 0 := by linarith [hx.2]
    have h3x : 3 * (1 - x) ≠ 0 := by positivity
    have hd1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    have hdlog : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - x)) x :=
      hd1.log h1x
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) ((2 : ℝ) * x ^ (2 - 1) / 2) x :=
      (hasDerivAt_pow 2 x).div_const 2
    have hden : HasDerivAt (fun x : ℝ => 3 * (1 - x)) (3 * (-1)) x :=
      hd1.const_mul 3
    have h3 : HasDerivAt (fun x : ℝ => x ^ 3 / (3 * (1 - x)))
        (((3 : ℝ) * x ^ (3 - 1) * (3 * (1 - x)) - x ^ 3 * (3 * (-1))) / (3 * (1 - x)) ^ 2) x :=
      (hasDerivAt_pow 3 x).div hden h3x
    have hd_all : HasDerivAt f
        (1 + (2 : ℝ) * x ^ (2 - 1) / 2 +
          (((3 : ℝ) * x ^ (3 - 1) * (3 * (1 - x)) - x ^ 3 * (3 * (-1))) / (3 * (1 - x)) ^ 2) +
          (-1 / (1 - x))) x :=
      (((hasDerivAt_id x).add h2).add h3).add hdlog
    convert hd_all using 1
    field_simp
    ring
  have hmono : MonotoneOn f (Set.Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Set.Ico (0 : ℝ) 1 := interior_subset hx
      rw [(hderiv x hx').deriv]
      have hx0 : 0 ≤ x := hx'.1
      positivity
  have h0 : f 0 ≤ f t := hmono ⟨le_refl 0, by norm_num⟩ ⟨ht0, ht1⟩ ht0
  have hz : f 0 = 0 := by simp [f]
  dsimp only [f] at h0 hz
  linarith

lemma log_two_decomp :
    Real.log 2 = -Real.log (1 - (1 : ℝ) / 5) + (-Real.log (1 - (1 : ℝ) / 6)) +
      (-Real.log (1 - (1 : ℝ) / 4)) := by
  have hprod : (1 - (1 : ℝ) / 5) * (1 - (1 : ℝ) / 6) * (1 - (1 : ℝ) / 4) = (2 : ℝ)⁻¹ := by
    norm_num
  have h1 : Real.log ((1 - (1 : ℝ) / 5) * (1 - (1 : ℝ) / 6) * (1 - (1 : ℝ) / 4)) =
      Real.log (1 - (1 : ℝ) / 5) + Real.log (1 - (1 : ℝ) / 6) + Real.log (1 - (1 : ℝ) / 4) := by
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  rw [hprod, Real.log_inv] at h1
  linarith

lemma log_two_gt : (6912 : ℝ) / 10000 < Real.log 2 := by
  have h1 := neg_log_one_sub_ge (t := (1 : ℝ) / 5) (by norm_num) (by norm_num)
  have h2 := neg_log_one_sub_ge (t := (1 : ℝ) / 6) (by norm_num) (by norm_num)
  have h3 := neg_log_one_sub_ge (t := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  rw [log_two_decomp]
  linarith

lemma log_two_lt : Real.log 2 < (6940 : ℝ) / 10000 := by
  have h1 := neg_log_one_sub_le (t := (1 : ℝ) / 5) (by norm_num) (by norm_num)
  have h2 := neg_log_one_sub_le (t := (1 : ℝ) / 6) (by norm_num) (by norm_num)
  have h3 := neg_log_one_sub_le (t := (1 : ℝ) / 4) (by norm_num) (by norm_num)
  rw [log_two_decomp]
  linarith

lemma sum_range_id_real (n : ℕ) :
    ∑ j ∈ Finset.range n, (j : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma sum_range_sq_real (n : ℕ) :
    ∑ j ∈ Finset.range n, (j : ℝ) ^ 2 = (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma sum_range_cube_real (n : ℕ) :
    ∑ j ∈ Finset.range n, (j : ℝ) ^ 3 = ((n : ℝ) * ((n : ℝ) - 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma descFactorial_cast_eq_prod {d n : ℕ} (hnd : n ≤ d) :
    (d.descFactorial n : ℝ) = ∏ j ∈ Finset.range n, ((d : ℝ) - (j : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.descFactorial_succ, Finset.prod_range_succ, Nat.cast_mul, ih (by omega), mul_comm]
    congr 1
    rw [Nat.cast_sub (by omega)]

lemma neg_sum_log_eq {d n : ℕ} (hn : 0 < d) (hnd : n ≤ d) :
    -∑ j ∈ Finset.range n, Real.log (1 - (j : ℝ) / (d : ℝ)) =
      Real.log ((d : ℝ) ^ n) - Real.log (d.descFactorial n : ℝ) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hn
  have hne : ∀ j ∈ Finset.range n, 1 - (j : ℝ) / (d : ℝ) ≠ 0 := by
    intro j hj
    have hjlt : j < n := Finset.mem_range.mp hj
    have hjd : (j : ℝ) < (d : ℝ) := by exact_mod_cast (show j < d by omega)
    have hlt1 : (j : ℝ) / (d : ℝ) < 1 := (div_lt_one hd_pos).mpr hjd
    linarith
  rw [← Real.log_prod hne]
  have hprod : ∏ j ∈ Finset.range n, (1 - (j : ℝ) / (d : ℝ)) =
      (d.descFactorial n : ℝ) / (d : ℝ) ^ n := by
    rw [descFactorial_cast_eq_prod hnd]
    have hpow : (d : ℝ) ^ n = ∏ _j ∈ Finset.range n, (d : ℝ) := by simp
    rw [hpow, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl ?_
    intro j _
    field_simp
  have hdf_pos : (0 : ℝ) < (d.descFactorial n : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hnd
  rw [hprod, Real.log_div (ne_of_gt hdf_pos) (ne_of_gt (pow_pos hd_pos n))]
  ring

lemma sum_neg_log_ge {n : ℕ} {d : ℝ} (hd_pos : 0 < d) (hnd : (n : ℝ) ≤ d) :
    (n : ℝ) * ((n : ℝ) - 1) / (2 * d) +
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / (12 * d ^ 2) +
      ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 / (12 * d ^ 3) ≤
      -∑ j ∈ Finset.range n, Real.log (1 - (j : ℝ) / d) := by
  rw [← Finset.sum_neg_distrib]
  have hstep : ∑ j ∈ Finset.range n,
      ((j : ℝ) / d + ((j : ℝ) / d) ^ 2 / 2 + ((j : ℝ) / d) ^ 3 / 3) ≤
      ∑ j ∈ Finset.range n, -Real.log (1 - (j : ℝ) / d) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hjlt : j < n := Finset.mem_range.mp hj
    have hjd : (j : ℝ) < d := lt_of_lt_of_le (by exact_mod_cast hjlt) hnd
    exact neg_log_one_sub_ge (div_nonneg (Nat.cast_nonneg j) (le_of_lt hd_pos))
      ((div_lt_one hd_pos).mpr hjd)
  refine le_trans (le_of_eq ?_) hstep
  simp only [Finset.sum_add_distrib, div_eq_mul_inv, mul_pow, ← Finset.sum_mul]
  rw [sum_range_id_real, sum_range_sq_real, sum_range_cube_real]
  field_simp
  ring

lemma sum_neg_log_le {n : ℕ} {d : ℝ} (hnd : (n : ℝ) < d) :
    -∑ j ∈ Finset.range n, Real.log (1 - (j : ℝ) / d) ≤
      (n : ℝ) * ((n : ℝ) - 1) / (2 * d) +
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / (12 * d ^ 2) +
      ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 / (12 * d ^ 2 * (d - (n : ℝ))) := by
  have hd_pos : 0 < d := lt_of_le_of_lt (Nat.cast_nonneg n) hnd
  have hdn : 0 < d - (n : ℝ) := by linarith
  rw [← Finset.sum_neg_distrib]
  have hstep : ∑ j ∈ Finset.range n, -Real.log (1 - (j : ℝ) / d) ≤
      ∑ j ∈ Finset.range n,
        ((j : ℝ) / d + ((j : ℝ) / d) ^ 2 / 2 + (j : ℝ) ^ 3 / (3 * d ^ 2 * (d - (n : ℝ)))) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hjlt : j < n := Finset.mem_range.mp hj
    have hjn : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hjlt
    have hjd : (j : ℝ) < d := lt_of_le_of_lt hjn hnd
    have h1 := neg_log_one_sub_le (div_nonneg (Nat.cast_nonneg j) (le_of_lt hd_pos))
      ((div_lt_one hd_pos).mpr hjd)
    refine le_trans h1 ?_
    have h3 : ((j : ℝ) / d) ^ 3 / (3 * (1 - (j : ℝ) / d)) ≤
        (j : ℝ) ^ 3 / (3 * d ^ 2 * (d - (n : ℝ))) := by
      have heq : ((j : ℝ) / d) ^ 3 / (3 * (1 - (j : ℝ) / d)) =
          (j : ℝ) ^ 3 / (3 * d ^ 2 * (d - (j : ℝ))) := by
        have hdj : d - (j : ℝ) ≠ 0 := by linarith
        have h1j : 1 - (j : ℝ) / d ≠ 0 := by
          have : (j : ℝ) / d < 1 := (div_lt_one hd_pos).mpr hjd
          linarith
        field_simp
      rw [heq]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      have : d - (n : ℝ) ≤ d - (j : ℝ) := by linarith
      nlinarith
    linarith
  refine le_trans hstep (le_of_eq ?_)
  simp only [Finset.sum_add_distrib, div_eq_mul_inv, mul_pow, ← Finset.sum_mul]
  rw [sum_range_id_real, sum_range_sq_real, sum_range_cube_real]
  field_simp
  ring

noncomputable def Q (n : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) - 1) / (2 * Real.log 2) + (n : ℝ) / 3

lemma Q_sub_gt_n {n : ℕ} (hn : 4 ≤ n) : (n : ℝ) < Q n - 1 / 5 := by
  unfold Q
  have hL1 := log_two_gt
  have hL2 := log_two_lt
  have hLpos : 0 < Real.log 2 := by linarith
  have hn' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (n : ℝ) * ((n : ℝ) - 1) / (7 / 5 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) / (2 * Real.log 2) := by
    apply div_lt_div_of_pos_left (by nlinarith) (by positivity) (by linarith)
  have hquad : (n : ℝ) < (n : ℝ) * ((n : ℝ) - 1) / (7 / 5 : ℝ) + (n : ℝ) / 3 - 1 / 5 := by
    nlinarith
  linarith

lemma descFactorial_lt_of_le_Q_sub {n d : ℕ} (hn : 4 ≤ n) (hnd : n ≤ d)
    (hd : (d : ℝ) ≤ Q n - 1 / 5) : 2 * d.descFactorial n < d ^ n := by
  set L := Real.log 2
  have hL1 : (6912 : ℝ) / 10000 < L := log_two_gt
  have hL2 : L < (6940 : ℝ) / 10000 := log_two_lt
  have hLpos : 0 < L := by linarith
  have hn' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd_pos_nat : 0 < d := by omega
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos_nat
  have hnd' : (n : ℝ) ≤ (d : ℝ) := by exact_mod_cast hnd
  set dm := Q n - 1 / 5
  have hdm_pos : 0 < dm := lt_of_lt_of_le hd_pos hd
  have h1 : (n : ℝ) * ((n : ℝ) - 1) / (2 * dm) ≤ (n : ℝ) * ((n : ℝ) - 1) / (2 * (d : ℝ)) := by
    apply div_le_div_of_nonneg_left (by nlinarith) (by positivity) (by linarith)
  have h2 : (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / (12 * dm ^ 2) ≤
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / (12 * (d : ℝ) ^ 2) := by
    apply div_le_div_of_nonneg_left (mul_nonneg (by nlinarith) (by linarith)) (by positivity) (by nlinarith)
  have h3 : ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 / (12 * dm ^ 3) ≤
      ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 / (12 * (d : ℝ) ^ 3) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have hpow : (d : ℝ) ^ 3 ≤ dm ^ 3 := pow_le_pow_left₀ (le_of_lt hd_pos) hd 3
    linarith
  have hpoly : L < (n : ℝ) * ((n : ℝ) - 1) / (2 * dm) +
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / (12 * dm ^ 2) +
      ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 / (12 * dm ^ 3) := by
    have hmul : 0 < 12 * dm ^ 3 := by positivity
    rw [← sub_pos]
    have hrew : (n : ℝ) * ((n : ℝ) - 1) / (2 * dm) +
        (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / (12 * dm ^ 2) +
        ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 / (12 * dm ^ 3) - L =
        (6 * (n : ℝ) * ((n : ℝ) - 1) * dm ^ 2 +
          (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * dm +
          ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 - 12 * L * dm ^ 3) / (12 * dm ^ 3) := by
      field_simp
      ring
    rw [hrew]
    apply div_pos _ hmul
    let m : ℝ := (n : ℝ) - 4
    have hm : 0 ≤ m := by linarith
    have hnum : (30 * L) ^ 3 * (6 * (n : ℝ) * ((n : ℝ) - 1) * dm ^ 2 +
        (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * dm +
        ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 - 12 * L * dm ^ 3) =
        L ^ 2 * ((2700 + 9000 * L) * m ^ 4 +
          (37800 + 131400 * L - 12000 * L ^ 2) * m ^ 3 +
          (197100 + 708840 * L - 122400 * L ^ 2) * m ^ 2 +
          (453600 + 1675080 * L - 416160 * L ^ 2) * m +
          (388800 + 1464480 * L - 471648 * L ^ 2)) := by
      have hdm_def : 30 * L * dm = 15 * (n : ℝ) * ((n : ℝ) - 1) + 10 * L * (n : ℝ) - 6 * L := by
        simp only [dm, Q]
        field_simp
        ring
      have hn_eq : (n : ℝ) = m + 4 := by simp [m]
      calc (30 * L) ^ 3 * (6 * (n : ℝ) * ((n : ℝ) - 1) * dm ^ 2 +
              (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * dm +
              ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 - 12 * L * dm ^ 3)
          = 6 * (30 * L) * (n : ℝ) * ((n : ℝ) - 1) * (30 * L * dm) ^ 2 +
            (30 * L) ^ 2 * (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * (30 * L * dm) +
            (30 * L) ^ 3 * ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 - 12 * L * (30 * L * dm) ^ 3 := by ring
        _ = 6 * (30 * L) * (m + 4) * ((m + 4) - 1) *
              (15 * (m + 4) * ((m + 4) - 1) + 10 * L * (m + 4) - 6 * L) ^ 2 +
            (30 * L) ^ 2 * (m + 4) * ((m + 4) - 1) * (2 * (m + 4) - 1) *
              (15 * (m + 4) * ((m + 4) - 1) + 10 * L * (m + 4) - 6 * L) +
            (30 * L) ^ 3 * ((m + 4) * ((m + 4) - 1)) ^ 2 -
            12 * L * (15 * (m + 4) * ((m + 4) - 1) + 10 * L * (m + 4) - 6 * L) ^ 3 := by
              rw [hdm_def, hn_eq]
        _ = L ^ 2 * ((2700 + 9000 * L) * m ^ 4 +
              (37800 + 131400 * L - 12000 * L ^ 2) * m ^ 3 +
              (197100 + 708840 * L - 122400 * L ^ 2) * m ^ 2 +
              (453600 + 1675080 * L - 416160 * L ^ 2) * m +
              (388800 + 1464480 * L - 471648 * L ^ 2)) := by ring
    have hc4 : 0 < 2700 + 9000 * L := by nlinarith only [hL1, hL2]
    have hc3 : 0 < 37800 + 131400 * L - 12000 * L ^ 2 := by nlinarith only [hL1, hL2]
    have hc2 : 0 < 197100 + 708840 * L - 122400 * L ^ 2 := by nlinarith only [hL1, hL2]
    have hc1 : 0 < 453600 + 1675080 * L - 416160 * L ^ 2 := by nlinarith only [hL1, hL2]
    have hc0 : 0 < 388800 + 1464480 * L - 471648 * L ^ 2 := by nlinarith only [hL1, hL2]
    have hrhs_pos : 0 < L ^ 2 * ((2700 + 9000 * L) * m ^ 4 +
        (37800 + 131400 * L - 12000 * L ^ 2) * m ^ 3 +
        (197100 + 708840 * L - 122400 * L ^ 2) * m ^ 2 +
        (453600 + 1675080 * L - 416160 * L ^ 2) * m +
        (388800 + 1464480 * L - 471648 * L ^ 2)) := by positivity
    have h30_nonneg : 0 ≤ (30 * L) ^ 3 := by positivity
    exact pos_of_mul_pos_right (hnum.symm ▸ hrhs_pos) h30_nonneg
  have hlog_lt : Real.log 2 < Real.log ((d : ℝ) ^ n) - Real.log (d.descFactorial n : ℝ) := by
    rw [← neg_sum_log_eq hd_pos_nat hnd]
    have hsum := sum_neg_log_ge hd_pos hnd'
    linarith
  have hdf_pos : (0 : ℝ) < (d.descFactorial n : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hnd
  have hlog2 : Real.log (2 * (d.descFactorial n : ℝ)) < Real.log ((d : ℝ) ^ n) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hdf_pos)]
    linarith
  have hreal : 2 * (d.descFactorial n : ℝ) < (d : ℝ) ^ n :=
    (Real.log_lt_log_iff (by positivity) (pow_pos hd_pos n)).mp hlog2
  exact_mod_cast hreal

lemma descFactorial_ge_of_ge_Q {n d : ℕ} (hn : 4 ≤ n) (hd : Q n ≤ (d : ℝ)) :
    d ^ n ≤ 2 * d.descFactorial n := by
  set L := Real.log 2
  have hL1 : (6912 : ℝ) / 10000 < L := log_two_gt
  have hL2 : L < (6940 : ℝ) / 10000 := log_two_lt
  have hLpos : 0 < L := by linarith
  have hn' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set dp := Q n
  have hndp : (n : ℝ) < dp := lt_trans (Q_sub_gt_n hn) (by linarith)
  have hdn_pos : 0 < dp - (n : ℝ) := by linarith
  have hnd_real : (n : ℝ) < (d : ℝ) := lt_of_lt_of_le hndp hd
  have hnd : n ≤ d := by exact_mod_cast le_of_lt hnd_real
  have hd_pos_nat : 0 < d := by omega
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos_nat
  have hdp_pos : 0 < dp := lt_of_le_of_lt (Nat.cast_nonneg n) hndp
  have h1 : (n : ℝ) * ((n : ℝ) - 1) / (2 * (d : ℝ)) ≤ (n : ℝ) * ((n : ℝ) - 1) / (2 * dp) := by
    apply div_le_div_of_nonneg_left (by nlinarith) (by positivity) (by linarith)
  have h2 : (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / (12 * (d : ℝ) ^ 2) ≤
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / (12 * dp ^ 2) := by
    apply div_le_div_of_nonneg_left (mul_nonneg (by nlinarith) (by linarith)) (by positivity) (by nlinarith)
  have h3 : ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 / (12 * (d : ℝ) ^ 2 * ((d : ℝ) - (n : ℝ))) ≤
      ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 / (12 * dp ^ 2 * (dp - (n : ℝ))) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have hdn2 : dp - (n : ℝ) ≤ (d : ℝ) - (n : ℝ) := by linarith
    have hsq : dp ^ 2 ≤ (d : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hpoly : (n : ℝ) * ((n : ℝ) - 1) / (2 * dp) +
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / (12 * dp ^ 2) +
      ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 / (12 * dp ^ 2 * (dp - (n : ℝ))) < L := by
    have hmul : 0 < 12 * dp ^ 2 * (dp - (n : ℝ)) := by positivity
    rw [← sub_pos]
    have hrew : L - ((n : ℝ) * ((n : ℝ) - 1) / (2 * dp) +
        (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / (12 * dp ^ 2) +
        ((n : ℝ) * ((n : ℝ) - 1)) ^ 2 / (12 * dp ^ 2 * (dp - (n : ℝ)))) =
        (12 * L * dp ^ 2 * (dp - (n : ℝ)) -
          (6 * (n : ℝ) * ((n : ℝ) - 1) * dp * (dp - (n : ℝ)) +
           (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * (dp - (n : ℝ)) +
           ((n : ℝ) * ((n : ℝ) - 1)) ^ 2)) / (12 * dp ^ 2 * (dp - (n : ℝ))) := by
      field_simp
      ring
    rw [hrew]
    apply div_pos _ hmul
    let m : ℝ := (n : ℝ) - 4
    have hm : 0 ≤ m := by linarith
    have hnum : (6 * L) ^ 3 * (12 * L * dp ^ 2 * (dp - (n : ℝ)) -
        (6 * (n : ℝ) * ((n : ℝ) - 1) * dp * (dp - (n : ℝ)) +
         (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * (dp - (n : ℝ)) +
         ((n : ℝ) * ((n : ℝ) - 1)) ^ 2)) =
        L ^ 2 * ((108 - 72 * L) * m ^ 4 +
          (1512 - 1008 * L - 192 * L ^ 2) * m ^ 3 +
          (7884 - 5256 * L - 2304 * L ^ 2) * m ^ 2 +
          (18144 - 12096 * L - 9216 * L ^ 2) * m +
          (15552 - 10368 * L - 12288 * L ^ 2)) := by
      have hdp_def : 6 * L * dp = 3 * (n : ℝ) * ((n : ℝ) - 1) + 2 * L * (n : ℝ) := by
        simp only [dp, Q]
        field_simp
        ring
      have hdpn_def : 6 * L * (dp - (n : ℝ)) = 3 * (n : ℝ) * ((n : ℝ) - 1) - 4 * L * (n : ℝ) := by
        linarith
      have hn_eq : (n : ℝ) = m + 4 := by simp [m]
      calc (6 * L) ^ 3 * (12 * L * dp ^ 2 * (dp - (n : ℝ)) -
              (6 * (n : ℝ) * ((n : ℝ) - 1) * dp * (dp - (n : ℝ)) +
               (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * (dp - (n : ℝ)) +
               ((n : ℝ) * ((n : ℝ) - 1)) ^ 2))
          = 12 * L * (6 * L * dp) ^ 2 * (6 * L * (dp - (n : ℝ))) -
            (6 * (6 * L) * (n : ℝ) * ((n : ℝ) - 1) * (6 * L * dp) * (6 * L * (dp - (n : ℝ))) +
             (6 * L) ^ 2 * (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) * (6 * L * (dp - (n : ℝ))) +
             (6 * L) ^ 3 * ((n : ℝ) * ((n : ℝ) - 1)) ^ 2) := by ring
        _ = 12 * L * (3 * (m + 4) * ((m + 4) - 1) + 2 * L * (m + 4)) ^ 2 *
              (3 * (m + 4) * ((m + 4) - 1) - 4 * L * (m + 4)) -
            (6 * (6 * L) * (m + 4) * ((m + 4) - 1) *
              (3 * (m + 4) * ((m + 4) - 1) + 2 * L * (m + 4)) *
              (3 * (m + 4) * ((m + 4) - 1) - 4 * L * (m + 4)) +
             (6 * L) ^ 2 * (m + 4) * ((m + 4) - 1) * (2 * (m + 4) - 1) *
              (3 * (m + 4) * ((m + 4) - 1) - 4 * L * (m + 4)) +
             (6 * L) ^ 3 * ((m + 4) * ((m + 4) - 1)) ^ 2) := by
              rw [hdp_def, hdpn_def, hn_eq]
        _ = L ^ 2 * ((108 - 72 * L) * m ^ 4 +
              (1512 - 1008 * L - 192 * L ^ 2) * m ^ 3 +
              (7884 - 5256 * L - 2304 * L ^ 2) * m ^ 2 +
              (18144 - 12096 * L - 9216 * L ^ 2) * m +
              (15552 - 10368 * L - 12288 * L ^ 2)) := by ring
    have hc4 : 0 < 108 - 72 * L := by nlinarith only [hL1, hL2]
    have hc3 : 0 < 1512 - 1008 * L - 192 * L ^ 2 := by nlinarith only [hL1, hL2]
    have hc2 : 0 < 7884 - 5256 * L - 2304 * L ^ 2 := by nlinarith only [hL1, hL2]
    have hc1 : 0 < 18144 - 12096 * L - 9216 * L ^ 2 := by nlinarith only [hL1, hL2]
    have hc0 : 0 < 15552 - 10368 * L - 12288 * L ^ 2 := by nlinarith only [hL1, hL2]
    have hrhs_pos : 0 < L ^ 2 * ((108 - 72 * L) * m ^ 4 +
        (1512 - 1008 * L - 192 * L ^ 2) * m ^ 3 +
        (7884 - 5256 * L - 2304 * L ^ 2) * m ^ 2 +
        (18144 - 12096 * L - 9216 * L ^ 2) * m +
        (15552 - 10368 * L - 12288 * L ^ 2)) := by positivity
    have h6_nonneg : 0 ≤ (6 * L) ^ 3 := by positivity
    exact pos_of_mul_pos_right (hnum.symm ▸ hrhs_pos) h6_nonneg
  have hlog_le : Real.log ((d : ℝ) ^ n) - Real.log (d.descFactorial n : ℝ) ≤ Real.log 2 := by
    rw [← neg_sum_log_eq hd_pos_nat hnd]
    have hsum := sum_neg_log_le hnd_real
    linarith
  have hdf_pos : (0 : ℝ) < (d.descFactorial n : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hnd
  have hlog2 : Real.log ((d : ℝ) ^ n) ≤ Real.log (2 * (d.descFactorial n : ℝ)) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hdf_pos)]
    linarith
  have hreal : (d : ℝ) ^ n ≤ 2 * (d.descFactorial n : ℝ) :=
    (Real.log_le_log_iff (pow_pos hd_pos n) (by positivity)).mp hlog2
  exact_mod_cast hreal

lemma birthdayCount_bounds {n : ℕ} (hn : 4 ≤ n) :
    Q n - 1 / 5 - (n : ℝ) < (birthdayCount n : ℝ) ∧
      (birthdayCount n : ℝ) < Q n + 1 - (n : ℝ) := by
  let S : Set ℕ := {d : ℕ | 2 < d ∧ n ≤ d ∧ 2 * d.descFactorial n < d ^ n}
  let lo : ℕ := ⌊Q n - 1 / 5⌋₊
  let hi : ℕ := ⌈Q n⌉₊
  have hQ_pos : 0 ≤ Q n - 1 / 5 := by
    have := Q_sub_gt_n hn
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hn_le_lo : n ≤ lo := Nat.le_floor (le_of_lt (Q_sub_gt_n hn))
  have hn_le_hi : n ≤ hi := le_of_lt (Nat.lt_ceil.mpr (lt_trans (Q_sub_gt_n hn) (by linarith)))
  have hsub1 : Set.Icc n lo ⊆ S := by
    intro d ⟨hd1, hd2⟩
    refine ⟨by omega, hd1, descFactorial_lt_of_le_Q_sub hn hd1 ?_⟩
    exact le_trans (by exact_mod_cast hd2) (Nat.floor_le hQ_pos)
  have hsub2 : S ⊆ Set.Ico n hi := by
    intro d ⟨_, hd2, hd3⟩
    refine ⟨hd2, Nat.lt_ceil.mpr ?_⟩
    by_contra hge
    have hle : Q n ≤ (d : ℝ) := le_of_not_gt hge
    have := descFactorial_ge_of_ge_Q hn hle
    omega
  have hfinB : (Set.Ico n hi).Finite := Set.finite_Ico n hi
  have hfinS : S.Finite := hfinB.subset hsub2
  have hcard1 : (Set.Icc n lo).ncard ≤ S.ncard := Set.ncard_le_ncard hsub1 hfinS
  have hcard2 : S.ncard ≤ (Set.Ico n hi).ncard := Set.ncard_le_ncard hsub2 hfinB
  have hcA : (Set.Icc n lo).ncard = lo + 1 - n := by
    rw [← Finset.coe_Icc, Set.ncard_coe_finset, Nat.card_Icc]
  have hcB : (Set.Ico n hi).ncard = hi - n := by
    rw [← Finset.coe_Ico, Set.ncard_coe_finset, Nat.card_Ico]
  rw [hcA] at hcard1
  rw [hcB] at hcard2
  change Q n - 1 / 5 - (n : ℝ) < (S.ncard : ℝ) ∧ (S.ncard : ℝ) < Q n + 1 - (n : ℝ)
  constructor
  · have h1 : ((lo + 1 - n : ℕ) : ℝ) ≤ (S.ncard : ℝ) := by exact_mod_cast hcard1
    have h2 : ((lo + 1 - n : ℕ) : ℝ) = (lo : ℝ) + 1 - (n : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    have h3 : Q n - 1 / 5 < (lo : ℝ) + 1 := Nat.lt_floor_add_one (Q n - 1 / 5)
    linarith
  · have h1 : (S.ncard : ℝ) ≤ ((hi - n : ℕ) : ℝ) := by exact_mod_cast hcard2
    have h2 : ((hi - n : ℕ) : ℝ) = (hi : ℝ) - (n : ℝ) := by rw [Nat.cast_sub hn_le_hi]
    have h3 : (hi : ℝ) < Q n + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith

lemma birthdayCount_1 : birthdayCount 1 = 0 := by
  unfold birthdayCount
  have hempty : {d : ℕ | 2 < d ∧ 1 ≤ d ∧ 2 * d.descFactorial 1 < d ^ 1} = ∅ := by
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
    intro hd _
    simp only [Nat.descFactorial_one, pow_one]
    omega
  rw [hempty, Set.ncard_empty]

lemma birthdayCount_2 : birthdayCount 2 = 0 := by
  unfold birthdayCount
  have hempty : {d : ℕ | 2 < d ∧ 2 ≤ d ∧ 2 * d.descFactorial 2 < d ^ 2} = ∅ := by
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
    intro hd _
    have hdesc : d.descFactorial 2 = d * (d - 1) := by
      simp [Nat.descFactorial_succ, mul_comm]
    rw [hdesc]
    have : d ^ 2 = d * d := sq d
    rw [this]
    have hd3 : 3 ≤ d := by omega
    obtain ⟨m, rfl⟩ : ∃ m, d = m + 3 := ⟨d - 3, by omega⟩
    have hsub : m + 3 - 1 = m + 2 := by omega
    rw [hsub]
    nlinarith
  rw [hempty, Set.ncard_empty]

lemma birthdayCount_3 : birthdayCount 3 = 3 := by
  unfold birthdayCount
  have heq : {d : ℕ | 2 < d ∧ 3 ≤ d ∧ 2 * d.descFactorial 3 < d ^ 3} =
      (Finset.Icc 3 5 : Set ℕ) := by
    ext d
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_Icc]
    constructor
    · rintro ⟨_, hd3, hlt⟩
      refine ⟨hd3, ?_⟩
      by_contra hgt
      have hd6 : 6 ≤ d := by omega
      obtain ⟨m, rfl⟩ : ∃ m, d = m + 6 := ⟨d - 6, by omega⟩
      have hdesc : (m + 6).descFactorial 3 = (m + 6) * (m + 5) * (m + 4) := by
        simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero]
        have h1 : m + 6 - 1 = m + 5 := by omega
        have h2 : m + 6 - 2 = m + 4 := by omega
        rw [h1, h2]
        ring
      rw [hdesc] at hlt
      nlinarith
    · rintro ⟨hd3, hd5⟩
      refine ⟨by omega, hd3, ?_⟩
      interval_cases d <;> decide
  rw [heq, Set.ncard_coe_finset]
  decide

lemma birthdayCount_4 : birthdayCount 4 = 6 := by
  unfold birthdayCount
  have heq : {d : ℕ | 2 < d ∧ 4 ≤ d ∧ 2 * d.descFactorial 4 < d ^ 4} =
      (Finset.Icc 4 9 : Set ℕ) := by
    ext d
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_Icc]
    constructor
    · rintro ⟨_, hd4, hlt⟩
      refine ⟨hd4, ?_⟩
      by_contra hgt
      have hd10 : 10 ≤ d := by omega
      obtain ⟨m, rfl⟩ : ∃ m, d = m + 10 := ⟨d - 10, by omega⟩
      have hdesc : (m + 10).descFactorial 4 = (m + 10) * (m + 9) * (m + 8) * (m + 7) := by
        simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero]
        have h1 : m + 10 - 1 = m + 9 := by omega
        have h2 : m + 10 - 2 = m + 8 := by omega
        have h3 : m + 10 - 3 = m + 7 := by omega
        rw [h1, h2, h3]
        ring
      rw [hdesc] at hlt
      have hpos : (m + 10) ^ 3 ≤ 2 * ((m + 9) * (m + 8) * (m + 7)) := by
        have hid : 2 * ((m + 9) * (m + 8) * (m + 7)) =
            (m + 10) ^ 3 + (m ^ 3 + 18 * m ^ 2 + 82 * m + 8) := by ring
        omega
      have hmul : (m + 10) * (m + 10) ^ 3 ≤ (m + 10) * (2 * ((m + 9) * (m + 8) * (m + 7))) :=
        Nat.mul_le_mul_left (m + 10) hpos
      have hlhs : (m + 10) ^ 4 = (m + 10) * (m + 10) ^ 3 := by ring
      have hrhs : 2 * ((m + 10) * (m + 9) * (m + 8) * (m + 7)) =
          (m + 10) * (2 * ((m + 9) * (m + 8) * (m + 7))) := by ring
      omega
    · rintro ⟨hd4, hd9⟩
      refine ⟨by omega, hd4, ?_⟩
      interval_cases d <;> decide
  rw [heq, Set.ncard_coe_finset]
  decide

lemma birthdayCount_5 : birthdayCount 5 = 12 := by
  unfold birthdayCount
  have heq : {d : ℕ | 2 < d ∧ 5 ≤ d ∧ 2 * d.descFactorial 5 < d ^ 5} =
      (Finset.Icc 5 16 : Set ℕ) := by
    ext d
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_Icc]
    constructor
    · rintro ⟨_, hd5, hlt⟩
      refine ⟨hd5, ?_⟩
      by_contra hgt
      have hd17 : 17 ≤ d := by omega
      have hQ5 : Q 5 ≤ (d : ℝ) := by
        unfold Q
        have hL1 := log_two_gt
        have hd' : (17 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd17
        have hdiv : (5 : ℝ) * (5 - 1) / (2 * Real.log 2) < 14.5 := by
          rw [div_lt_iff₀ (by linarith)]
          linarith
        norm_num at hdiv ⊢
        linarith
      have := descFactorial_ge_of_ge_Q (by decide) hQ5
      omega
    · rintro ⟨hd5, hd16⟩
      refine ⟨by omega, hd5, ?_⟩
      interval_cases d <;> decide
  rw [heq, Set.ncard_coe_finset]
  decide

lemma secondDifference_bounds (k : ℕ) :
    0 ≤ secondDifference k ∧ secondDifference k ≤ 3 := by
  by_cases hk : k < 3
  · interval_cases k <;>
      simp [secondDifference, birthdayCount_1, birthdayCount_2, birthdayCount_3,
        birthdayCount_4, birthdayCount_5]
  · have hk3 : 3 ≤ k := by omega
    have hb1 := birthdayCount_bounds (n := k + 1) (by omega)
    have hb2 := birthdayCount_bounds (n := k + 2) (by omega)
    have hb3 := birthdayCount_bounds (n := k + 3) (by omega)
    have hL1 := log_two_gt
    have hL2 := log_two_lt
    have hLpos : 0 < Real.log 2 := by linarith
    have hQdiff : Q (k + 3) - 2 * Q (k + 2) + Q (k + 1) = 1 / Real.log 2 := by
      unfold Q
      push_cast
      field_simp
      ring
    have hinv_gt : (144 : ℝ) / 100 < 1 / Real.log 2 := by
      rw [lt_div_iff₀ hLpos]
      linarith
    have hinv_lt : 1 / Real.log 2 < (145 : ℝ) / 100 := by
      rw [div_lt_iff₀ hLpos]
      linarith
    have hsd_cast : (secondDifference k : ℝ) =
        (birthdayCount (k + 3) : ℝ) - 2 * (birthdayCount (k + 2) : ℝ) +
          (birthdayCount (k + 1) : ℝ) := by
      unfold secondDifference
      push_cast
      ring
    have hlin : ((k + 3 : ℕ) : ℝ) - 2 * ((k + 2 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) = 0 := by
      push_cast
      ring
    have hlo_real : (-1 : ℝ) < (secondDifference k : ℝ) := by
      rw [hsd_cast]
      linarith [hb3.1, hb2.2, hb1.1, hQdiff, hinv_gt, hlin]
    have hhi_real : (secondDifference k : ℝ) < (4 : ℝ) := by
      rw [hsd_cast]
      linarith [hb3.2, hb2.1, hb1.2, hQdiff, hinv_lt, hlin]
    have hlo_int : (-1 : ℤ) < secondDifference k := by exact_mod_cast hlo_real
    have hhi_int : secondDifference k < (4 : ℤ) := by exact_mod_cast hhi_real
    omega

end A180021Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a180021.main :=
  A180021Proof.secondDifference_bounds
