import OMAStatements.S_oeis_a321942
import Mathlib

open MeasureTheory Set Filter Topology

-- Part 1. The Lah sums A000262 satisfy the recurrence of a (creative telescoping).
-- T j k is the k-th term of A000262 (j + 1).

def a321942_T (n k : ℕ) : ℚ :=
  ((Nat.factorial k : ℕ) : ℚ) * (n.choose k : ℚ) * ((n + 1).choose k : ℚ)

theorem a321942_T_zero (n k : ℕ) (h : n < k) : a321942_T n k = 0 := by
  simp [a321942_T, Nat.choose_eq_zero_of_lt h]

theorem a321942_T_closed (k j : ℕ) :
    a321942_T (k + j) k = (Nat.factorial (k + j) : ℚ) * (Nat.factorial (k + j + 1) : ℚ) /
      ((Nat.factorial k : ℚ) * (Nat.factorial j : ℚ) * (Nat.factorial (j + 1) : ℚ)) := by
  have e1 : ((k + j).choose k : ℚ) * (Nat.factorial j) * (Nat.factorial k) =
      Nat.factorial (k + j) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial j k
    rw [Nat.add_comm j k] at h
    exact_mod_cast h
  have e2 : ((k + j + 1).choose k : ℚ) * (Nat.factorial (j + 1)) * (Nat.factorial k) =
      Nat.factorial (k + j + 1) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial (j + 1) k
    rw [show j + 1 + k = k + j + 1 by ring] at h
    exact_mod_cast h
  have hk : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  have hj : (Nat.factorial j : ℚ) ≠ 0 := by positivity
  have hj1 : (Nat.factorial (j + 1) : ℚ) ≠ 0 := by positivity
  rw [eq_div_iff (by positivity)]
  unfold a321942_T
  linear_combination ((Nat.factorial k : ℚ) * ((k + j + 1).choose k : ℚ) *
    (Nat.factorial (j + 1) : ℚ)) * e1 + (Nat.factorial (k + j) : ℚ) * e2

-- Shift in n.
theorem a321942_S (n k : ℕ) :
    a321942_T n k * (((n : ℚ) + 1) * ((n : ℚ) + 2)) =
      a321942_T (n + 1) k * (((n : ℚ) + 1 - k) * ((n : ℚ) + 2 - k)) := by
  rcases lt_trichotomy k (n + 1) with h | h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (by omega : k ≤ n)
    rw [show k + j + 1 = k + (j + 1) from rfl, a321942_T_closed k j, a321942_T_closed k (j + 1)]
    rw [show k + (j + 1) + 1 = k + j + 1 + 1 from rfl, show k + (j + 1) = k + j + 1 from rfl]
    rw [Nat.factorial_succ (k + j + 1), Nat.factorial_succ (k + j), Nat.factorial_succ (j + 1),
      Nat.factorial_succ j]
    push_cast
    field_simp
    ring
  · rw [a321942_T_zero n k (by omega), h]
    push_cast
    ring
  · rw [a321942_T_zero n k (by omega), a321942_T_zero (n + 1) k h]
    ring

-- Shift in k.
theorem a321942_K (n k : ℕ) :
    a321942_T n (k + 1) * ((k : ℚ) + 1) =
      a321942_T n k * (((n : ℚ) - k) * ((n : ℚ) + 1 - k)) := by
  rcases lt_trichotomy k n with h | h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show k + 1 ≤ n from h)
    rw [a321942_T_closed (k + 1) j, show k + 1 + j = k + (j + 1) by ring,
      a321942_T_closed k (j + 1)]
    rw [Nat.factorial_succ k, Nat.factorial_succ (j + 1), Nat.factorial_succ j]
    push_cast
    field_simp
    ring
  · rw [a321942_T_zero n (k + 1) (by omega), h]
    ring
  · rw [a321942_T_zero n k h, a321942_T_zero n (k + 1) (by omega)]
    ring

-- The certificate.
def a321942_G (m k : ℕ) : ℚ :=
  a321942_T (m + 2) k * ((k : ℚ) * (((m : ℚ) + 2 - k) ^ 2 - (m : ℚ) - 3)) /
    (((m : ℚ) + 2) * ((m : ℚ) + 3))

theorem a321942_step (m k : ℕ) :
    a321942_T (m + 2) k - (2 * (m : ℚ) + 5) * a321942_T (m + 1) k +
        ((m : ℚ) + 2) * ((m : ℚ) + 1) * a321942_T m k =
      a321942_G m (k + 1) - a321942_G m k := by
  have h1 := a321942_S (m + 1) k
  have h2 := a321942_S m k
  have h3 := a321942_K (m + 2) k
  rw [show m + 1 + 1 = m + 2 from rfl] at h1
  push_cast at h1 h2 h3
  have p1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have p2 : (m : ℚ) + 2 ≠ 0 := by positivity
  have p3 : (m : ℚ) + 3 ≠ 0 := by positivity
  have pk : (k : ℚ) + 1 ≠ 0 := by positivity
  have e1 : a321942_T (m + 1) k = a321942_T (m + 2) k * (((m : ℚ) + 2 - k) * ((m : ℚ) + 3 - k)) /
      (((m : ℚ) + 2) * ((m : ℚ) + 3)) := by
    rw [eq_div_iff (by positivity)]
    linear_combination h1
  have e2 : a321942_T m k = a321942_T (m + 1) k * (((m : ℚ) + 1 - k) * ((m : ℚ) + 2 - k)) /
      (((m : ℚ) + 1) * ((m : ℚ) + 2)) := by
    rw [eq_div_iff (by positivity)]
    linear_combination h2
  have e3 : a321942_T (m + 2) (k + 1) =
      a321942_T (m + 2) k * (((m : ℚ) + 2 - k) * ((m : ℚ) + 3 - k)) / ((k : ℚ) + 1) := by
    rw [eq_div_iff (by positivity)]
    linear_combination h3
  unfold a321942_G
  rw [e3, e2, e1]
  push_cast
  field_simp
  ring

theorem a321942_ext (n d N : ℕ) (hN : N = n + 1 + d) :
    ∑ k ∈ Finset.range (n + 1), a321942_T n k = ∑ k ∈ Finset.range N, a321942_T n k := by
  subst hN
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [ih, show n + 1 + (d + 1) = n + 1 + d + 1 from rfl, Finset.sum_range_succ _ (n + 1 + d),
      a321942_T_zero n (n + 1 + d) (by omega), add_zero]

theorem a321942_L_cast (j : ℕ) :
    ((OMA.S_oeis_a321942.A000262 (j + 1) : ℕ) : ℚ) = ∑ k ∈ Finset.range (j + 1), a321942_T j k := by
  simp [OMA.S_oeis_a321942.A000262, a321942_T]

theorem a321942_Lrec (m : ℕ) :
    ((OMA.S_oeis_a321942.A000262 (m + 3) : ℕ) : ℚ) =
      (2 * (m : ℚ) + 5) * (OMA.S_oeis_a321942.A000262 (m + 2) : ℚ) -
        ((m : ℚ) + 2) * ((m : ℚ) + 1) * (OMA.S_oeis_a321942.A000262 (m + 1) : ℚ) := by
  have tel : ∑ k ∈ Finset.range (m + 2 + 1), (a321942_T (m + 2) k -
      (2 * (m : ℚ) + 5) * a321942_T (m + 1) k + ((m : ℚ) + 2) * ((m : ℚ) + 1) * a321942_T m k) = 0 := by
    rw [Finset.sum_congr rfl (fun k _ => a321942_step m k), Finset.sum_range_sub]
    have h0 : a321942_T (m + 2) (m + 2 + 1) = 0 := a321942_T_zero _ _ (by omega)
    simp [a321942_G, h0]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at tel
  have s2 : ((OMA.S_oeis_a321942.A000262 (m + 3) : ℕ) : ℚ) =
      ∑ k ∈ Finset.range (m + 2 + 1), a321942_T (m + 2) k := a321942_L_cast (m + 2)
  have s1 : ((OMA.S_oeis_a321942.A000262 (m + 2) : ℕ) : ℚ) =
      ∑ k ∈ Finset.range (m + 2 + 1), a321942_T (m + 1) k :=
    (a321942_L_cast (m + 1)).trans (a321942_ext (m + 1) 1 _ (by omega))
  have s0 : ((OMA.S_oeis_a321942.A000262 (m + 1) : ℕ) : ℚ) =
      ∑ k ∈ Finset.range (m + 2 + 1), a321942_T m k :=
    (a321942_L_cast m).trans (a321942_ext m 2 _ (by omega))
  rw [s2, s1, s0]
  linear_combination tel

-- Part 2. The integrals satisfy the same recurrence.

noncomputable def a321942_I (n : ℕ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), (x / (1 + x)) ^ n * Real.exp (-x)

theorem a321942_int (n : ℕ) :
    IntegrableOn (fun x : ℝ => (x / (1 + x)) ^ n * Real.exp (-x)) (Ioi 0) := by
  have hc : ContinuousOn (fun x : ℝ => (x / (1 + x)) ^ n * Real.exp (-x)) (Ioi 0) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.pow
      apply ContinuousOn.div continuousOn_id (continuousOn_const.add continuousOn_id)
      intro x hx
      have hx0 : (0 : ℝ) < x := hx
      show (1 : ℝ) + x ≠ 0
      positivity
    · exact Continuous.continuousOn (by fun_prop)
  refine Integrable.mono' (integrableOn_exp_neg_Ioi 0) (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  show ‖(x / (1 + x)) ^ n * Real.exp (-x)‖ ≤ Real.exp (-x)
  have h1 : 0 ≤ x / (1 + x) := by positivity
  have h2 : x / (1 + x) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (pow_le_one₀ h1 h2)

theorem a321942_rec (m : ℕ) :
    ((m : ℝ) + 1) * a321942_I (m + 2) - (2 * (m : ℝ) + 3) * a321942_I (m + 1) +
      ((m : ℝ) + 1) * a321942_I m = 0 := by
  unfold a321942_I
  have i2 : Integrable (fun x : ℝ => ((m : ℝ) + 1) * ((x / (1 + x)) ^ (m + 2) * Real.exp (-x)))
      (volume.restrict (Ioi 0)) := (a321942_int (m + 2)).const_mul _
  have i1 : Integrable (fun x : ℝ => (2 * (m : ℝ) + 3) * ((x / (1 + x)) ^ (m + 1) * Real.exp (-x)))
      (volume.restrict (Ioi 0)) := (a321942_int (m + 1)).const_mul _
  have i0 : Integrable (fun x : ℝ => ((m : ℝ) + 1) * ((x / (1 + x)) ^ m * Real.exp (-x)))
      (volume.restrict (Ioi 0)) := (a321942_int m).const_mul _
  have i21 : Integrable (fun x : ℝ => ((m : ℝ) + 1) * ((x / (1 + x)) ^ (m + 2) * Real.exp (-x)) -
      (2 * (m : ℝ) + 3) * ((x / (1 + x)) ^ (m + 1) * Real.exp (-x))) (volume.restrict (Ioi 0)) :=
    i2.sub i1
  have iall : IntegrableOn (fun x : ℝ => ((m : ℝ) + 1) * ((x / (1 + x)) ^ (m + 2) * Real.exp (-x)) -
      (2 * (m : ℝ) + 3) * ((x / (1 + x)) ^ (m + 1) * Real.exp (-x)) +
      ((m : ℝ) + 1) * ((x / (1 + x)) ^ m * Real.exp (-x))) (Ioi 0) := i21.add i0
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun y : ℝ => (y / (1 + y)) ^ (m + 1) * Real.exp (-y))
      (((m : ℝ) + 1) * ((x / (1 + x)) ^ (m + 2) * Real.exp (-x)) -
        (2 * (m : ℝ) + 3) * ((x / (1 + x)) ^ (m + 1) * Real.exp (-x)) +
        ((m : ℝ) + 1) * ((x / (1 + x)) ^ m * Real.exp (-x))) x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx
    have hne : (1 : ℝ) + x ≠ 0 := by positivity
    have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' x
    have hden : HasDerivAt (fun y : ℝ => 1 + y) 1 x := hid.const_add 1
    have h1 : HasDerivAt (fun y : ℝ => y / (1 + y)) ((1 * (1 + x) - x * 1) / (1 + x) ^ 2) x :=
      hid.div hden hne
    have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := hasDerivAt_neg' x
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-x) * -1) x := hneg.exp
    have key : HasDerivAt (fun y : ℝ => (y / (1 + y)) ^ (m + 1) * Real.exp (-y))
        (((m + 1 : ℕ) : ℝ) * (x / (1 + x)) ^ (m + 1 - 1) * ((1 * (1 + x) - x * 1) / (1 + x) ^ 2) *
          Real.exp (-x) + (x / (1 + x)) ^ (m + 1) * (Real.exp (-x) * -1)) x :=
      (h1.pow (m + 1)).mul hexp
    have hD : (1 * (1 + x) - x * 1) / (1 + x) ^ 2 = (1 - x / (1 + x)) ^ 2 := by
      field_simp
      ring
    rw [hD, Nat.add_sub_cancel] at key
    convert key using 1
    push_cast
    ring
  have hlim : Tendsto (fun y : ℝ => (y / (1 + y)) ^ (m + 1) * Real.exp (-y)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      Real.tendsto_exp_neg_atTop_nhds_zero ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      positivity
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      have h1 : 0 ≤ x / (1 + x) := by positivity
      have h2 : x / (1 + x) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
      exact mul_le_of_le_one_left (Real.exp_pos _).le (pow_le_one₀ h1 h2)
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv iall hlim
  rw [integral_add i21 i0, integral_sub i2 i1, integral_const_mul, integral_const_mul,
    integral_const_mul] at hftc
  rw [hftc]
  simp

theorem a321942_I0 : a321942_I 0 = 1 := by
  unfold a321942_I
  simp only [pow_zero, one_mul]
  exact integral_exp_neg_Ioi_zero

theorem a321942_I1 : a321942_I 1 = 1 - OMA.S_oeis_a321942.G := by
  unfold a321942_I OMA.S_oeis_a321942.G
  have hG : IntegrableOn (fun x : ℝ => Real.exp (-x) / (1 + x)) (Ioi 0) := by
    refine ((a321942_int 0).sub (a321942_int 1)).congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hne : (1 : ℝ) + x ≠ 0 := by positivity
    simp only [Pi.sub_apply, pow_zero, pow_one, one_mul]
    field_simp
    ring
  have e : ∫ x in Ioi (0 : ℝ), (x / (1 + x)) ^ 1 * Real.exp (-x) =
      ∫ x in Ioi (0 : ℝ), (Real.exp (-x) - Real.exp (-x) / (1 + x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hne : (1 : ℝ) + x ≠ 0 := by positivity
    simp only [pow_one]
    field_simp
    ring
  rw [e, integral_sub (integrableOn_exp_neg_Ioi 0) hG, integral_exp_neg_Ioi_zero]

-- Part 3. Induction.

theorem a321942_claim (m : ℕ) :
    a321942_I (m + 1) * (m.factorial : ℝ) = (OMA.S_oeis_a321942.a (m + 1) : ℝ) -
        (OMA.S_oeis_a321942.A000262 (m + 1) : ℝ) * OMA.S_oeis_a321942.G ∧
      a321942_I (m + 2) * ((m + 1).factorial : ℝ) = (OMA.S_oeis_a321942.a (m + 2) : ℝ) -
        (OMA.S_oeis_a321942.A000262 (m + 2) : ℝ) * OMA.S_oeis_a321942.G := by
  induction m with
  | zero =>
    have h0 := a321942_I0
    have h1 := a321942_I1
    have r := a321942_rec 0
    have L1 : OMA.S_oeis_a321942.A000262 1 = 1 := by decide +kernel
    have L2 : OMA.S_oeis_a321942.A000262 2 = 3 := by decide +kernel
    have a1 : OMA.S_oeis_a321942.a 1 = 1 := rfl
    have a2 : OMA.S_oeis_a321942.a 2 = 2 := rfl
    simp only [Nat.zero_add] at r ⊢
    rw [L1, L2, a1, a2]
    push_cast at r ⊢
    simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, mul_one] at r ⊢
    constructor
    · linarith
    · linarith
  | succ m ih =>
    obtain ⟨hP0, hP1⟩ := ih
    refine ⟨hP1, ?_⟩
    have r := a321942_rec (m + 1)
    simp only [show m + 1 + 1 = m + 2 from rfl, show m + 1 + 2 = m + 3 from rfl] at r ⊢
    have ha0 : OMA.S_oeis_a321942.a (m + 3) = (2 * ((m : ℤ) + 3) - 1) * OMA.S_oeis_a321942.a (m + 2) -
        (((m : ℤ) + 3) - 1) * (((m : ℤ) + 3) - 2) * OMA.S_oeis_a321942.a (m + 1) := by
      first
        | rfl
        | simp only [OMA.S_oeis_a321942.a]
    have ha : ((OMA.S_oeis_a321942.a (m + 3) : ℤ) : ℝ) =
        (2 * (m : ℝ) + 5) * (OMA.S_oeis_a321942.a (m + 2) : ℝ) -
          ((m : ℝ) + 2) * ((m : ℝ) + 1) * (OMA.S_oeis_a321942.a (m + 1) : ℝ) := by
      rw [ha0]
      push_cast
      ring
    have hZ : (OMA.S_oeis_a321942.A000262 (m + 3) : ℤ) =
        (2 * (m : ℤ) + 5) * (OMA.S_oeis_a321942.A000262 (m + 2) : ℤ) -
          ((m : ℤ) + 2) * ((m : ℤ) + 1) * (OMA.S_oeis_a321942.A000262 (m + 1) : ℤ) := by
      have hq := a321942_Lrec m
      exact_mod_cast hq
    have hL : (OMA.S_oeis_a321942.A000262 (m + 3) : ℝ) =
        (2 * (m : ℝ) + 5) * (OMA.S_oeis_a321942.A000262 (m + 2) : ℝ) -
          ((m : ℝ) + 2) * ((m : ℝ) + 1) * (OMA.S_oeis_a321942.A000262 (m + 1) : ℝ) := by
      exact_mod_cast hZ
    have hf1 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hf2 : ((m + 2).factorial : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) * (m.factorial : ℝ) := by
      rw [Nat.factorial_succ (m + 1), Nat.factorial_succ m]
      push_cast
      ring
    rw [hf1] at hP1
    rw [hf2, ha, hL]
    push_cast at r
    linear_combination ((m : ℝ) + 1) * (m.factorial : ℝ) * r + (2 * (m : ℝ) + 5) * hP1 -
      ((m : ℝ) + 2) * ((m : ℝ) + 1) * hP0

theorem OMA.solution : type_of% @OMA.S_oeis_a321942.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := (a321942_claim m).1
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  rw [Nat.add_sub_cancel]
  show a321942_I (m + 1) = _
  rw [← h, one_div, mul_comm (a321942_I (m + 1)) _, ← mul_assoc, inv_mul_cancel₀ hm, one_mul]
