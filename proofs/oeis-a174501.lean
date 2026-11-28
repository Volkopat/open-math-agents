import OMAStatements.S_oeis_a174501

namespace OMA.S_oeis_a174501

/-- `q = 3 - sqrt 8`. -/
noncomputable def q : ℝ := 3 - Real.sqrt 8

lemma sqrt8_lt : Real.sqrt 8 < 3 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma lt_sqrt8 : (14 : ℝ) / 5 < Real.sqrt 8 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

lemma q_pos : 0 < q := by unfold q; linarith [sqrt8_lt]

lemma q_lt : q < 1 / 5 := by unfold q; linarith [lt_sqrt8]

lemma q_sq : q ^ 2 = 6 * q - 1 := by
  unfold q; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 8 by norm_num)]

lemma qpow_pos (k : ℕ) : 0 < q ^ k := pow_pos q_pos k
lemma qpow_nonneg (k : ℕ) : 0 ≤ q ^ k := (qpow_pos k).le

lemma A_formula (n : ℕ) : (A003499 n : ℝ) = q ^ n + (q ^ n)⁻¹ := by
  have hq := q_pos
  set p := q⁻¹ with hp
  have hqp : q * p = 1 := mul_inv_cancel₀ hq.ne'
  have hp2 : p ^ 2 = 6 * p - 1 := by
    linear_combination p ^ 2 * q_sq + (6 * p - p * q - 1) * hqp
  have key : ∀ n, (A003499 n : ℝ) = q ^ n + p ^ n ∧
      (A003499 (n + 1) : ℝ) = q ^ (n + 1) + p ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [A003499]; norm_num, ?_⟩
      simp only [A003499, zero_add, pow_one]
      push_cast
      linear_combination (-p) * q_sq + (q - 6) * hqp
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 1 = k + 2 from rfl, A003499]
      push_cast
      rw [ih.1, ih.2]
      linear_combination (-q ^ k) * q_sq + (-p ^ k) * hp2
  rw [(key n).1, hp, inv_pow]

/-- Coefficients of the auxiliary q-series. -/
noncomputable def c (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => c a j * q ^ (2 * j) * (1 - a * q ^ (2 * j + 1)) / (1 - q ^ (2 * j + 2))

noncomputable def H (a z : ℝ) : ℝ := ∑' j : ℕ, c a j * z ^ j

lemma qpow_lt_one (k : ℕ) (hk : k ≠ 0) : q ^ k < 1 :=
  pow_lt_one₀ q_pos.le (by linarith [q_lt]) hk

lemma den_pos (j : ℕ) : 0 < 1 - q ^ (2 * j + 2) := by
  linarith [qpow_lt_one (2 * j + 2) (by omega)]

lemma c_nonneg {a : ℝ} (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) (j : ℕ) : 0 ≤ c a j := by
  induction j with
  | zero => simp [c]
  | succ j ih =>
    simp only [c]
    have : a * q ^ (2 * j + 1) ≤ 1 := by
      calc a * q ^ (2 * j + 1) ≤ 1 * 1 :=
            mul_le_mul ha1 (qpow_lt_one _ (by omega)).le (qpow_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have := den_pos j
    have : 0 ≤ q ^ (2 * j) := qpow_nonneg _
    apply div_nonneg _ (by linarith)
    apply mul_nonneg (mul_nonneg ih this) (by linarith)

/-- Uniform bound `c a j ≤ 4 (1/2)^j` for `0 ≤ a ≤ 1`. -/
lemma c_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (j : ℕ) : c a j ≤ 4 * (1 / 2) ^ j := by
  have hq := q_pos
  have hql := q_lt
  have step : ∀ j, c a (j + 1) ≤ 2 * (1 / 2) ^ j := by
    intro j
    induction j with
    | zero =>
      simp only [c]
      have := den_pos 0
      rw [div_le_iff₀ this]
      have : 0 ≤ a * q ^ (2 * 0 + 1) := mul_nonneg ha0 (qpow_nonneg _)
      have : q ^ (2 * 0 + 2) ≤ 1 / 4 := by norm_num; nlinarith
      norm_num at *; nlinarith
    | succ j ih =>
      rw [show c a (j + 1 + 1) = c a (j + 1) * q ^ (2 * (j + 1)) * (1 - a * q ^ (2 * (j + 1) + 1)) /
        (1 - q ^ (2 * (j + 1) + 2)) from rfl]
      have hd := den_pos (j + 1)
      rw [div_le_iff₀ hd]
      have h1 : q ^ (2 * (j + 1)) ≤ q ^ 2 := pow_le_pow_of_le_one hq.le (by linarith) (by omega)
      have h2 : q ^ (2 * (j + 1) + 2) ≤ q ^ 2 := pow_le_pow_of_le_one hq.le (by linarith) (by omega)
      have h3 : 0 ≤ a * q ^ (2 * (j + 1) + 1) := mul_nonneg ha0 (qpow_nonneg _)
      have h4 : a * q ^ (2 * (j + 1) + 1) ≤ 1 :=
        calc a * q ^ (2 * (j + 1) + 1) ≤ 1 * 1 :=
              mul_le_mul ha1 (qpow_lt_one _ (by omega)).le (qpow_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      have hc := c_nonneg ha0 ha1 (j + 1)
      have hq2 : q ^ 2 ≤ 1 / 25 := by nlinarith
      have hp : (0:ℝ) ≤ (1/2) ^ j := by positivity
      have e : (2:ℝ) * (1 / 2) ^ (j + 1) = (1/2)^j := by ring
      rw [e]
      have hqq : 0 ≤ q ^ (2 * (j + 1)) := qpow_nonneg _
      calc c a (j + 1) * q ^ (2 * (j + 1)) * (1 - a * q ^ (2 * (j + 1) + 1))
          ≤ (2 * (1/2)^j) * (1/25) * 1 := by
            apply mul_le_mul (mul_le_mul ih (h1.trans hq2) hqq (by positivity)) (by linarith)
              (by linarith) (by positivity)
        _ ≤ (1 / 2) ^ j * (1 - q ^ (2 * (j + 1) + 2)) := by nlinarith
  cases j with
  | zero => simp [c]
  | succ j => have := step j; rw [pow_succ]; linarith

lemma term_nonneg {a z : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hz0 : 0 ≤ z) (j : ℕ) :
    0 ≤ c a j * z ^ j := mul_nonneg (c_nonneg ha0 ha1 j) (pow_nonneg hz0 j)

lemma term_le {a z : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (j : ℕ) :
    c a j * z ^ j ≤ 4 * (1 / 2) ^ j := by
  calc c a j * z ^ j ≤ 4 * (1 / 2) ^ j * 1 :=
        mul_le_mul (c_le ha0 ha1 j) (pow_le_one₀ hz0 hz1) (by positivity) (by positivity)
    _ = _ := by ring

lemma summable_bound : Summable (fun j : ℕ => (4 : ℝ) * (1 / 2) ^ j) :=
  (summable_geometric_two).mul_left 4

lemma summable_term {a z : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Summable (fun j => c a j * z ^ j) :=
  Summable.of_nonneg_of_le (term_nonneg ha0 ha1 hz0) (term_le ha0 ha1 hz0 hz1) summable_bound

lemma one_le_H {a z : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    1 ≤ H a z := by
  have := (summable_term ha0 ha1 hz0 hz1).le_tsum 0 (fun j _ => term_nonneg ha0 ha1 hz0 j)
  simpa [H, c] using this

lemma H_le {a z : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    H a z ≤ 8 := by
  have := (summable_term ha0 ha1 hz0 hz1).tsum_le_tsum (term_le ha0 ha1 hz0 hz1) summable_bound
  rw [tsum_mul_left, tsum_geometric_two] at this
  unfold H; linarith

lemma H_mono {a z w : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hz0 : 0 ≤ z) (hzw : z ≤ w) (hw1 : w ≤ 1) :
    H a z ≤ H a w :=
  (summable_term ha0 ha1 hz0 (hzw.trans hw1)).tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hzw j) (c_nonneg ha0 ha1 j))
    (summable_term ha0 ha1 (hz0.trans hzw) hw1)


lemma cX (a : ℝ) (j : ℕ) : c a j * (1 - a * q ^ (2 * j + 1)) = (1 - a * q) * c (a * q ^ 2) j := by
  induction j with
  | zero => simp [c]
  | succ j ih =>
    simp only [c]
    have hd := (den_pos j).ne'
    rw [show c a j * q ^ (2 * j) * (1 - a * q ^ (2 * j + 1)) =
      (c a j * (1 - a * q ^ (2 * j + 1))) * q ^ (2 * j) by ring, ih]
    field_simp
    ring

lemma cR1 (a : ℝ) (j : ℕ) :
    c a (j + 1) = c (a * q ^ 2) (j + 1) - a * q * q ^ (2 * j) * c (a * q ^ 2) j := by
  have h := cX a j
  have hd := (den_pos j).ne'
  simp only [c]
  rw [mul_assoc (c a j), mul_comm (q ^ (2 * j)), ← mul_assoc, h]
  field_simp
  ring

lemma cR2 (a : ℝ) (j : ℕ) :
    c a (j + 1) * (1 - q ^ (2 * j + 2)) = c a j * q ^ (2 * j) * (1 - a * q ^ (2 * j + 1)) := by
  simp only [c]
  exact div_mul_cancel₀ _ (den_pos j).ne'

lemma unit_aq2 {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : 0 ≤ a * q ^ 2 ∧ a * q ^ 2 ≤ 1 :=
  ⟨mul_nonneg ha0 (qpow_nonneg 2),
   by nlinarith [qpow_lt_one 2 (by norm_num), qpow_nonneg 2]⟩

lemma unit_zq2 {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ z * q ^ 2 ∧ z * q ^ 2 ≤ 1 :=
  unit_aq2 hz0 hz1

/-- `H a z = H (a q^2) z - a q z H (a q^2) (z q^2)`. -/
lemma HR1 {a z : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    H a z = H (a * q ^ 2) z - a * q * z * H (a * q ^ 2) (z * q ^ 2) := by
  obtain ⟨hb0, hb1⟩ := unit_aq2 ha0 ha1
  obtain ⟨hw0, hw1⟩ := unit_zq2 hz0 hz1
  have S1 := summable_term ha0 ha1 hz0 hz1
  have S2 := summable_term hb0 hb1 hz0 hz1
  have S3 := summable_term hb0 hb1 hw0 hw1
  unfold H
  rw [S1.tsum_eq_zero_add, S2.tsum_eq_zero_add]
  have S2' := (summable_nat_add_iff 1).mpr S2
  have e : ∀ j : ℕ, c a (j + 1) * z ^ (j + 1) =
      c (a * q ^ 2) (j + 1) * z ^ (j + 1) - a * q * z * (c (a * q ^ 2) j * (z * q ^ 2) ^ j) := by
    intro j; rw [cR1]; rw [mul_pow, ← pow_mul, mul_comm 2 j]; ring
  simp_rw [e]
  rw [S2'.tsum_sub (S3.mul_left _), tsum_mul_left]
  simp [c]; ring

/-- `H a z - a q H a (z q^2) = (1 - a q) H (a q^2) z`. -/
lemma HR2 {a z : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    H a z - a * q * H a (z * q ^ 2) = (1 - a * q) * H (a * q ^ 2) z := by
  obtain ⟨hb0, hb1⟩ := unit_aq2 ha0 ha1
  obtain ⟨hw0, hw1⟩ := unit_zq2 hz0 hz1
  have S1 := summable_term ha0 ha1 hz0 hz1
  have S2 := summable_term hb0 hb1 hz0 hz1
  have S3 := summable_term ha0 ha1 hw0 hw1
  unfold H
  rw [← tsum_mul_left, ← tsum_mul_left, ← S1.tsum_sub (S3.mul_left _)]
  congr 1; ext j
  rw [show (1 - a * q) * (c (a * q ^ 2) j * z ^ j) = ((1 - a * q) * c (a * q ^ 2) j) * z ^ j by ring,
    ← cX, mul_pow, ← pow_mul]; ring

/-- The `a = 1` three-term relation `H z = (1+z) H (z q^2) - q z H (z q^4)`. -/
lemma HR3 {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    H 1 z = (1 + z) * H 1 (z * q ^ 2) - q * z * H 1 (z * q ^ 2 * q ^ 2) := by
  obtain ⟨hw0, hw1⟩ := unit_zq2 hz0 hz1
  have h1 := HR1 zero_le_one le_rfl hz0 hz1
  have h2 := HR2 zero_le_one le_rfl hz0 hz1
  have h3 := HR2 zero_le_one le_rfl hw0 hw1
  have hq := q_pos
  have : q * (H 1 z - ((1 + z) * H 1 (z * q ^ 2) - q * z * H 1 (z * q ^ 2 * q ^ 2))) = 0 := by
    linear_combination (-(1 - q)) * h1 + h2 - q * z * h3
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hq.ne'
  · linarith

lemma q2_unit : 0 ≤ q ^ 2 ∧ q ^ 2 ≤ 1 := ⟨qpow_nonneg 2, (qpow_lt_one 2 (by norm_num)).le⟩

lemma K_step {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    H a (q ^ 2) = (1 - a * q ^ 3) * H (a * q ^ 4) (q ^ 2) := by
  obtain ⟨hb0, hb1⟩ := unit_aq2 ha0 ha1
  rw [HR1 ha0 ha1 q2_unit.1 q2_unit.2]
  have := HR2 hb0 hb1 q2_unit.1 q2_unit.2
  rw [show a * q ^ 2 * q ^ 2 = a * q ^ 4 by ring] at this
  linear_combination this

lemma M_step {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    H a (q ^ 2) - a * q * H a (q ^ 4) =
      (1 - a * q) * (H (a * q ^ 4) (q ^ 2) - a * q ^ 4 * q * H (a * q ^ 4) (q ^ 4)) := by
  obtain ⟨hb0, hb1⟩ := unit_aq2 ha0 ha1
  have h2 := HR2 ha0 ha1 q2_unit.1 q2_unit.2
  rw [show q ^ 2 * q ^ 2 = q ^ 4 by ring] at h2
  rw [h2, HR1 hb0 hb1 q2_unit.1 q2_unit.2]
  rw [show a * q ^ 2 * q ^ 2 = a * q ^ 4 by ring, show q ^ 2 * q ^ 2 = q ^ 4 by ring]
  ring


open Filter Topology Finset

lemma a4_unit (N : ℕ) : 0 ≤ q ^ (4 * N) ∧ q ^ (4 * N) ≤ 1 :=
  ⟨qpow_nonneg _, pow_le_one₀ q_pos.le (by linarith [q_lt])⟩

lemma K_prod (N : ℕ) :
    H 1 (q ^ 2) = (∏ m ∈ range N, (1 - q ^ (4 * m + 3))) * H (q ^ (4 * N)) (q ^ 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, K_step (a4_unit N).1 (a4_unit N).2, prod_range_succ]
    rw [show q ^ (4 * N) * q ^ 3 = q ^ (4 * N + 3) by ring,
      show q ^ (4 * N) * q ^ 4 = q ^ (4 * (N + 1)) by ring]
    ring

/-- `M a = H a (q^2) - a q H a (q^4)`. -/
noncomputable def M (a : ℝ) : ℝ := H a (q ^ 2) - a * q * H a (q ^ 4)

lemma M_prod (N : ℕ) :
    M 1 = (∏ m ∈ range N, (1 - q ^ (4 * m + 1))) * M (q ^ (4 * N)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih]; unfold M
    rw [M_step (a4_unit N).1 (a4_unit N).2, prod_range_succ]
    rw [show q ^ (4 * N) * q = q ^ (4 * N + 1) by ring,
      show q ^ (4 * N) * q ^ 4 = q ^ (4 * (N + 1)) by ring]
    ring

lemma M_pos {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : 0 < M a := by
  obtain ⟨hb0, hb1⟩ := unit_aq2 ha0 ha1
  have h := HR2 ha0 ha1 q2_unit.1 q2_unit.2
  rw [show q ^ 2 * q ^ 2 = q ^ 4 by ring] at h
  unfold M; rw [h]
  have := one_le_H hb0 hb1 q2_unit.1 q2_unit.2
  have : a * q < 1 := by nlinarith [q_lt, q_pos]
  nlinarith

lemma continuous_c (j : ℕ) : Continuous (fun a => c a j) := by
  induction j with
  | zero => simp only [c]; exact continuous_const
  | succ j ih =>
    show Continuous (fun a => c a j * q ^ (2 * j) * (1 - a * q ^ (2 * j + 1)) / (1 - q ^ (2 * j + 2)))
    exact ((ih.mul continuous_const).mul (continuous_const.sub (continuous_id.mul continuous_const))).div_const _

lemma tendsto_a4 : Tendsto (fun N : ℕ => q ^ (4 * N)) atTop (𝓝 0) := by
  have := tendsto_pow_atTop_nhds_zero_of_lt_one (qpow_nonneg 4) (qpow_lt_one 4 (by norm_num))
  simpa [pow_mul] using this

lemma H_tendsto {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun N : ℕ => H (q ^ (4 * N)) z) atTop (𝓝 (H 0 z)) := by
  unfold H
  apply tendsto_tsum_of_dominated_convergence summable_bound
  · intro j
    have h1 := ((continuous_c j).tendsto 0).comp tendsto_a4
    exact h1.mul_const _
  · refine Eventually.of_forall (fun N j => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg (a4_unit N).1 (a4_unit N).2 hz0 j)]
    exact term_le (a4_unit N).1 (a4_unit N).2 hz0 hz1 j

lemma partial_prod_tendsto :
    Tendsto (fun N : ℕ => (∏ m ∈ range N, (1 - q ^ (4 * m + 3))) /
      (∏ m ∈ range N, (1 - q ^ (4 * m + 1)))) atTop (𝓝 (H 1 (q ^ 2) / M 1)) := by
  have hK : Tendsto (fun N : ℕ => H (q ^ (4 * N)) (q ^ 2)) atTop (𝓝 (H 0 (q ^ 2))) :=
    H_tendsto q2_unit.1 q2_unit.2
  have q4u : 0 ≤ q ^ 4 ∧ q ^ 4 ≤ 1 := ⟨qpow_nonneg 4, (qpow_lt_one 4 (by norm_num)).le⟩
  have hM : Tendsto (fun N : ℕ => M (q ^ (4 * N))) atTop (𝓝 (H 0 (q ^ 2))) := by
    have := hK.sub ((tendsto_a4.mul_const q).mul (H_tendsto q4u.1 q4u.2))
    simpa [M] using this
  have h0 : H 0 (q ^ 2) ≠ 0 := (lt_of_lt_of_le one_pos (one_le_H le_rfl zero_le_one q2_unit.1 q2_unit.2)).ne'
  have hlim : Tendsto (fun N : ℕ => H 1 (q ^ 2) / M 1 * (M (q ^ (4 * N)) / H (q ^ (4 * N)) (q ^ 2)))
      atTop (𝓝 (H 1 (q ^ 2) / M 1 * (H 0 (q ^ 2) / H 0 (q ^ 2)))) :=
    (hM.div hK h0).const_mul _
  rw [div_self h0, mul_one] at hlim
  refine hlim.congr (fun N => ?_)
  have hKN := one_le_H (a4_unit N).1 (a4_unit N).2 q2_unit.1 q2_unit.2
  have hMN := M_pos (a4_unit N).1 (a4_unit N).2
  have hM1 := M_pos zero_le_one le_rfl
  rw [K_prod N, M_prod N]
  have hp : (∏ m ∈ range N, (1 - q ^ (4 * m + 1))) ≠ 0 := by
    rw [prod_ne_zero_iff]; intro m _
    linarith [qpow_lt_one (4 * m + 1) (by omega)]
  field_simp


/-- The double series. -/
noncomputable def F (p : ℕ × ℕ) : ℝ :=
  (-1) ^ p.2 * ((q ^ (2 * p.2 + 1)) ^ (p.1 + 1) / ((p.1 : ℝ) + 1))

lemma summable_F : Summable F := by
  have hg : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one (qpow_nonneg 1 |>.trans_eq (pow_one q)) (by linarith [q_lt])
  have hprod := hg.mul_of_nonneg hg (fun n => qpow_nonneg n) (fun n => qpow_nonneg n)
  refine Summable.of_norm_bounded hprod (fun p => ?_)
  obtain ⟨n, k⟩ := p
  rw [Real.norm_eq_abs, F, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_div,
    abs_of_nonneg (pow_nonneg (qpow_nonneg _) _), abs_of_pos (by positivity : (0:ℝ) < (n:ℝ) + 1)]
  have h1 : (q ^ (2 * k + 1)) ^ (n + 1) ≤ q ^ n * q ^ k := by
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_of_le_one q_pos.le (by linarith [q_lt]) (by nlinarith)
  have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  calc (q ^ (2 * k + 1)) ^ (n + 1) / ((n : ℝ) + 1) ≤ (q ^ (2 * k + 1)) ^ (n + 1) :=
        div_le_self (pow_nonneg (qpow_nonneg _) _) h2
    _ ≤ _ := h1

lemma fiber_n (n : ℕ) :
    HasSum (fun k => F (n, k)) (1 / (((n : ℝ) + 1) * (A003499 (n + 1) : ℝ))) := by
  have hr1 : |-(q ^ (2 * (n + 1)))| < 1 := by
    rw [abs_neg, abs_of_nonneg (qpow_nonneg _)]; exact qpow_lt_one _ (by omega)
  have h := (hasSum_geometric_of_abs_lt_one hr1).mul_left (q ^ (n + 1) / ((n : ℝ) + 1))
  have e : ∀ k : ℕ, F (n, k) = q ^ (n + 1) / ((n : ℝ) + 1) * (-(q ^ (2 * (n + 1)))) ^ k := by
    intro k
    unfold F
    dsimp only
    rw [neg_pow (q ^ (2 * (n + 1))) k, ← pow_mul, ← pow_mul,
      show (2 * k + 1) * (n + 1) = (n + 1) + 2 * (n + 1) * k by ring, pow_add]
    ring
  have hv : 1 / (((n : ℝ) + 1) * (A003499 (n + 1) : ℝ)) =
      q ^ (n + 1) / ((n : ℝ) + 1) * (1 - -(q ^ (2 * (n + 1))))⁻¹ := by
    rw [A_formula]
    have hq1 : 0 < q ^ (n + 1) := qpow_pos _
    have hn : (0:ℝ) < (n : ℝ) + 1 := by positivity
    rw [show q ^ (2 * (n + 1)) = q ^ (n + 1) * q ^ (n + 1) by rw [← pow_add]; ring_nf]
    have hd : (1 - -(q ^ (n + 1) * q ^ (n + 1))) ≠ 0 := by nlinarith
    rw [eq_mul_inv_iff_mul_eq₀ hd]
    field_simp
    ring
  rw [show (fun k => F (n, k)) = fun k => q ^ (n + 1) / ((n : ℝ) + 1) * (-(q ^ (2 * (n + 1)))) ^ k
    from funext e, hv]
  exact h

/-- `g k = (-1)^k * (-log (1 - q^(2k+1)))`. -/
noncomputable def g (k : ℕ) : ℝ := (-1) ^ k * (-Real.log (1 - q ^ (2 * k + 1)))

lemma fiber_k (k : ℕ) : HasSum (fun n => F (n, k)) (g k) := by
  have h1 : |q ^ (2 * k + 1)| < 1 := by
    rw [abs_of_nonneg (qpow_nonneg _)]; exact qpow_lt_one _ (by omega)
  exact (Real.hasSum_pow_div_log_of_abs_lt_one h1).mul_left _

/-- The exponent `L` of the OEIS constant. -/
noncomputable def L : ℝ := ∑' n : ℕ, 1 / (((n : ℝ) + 1) * (A003499 (n + 1) : ℝ))

lemma hasSum_g : HasSum g L := by
  have hF := summable_F.hasSum
  have hn := hF.prod_fiberwise fiber_n
  have hk := ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hF).prod_fiberwise (fun k => fiber_k k)
  unfold L
  rw [hn.tsum_eq]
  exact hk

lemma exp_partial (N : ℕ) :
    Real.exp (∑ k ∈ range (2 * N), g k) =
      (∏ m ∈ range N, (1 - q ^ (4 * m + 3))) / (∏ m ∈ range N, (1 - q ^ (4 * m + 1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      Real.exp_add, Real.exp_add, ih, prod_range_succ, prod_range_succ]
    have h1 : 0 < 1 - q ^ (4 * N + 1) := by linarith [qpow_lt_one (4 * N + 1) (by omega)]
    have h3 : 0 < 1 - q ^ (4 * N + 3) := by linarith [qpow_lt_one (4 * N + 3) (by omega)]
    have e1 : g (2 * N) = -Real.log (1 - q ^ (4 * N + 1)) := by
      simp only [g]; rw [pow_mul]; norm_num; ring_nf
    have e2 : g (2 * N + 1) = Real.log (1 - q ^ (4 * N + 3)) := by
      simp only [g]; rw [pow_succ, pow_mul]; norm_num; ring_nf
    rw [e1, e2, Real.exp_neg, Real.exp_log h1, Real.exp_log h3]
    have hp : (∏ m ∈ range N, (1 - q ^ (4 * m + 1))) ≠ 0 := by
      rw [prod_ne_zero_iff]; intro m _
      linarith [qpow_lt_one (4 * m + 1) (by omega)]
    field_simp

lemma x_eq : x = H 1 (q ^ 2) / M 1 := by
  have h1 : Tendsto (fun N : ℕ => ∑ k ∈ range (2 * N), g k) atTop (𝓝 L) :=
    hasSum_g.tendsto_sum_nat.comp (tendsto_atTop_mono (fun n => show n ≤ 2 * n by omega) tendsto_id)
  have h2 := (Real.continuous_exp.tendsto L).comp h1
  have h3 : Tendsto (fun N : ℕ => (∏ m ∈ range N, (1 - q ^ (4 * m + 3))) /
      (∏ m ∈ range N, (1 - q ^ (4 * m + 1)))) atTop (𝓝 (Real.exp L)) := by
    refine h2.congr (fun N => ?_)
    simp only [Function.comp, exp_partial]
  exact tendsto_nhds_unique h3 partial_prod_tendsto


lemma cf_step {v w : ℝ} {b : ℤ} (hw : 1 < w) (hv : v = b + 1 / w) :
    (GenContFract.of v).h = b ∧
    (GenContFract.of v).partDens.get? 0 = some (GenContFract.of w).h ∧
    ∀ n, (GenContFract.of v).partDens.get? (n + 1) = (GenContFract.of w).partDens.get? n := by
  have hw0 : 0 < w := by linarith
  have h1 : 0 < 1 / w := by positivity
  have h2 : 1 / w < 1 := by rw [div_lt_one hw0]; exact hw
  have hfl : ⌊v⌋ = b := by
    rw [Int.floor_eq_iff, hv]; constructor <;> linarith
  have hfr : Int.fract v = 1 / w := by
    rw [Int.fract, hfl, hv]; ring
  refine ⟨by rw [GenContFract.of_h_eq_floor, hfl], ?_, ?_⟩
  · have hs := GenContFract.of_s_head (v := v) (by rw [hfr]; exact h1.ne')
    unfold GenContFract.partDens
    rw [Stream'.Seq.map_get?]
    change (GenContFract.of v).s.get? 0 = _ at hs
    rw [hs, hfr, one_div, inv_inv, GenContFract.of_h_eq_floor]
    rfl
  · intro n
    unfold GenContFract.partDens
    rw [Stream'.Seq.map_get?, Stream'.Seq.map_get?, GenContFract.of_s_succ, hfr, one_div, inv_inv]

/-- Tails of the negative continued fraction `A(1) - 1/(A(2) - 1/(A(3) - ...))`. -/
noncomputable def u (n : ℕ) : ℝ := H 1 (q ^ (2 * n + 2)) / (q ^ (n + 1) * H 1 (q ^ (2 * n + 4)))

lemma qz_unit (k : ℕ) : 0 ≤ q ^ k ∧ q ^ k ≤ 1 := ⟨qpow_nonneg k, pow_le_one₀ q_pos.le (by linarith [q_lt])⟩

lemma u_gt (n : ℕ) : 2 < u n := by
  have hH4 := one_le_H zero_le_one le_rfl (qz_unit (2 * n + 4)).1 (qz_unit (2 * n + 4)).2
  have hmono : H 1 (q ^ (2 * n + 4)) ≤ H 1 (q ^ (2 * n + 2)) :=
    H_mono zero_le_one le_rfl (qz_unit _).1
      (pow_le_pow_of_le_one q_pos.le (by linarith [q_lt]) (by omega)) (qz_unit _).2
  have hq : q ^ (n + 1) ≤ q := by
    calc q ^ (n + 1) ≤ q ^ 1 := pow_le_pow_of_le_one q_pos.le (by linarith [q_lt]) (by omega)
      _ = q := pow_one q
  have hqp := qpow_pos (n + 1)
  unfold u
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [q_lt]

lemma u_rec (n : ℕ) : u n = (A003499 (n + 1) : ℝ) - 1 / u (n + 1) := by
  have h := HR3 (qz_unit (2 * n + 2)).1 (qz_unit (2 * n + 2)).2
  have e4 : q ^ (2 * n + 2) * q ^ 2 = q ^ (2 * n + 4) := by ring
  have e6 : q ^ (2 * n + 4) * q ^ 2 = q ^ (2 * (n + 1) + 4) := by ring
  rw [e4, e6] at h
  have hH4 := one_le_H zero_le_one le_rfl (qz_unit (2 * n + 4)).1 (qz_unit (2 * n + 4)).2
  have hH6 := one_le_H zero_le_one le_rfl (qz_unit (2 * (n + 1) + 4)).1 (qz_unit (2 * (n + 1) + 4)).2
  have hqp := qpow_pos (n + 1)
  have hq := q_pos
  unfold u
  rw [A_formula, show 2 * (n + 1) + 2 = 2 * n + 4 by ring, h,
    show q ^ (2 * n + 2) = q ^ (n + 1) * q ^ (n + 1) by rw [← pow_add]; ring_nf,
    show q ^ (n + 1 + 1) = q ^ (n + 1) * q by ring]
  field_simp
  ring

lemma tail_dec (n : ℕ) :
    u n - 1 = (((A003499 (n + 1) - 2 : ℤ)) : ℝ) + 1 / (u (n + 1) / (u (n + 1) - 1)) := by
  have := u_gt (n + 1)
  have hne : u (n + 1) ≠ 0 := by linarith
  rw [u_rec n]; push_cast
  field_simp
  ring

lemma tail_dec2 (n : ℕ) :
    u (n + 1) / (u (n + 1) - 1) = ((1 : ℤ) : ℝ) + 1 / (u (n + 1) - 1) := by
  have := u_gt (n + 1)
  have hne : u (n + 1) - 1 ≠ 0 := by linarith
  push_cast
  field_simp
  ring

lemma z_gt (n : ℕ) : 1 < u (n + 1) / (u (n + 1) - 1) := by
  have := u_gt (n + 1)
  rw [one_lt_div (by linarith)]; linarith

lemma tail_h (n : ℕ) : (GenContFract.of (u n - 1)).h = ((A003499 (n + 1) - 2 : ℤ) : ℝ) :=
  (cf_step (z_gt n) (tail_dec n)).1

lemma tail_cf (k : ℕ) : ∀ n : ℕ,
    (GenContFract.of (u n - 1)).partDens.get? (2 * k) = some 1 ∧
    (GenContFract.of (u n - 1)).partDens.get? (2 * k + 1) =
      some ((A003499 (n + k + 2) : ℝ) - 2) := by
  have key : ∀ n m, (GenContFract.of (u n - 1)).partDens.get? (m + 2) =
      (GenContFract.of (u (n + 1) - 1)).partDens.get? m := by
    intro n m
    have s1 := cf_step (z_gt n) (tail_dec n)
    have s2 := cf_step (show 1 < u (n + 1) - 1 by linarith [u_gt (n + 1)]) (tail_dec2 n)
    rw [s1.2.2 (m + 1), s2.2.2 m]
  induction k with
  | zero =>
    intro n
    have s1 := cf_step (z_gt n) (tail_dec n)
    have s2 := cf_step (show 1 < u (n + 1) - 1 by linarith [u_gt (n + 1)]) (tail_dec2 n)
    refine ⟨?_, ?_⟩
    · rw [s1.2.1, s2.1]; simp
    · rw [s1.2.2 0, s2.2.1, tail_h (n + 1)]; push_cast; ring_nf
  | succ k ih =>
    intro n
    obtain ⟨i1, i2⟩ := ih (n + 1)
    refine ⟨?_, ?_⟩
    · rw [show 2 * (k + 1) = 2 * k + 2 by ring, key]; exact i1
    · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, key, i2]
      rw [show n + 1 + k + 2 = n + (k + 1) + 2 by ring]

lemma x_dec : x = ((1 : ℤ) : ℝ) + 1 / (u 0 - 1) := by
  have hu := u_gt 0
  have hM := M_pos zero_le_one le_rfl
  have hH4 := one_le_H zero_le_one le_rfl (qz_unit 4).1 (qz_unit 4).2
  have hq := q_pos
  rw [x_eq]
  unfold u M at *
  norm_num at *
  have hne : H 1 (q ^ 2) / (q * H 1 (q ^ 4)) - 1 ≠ 0 := by linarith
  have hM' : H 1 (q ^ 2) - q * H 1 (q ^ 4) ≠ 0 := by linarith
  field_simp
  ring


end OMA.S_oeis_a174501

open OMA.S_oeis_a174501

theorem OMA.solution : type_of% @OMA.S_oeis_a174501.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have s0 := cf_step (show 1 < u 0 - 1 by linarith [u_gt 0]) x_dec
  refine ⟨?_, ?_⟩
  · rcases m with _ | m
    · unfold oeisTerm
      rw [if_neg (by omega), if_pos (by omega), s0.1]
      simp
    · rw [show 2 * (m + 1 + 1) - 1 = (2 * m + 1) + 2 by omega]
      unfold oeisTerm
      rw [if_neg (by omega), if_neg (by omega), show 2 * m + 1 + 2 - 2 = 2 * m + 1 by omega,
        s0.2.2 (2 * m)]
      exact (tail_cf m 0).1
  · rcases m with _ | m
    · unfold oeisTerm
      rw [if_neg (by omega), if_neg (by omega), show 2 * (0 + 1) - 2 = 0 by omega, s0.2.1,
        tail_h 0]
      push_cast; ring_nf
    · unfold oeisTerm
      rw [if_neg (by omega), if_neg (by omega), show 2 * (m + 1 + 1) - 2 = 2 * m + 1 + 1 by omega,
        s0.2.2 (2 * m + 1), (tail_cf m 0).2]
      ring_nf
