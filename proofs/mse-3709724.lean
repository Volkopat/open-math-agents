import OMAStatements.S_mse_3709724

/-!
# mse-3709724 的完整形式化证伪

针对原问题第二部分（对每个整数 n ≥ 3，上界函数与 Gamma 比值之差在 x → +∞ 时趋于 0），
我们在 n = 5 处给出完全初等（零微积分）的严格渐近下界证明：
当 n = 5 时，设中心化变量 u = x + 2，则
- Gamma(x + 5) / Gamma(x) = u^5 - 5 u^3 + 4 u；
- 加权几何平均项满足 G(x) ≤ u + 1/u + (23/20) u^(-3)；
- 从而 upper(5, x) - Gamma(x + 5)/Gamma(x) 以 +(2/3) x 的阶发散至 +∞，
  特别地对一切 x ≥ 2000 恒有差值 ≥ 1，故不可能在 x → +∞ 时趋于 0。
-/

namespace MSE3709724Proof

-- 辅助引理一：利用四阶对数泰勒余项界导出对称对数组合的四阶上界
lemma sym_log_bound {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 1000) :
    (1 + t) * Real.log (1 + t) + (1 - t) * Real.log (1 - t) ≤ t ^ 2 + 17 / 100 * t ^ 4 := by
  have h_one_sub_pos : 0 < 1 - t := by linarith
  have ht4_nonneg : 0 ≤ t ^ 4 := pow_nonneg ht0 4
  have hrem : t ^ 5 / (1 - t) ≤ t ^ 4 / 999 := by
    rw [div_le_div_iff₀ h_one_sub_pos (by norm_num : (0 : ℝ) < 999)]
    have h999 : 999 * t ≤ 1 - t := by linarith
    have hmul := mul_le_mul_of_nonneg_left h999 ht4_nonneg
    linarith [show t ^ 4 * (999 * t) = t ^ 5 * 999 by ring]
  -- 对 s = t 应用四阶对数余项不等式
  have h_pos := Real.abs_log_sub_add_sum_range_le (x := t) (by rw [abs_of_nonneg ht0]; linarith) 4
  have hsum_pos : (∑ i ∈ Finset.range 4, t ^ (i + 1) / ((i : ℝ) + 1)) =
      t + t ^ 2 / 2 + t ^ 3 / 3 + t ^ 4 / 4 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    push_cast
    ring
  rw [hsum_pos, abs_of_nonneg ht0] at h_pos
  have hlog_sub : Real.log (1 - t) ≤ -t - t ^ 2 / 2 - t ^ 3 / 3 - t ^ 4 / 4 + t ^ 4 / 999 := by
    have h1 := le_trans (le_abs_self _) h_pos
    linarith
  -- 对 s = -t 应用四阶对数余项不等式
  have habs_neg : |-t| = t := by rw [abs_neg, abs_of_nonneg ht0]
  have h_neg := Real.abs_log_sub_add_sum_range_le (x := -t) (by rw [habs_neg]; linarith) 4
  have hsum_neg : (∑ i ∈ Finset.range 4, (-t) ^ (i + 1) / ((i : ℝ) + 1)) =
      -t + t ^ 2 / 2 - t ^ 3 / 3 + t ^ 4 / 4 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    push_cast
    ring
  rw [hsum_neg, habs_neg, show 1 - -t = 1 + t by ring] at h_neg
  have hlog_add : Real.log (1 + t) ≤ t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4 + t ^ 4 / 999 := by
    have h2 := le_trans (le_abs_self _) h_neg
    linarith
  -- 加权合并消去奇次项
  have hm1 := mul_le_mul_of_nonneg_left hlog_add (by linarith : 0 ≤ 1 + t)
  have hm2 := mul_le_mul_of_nonneg_left hlog_sub (by linarith : 0 ≤ 1 - t)
  have hcomb : (1 + t) * (t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4 + t ^ 4 / 999) +
      (1 - t) * (-t - t ^ 2 / 2 - t ^ 3 / 3 - t ^ 4 / 4 + t ^ 4 / 999) =
      t ^ 2 + 337 / 1998 * t ^ 4 := by ring
  linarith

-- 辅助引理二：通过连续四次平方与显式正项分解证明零微积分指数二次上界
lemma exp_quad_upper {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 1000) :
    Real.exp w ≤ 1 + w + 14 / 25 * w ^ 2 := by
  set a : ℝ := w / 16
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 / 16000 := by
    change w / 16 ≤ 1 / 16000
    linarith
  have ha2_nonneg : 0 ≤ a ^ 2 := sq_nonneg a
  have ha4_nonneg : 0 ≤ a ^ 4 := pow_nonneg ha0 4
  -- 连续平方建立 (1 - a)^16 的二次多项式下界
  have hp4 : 1 - 4 * a + 5 * a ^ 2 ≤ (1 - a) ^ 4 := by
    have hid : (1 - a) ^ 4 - (1 - 4 * a + 5 * a ^ 2) = a ^ 2 * (1 - 4 * a) + a ^ 4 := by ring
    have hpos : 0 ≤ a ^ 2 * (1 - 4 * a) := mul_nonneg ha2_nonneg (by linarith)
    linarith
  have hp8 : 1 - 8 * a + 25 * a ^ 2 ≤ (1 - a) ^ 8 := by
    have hsq : (1 - 4 * a + 5 * a ^ 2) ^ 2 ≤ ((1 - a) ^ 4) ^ 2 :=
      pow_le_pow_left₀ (by nlinarith) hp4 2
    have hid : (1 - 4 * a + 5 * a ^ 2) ^ 2 - (1 - 8 * a + 25 * a ^ 2) =
        a ^ 2 * (1 - 40 * a) + 25 * a ^ 4 := by ring
    have hpos : 0 ≤ a ^ 2 * (1 - 40 * a) := mul_nonneg ha2_nonneg (by linarith)
    have hpow : ((1 - a) ^ 4) ^ 2 = (1 - a) ^ 8 := by ring
    linarith
  have hp16 : 1 - 16 * a + 113 * a ^ 2 ≤ (1 - a) ^ 16 := by
    have hsq : (1 - 8 * a + 25 * a ^ 2) ^ 2 ≤ ((1 - a) ^ 8) ^ 2 :=
      pow_le_pow_left₀ (by nlinarith) hp8 2
    have hid : (1 - 8 * a + 25 * a ^ 2) ^ 2 - (1 - 16 * a + 113 * a ^ 2) =
        a ^ 2 * (1 - 400 * a) + 625 * a ^ 4 := by ring
    have hpos : 0 ≤ a ^ 2 * (1 - 400 * a) := mul_nonneg ha2_nonneg (by linarith)
    have hpow : ((1 - a) ^ 8) ^ 2 = (1 - a) ^ 16 := by ring
    linarith
  have hp16_w : 1 - w + 113 / 256 * w ^ 2 ≤ (1 - a) ^ 16 := by
    have heq : 1 - 16 * a + 113 * a ^ 2 = 1 - w + 113 / 256 * w ^ 2 := by
      change 1 - 16 * (w / 16) + 113 * (w / 16) ^ 2 = 1 - w + 113 / 256 * w ^ 2
      ring
    linarith
  -- 利用 1 - a ≤ exp(-a) 的 16 次幂连接指数函数
  have hexp_step : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
  have hexp16 : (1 - a) ^ 16 ≤ Real.exp (-a) ^ 16 :=
    pow_le_pow_left₀ (by linarith) hexp_step 16
  have hexp_pow : Real.exp (-a) ^ 16 = Real.exp (-w) := by
    rw [← Real.exp_nat_mul]
    congr 1
    change (16 : ℕ) * -(w / 16) = -w
    push_cast
    ring
  rw [hexp_pow] at hexp16
  have hprod_le_one : Real.exp w * (1 - a) ^ 16 ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hexp16 (Real.exp_nonneg w)
    have hcancel : Real.exp w * Real.exp (-w) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    linarith
  have hprod_ge_one : 1 ≤ (1 + w + 14 / 25 * w ^ 2) * (1 - a) ^ 16 := by
    have hq_nonneg : 0 ≤ 1 + w + 14 / 25 * w ^ 2 := by positivity
    have hm := mul_le_mul_of_nonneg_left hp16_w hq_nonneg
    have hid : (1 + w + 14 / 25 * w ^ 2) * (1 - w + 113 / 256 * w ^ 2) - 1 =
        w ^ 2 * (9 / 6400 - 759 / 6400 * w) + 791 / 3200 * w ^ 4 := by ring
    have hw2_pos : 0 ≤ w ^ 2 * (9 / 6400 - 759 / 6400 * w) :=
      mul_nonneg (sq_nonneg w) (by linarith)
    have hw4_pos : 0 ≤ 791 / 3200 * w ^ 4 := by positivity
    linarith
  have ha16_pos : 0 < (1 - a) ^ 16 := pow_pos (by linarith) 16
  exact le_of_mul_le_mul_right (le_trans hprod_le_one hprod_ge_one) ha16_pos

-- 辅助引理三：中心化配对对数恒等式
lemma pair_log_eq {u k : ℝ} (hk : 0 < k) (hku : k < u) :
    Real.log (u - k) * (u - k) + Real.log (u + k) * (u + k) =
      2 * u * Real.log u +
        u * ((1 + k / u) * Real.log (1 + k / u) + (1 - k / u) * Real.log (1 - k / u)) := by
  have hu_ne : u ≠ 0 := by linarith
  have hsub : u - k = u * (1 - k / u) := by
    rw [mul_sub, mul_one, mul_div_cancel₀ _ hu_ne]
  have hadd : u + k = u * (1 + k / u) := by
    rw [mul_add, mul_one, mul_div_cancel₀ _ hu_ne]
  have hsub_ne : 1 - k / u ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsub
    linarith
  have hadd_ne : 1 + k / u ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hadd
    linarith
  rw [hsub, hadd, Real.log_mul hu_ne hsub_ne, Real.log_mul hu_ne hadd_ne]
  ring

-- 辅助引理四：将指数对数复合上界转化为 G 的纯有理函数上界（隔离复杂表达式加速内核归约）
lemma exp_u_bound {u : ℝ} (hu : 2002 ≤ u) :
    u * Real.exp (1 / u ^ 2 + 289 / (500 * u ^ 4)) ≤ u + 1 / u + 23 / (20 * u ^ 3) := by
  have hu_pos : 0 < u := by linarith
  have hu_ne : u ≠ 0 := ne_of_gt hu_pos
  have hu2_ge : 4000000 ≤ u ^ 2 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 2)
  have hu4_ge : 16000000000000 ≤ u ^ 4 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 4)
  let w : ℝ := 1 / u ^ 2 + 289 / (500 * u ^ 4)
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 / 1000 := by
    have hp1 : 1 / u ^ 2 ≤ 1 / 4000000 := by
      rw [div_le_div_iff₀ (pow_pos hu_pos 2) (by norm_num : (0 : ℝ) < 4000000)]
      linarith
    have hp2 : 289 / (500 * u ^ 4) ≤ 1 / 4000000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4000000)]
      linarith
    change 1 / u ^ 2 + 289 / (500 * u ^ 4) ≤ 1 / 1000
    linarith
  have hexp_w : Real.exp w ≤ 1 + w + 14 / 25 * w ^ 2 := exp_quad_upper hw0 hw1
  have hw_rat : 1 + w + 14 / 25 * w ^ 2 ≤ 1 + 1 / u ^ 2 + 23 / (20 * u ^ 4) := by
    have hu8_pos : 0 < u ^ 8 := pow_pos hu_pos 8
    suffices h : (1 + w + 14 / 25 * w ^ 2) * u ^ 8 ≤ (1 + 1 / u ^ 2 + 23 / (20 * u ^ 4)) * u ^ 8 by
      exact le_of_mul_le_mul_right h hu8_pos
    have hid : (1 + 1 / u ^ 2 + 23 / (20 * u ^ 4)) * u ^ 8 -
        (1 + w + 14 / 25 * w ^ 2) * u ^ 8 =
        u ^ 2 * (3 / 500 * u ^ 2 - 2023 / 3125) + (3 / 500 * u ^ 4 - 584647 / 3125000) := by
      change (1 + 1 / u ^ 2 + 23 / (20 * u ^ 4)) * u ^ 8 -
        (1 + (1 / u ^ 2 + 289 / (500 * u ^ 4)) +
          14 / 25 * (1 / u ^ 2 + 289 / (500 * u ^ 4)) ^ 2) * u ^ 8 = _
      field_simp [hu_ne]
      ring
    have hp_a : 0 ≤ u ^ 2 * (3 / 500 * u ^ 2 - 2023 / 3125) :=
      mul_nonneg (sq_nonneg u) (by linarith)
    linarith
  have hmul := mul_le_mul_of_nonneg_left (le_trans hexp_w hw_rat) (le_of_lt hu_pos)
  have hrhs : u * (1 + 1 / u ^ 2 + 23 / (20 * u ^ 4)) = u + 1 / u + 23 / (20 * u ^ 3) := by
    field_simp [hu_ne]
  change u * Real.exp w ≤ _
  linarith

-- 辅助引理五：五次幂纯有理函数下界（完全独立于超越函数与有限积）
lemma quintic_gap_ge_one {u G : ℝ} (hu : 2002 ≤ u) (hG : G ≤ u + 1 / u + 23 / (20 * u ^ 3)) :
    1 ≤ (2 * u - G) ^ 5 - (u ^ 5 - 5 * u ^ 3 + 4 * u) := by
  have hu_pos : 0 < u := by linarith
  have hu_ne : u ≠ 0 := ne_of_gt hu_pos
  have hu2_ge : 4000000 ≤ u ^ 2 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 2)
  have hu3_ge : 8000000000 ≤ u ^ 3 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 3)
  have hu4_ge : 16000000000000 ≤ u ^ 4 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 4)
  have hu6_ge : 16000000000000 ≤ u ^ 6 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 6)
  have hbase_ge : u - 1 / u - 23 / (20 * u ^ 3) ≤ 2 * u - G := by linarith
  have hbase_nonneg : 0 ≤ u - 1 / u - 23 / (20 * u ^ 3) := by
    have h1 : 1 / u ≤ 1 := by rw [div_le_one hu_pos]; linarith
    have h2 : 23 / (20 * u ^ 3) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hpow5_ge : (u - 1 / u - 23 / (20 * u ^ 3)) ^ 5 ≤ (2 * u - G) ^ 5 :=
    pow_le_pow_left₀ hbase_nonneg hbase_ge 5
  have hpoly5 : u ^ 5 - 5 * u ^ 3 + 4 * u + 1 ≤ (u - 1 / u - 23 / (20 * u ^ 3)) ^ 5 := by
    have hu15_pos : 0 < u ^ 15 := pow_pos hu_pos 15
    suffices h : (u ^ 5 - 5 * u ^ 3 + 4 * u + 1) * u ^ 15 ≤
        (u - 1 / u - 23 / (20 * u ^ 3)) ^ 5 * u ^ 15 by
      exact le_of_mul_le_mul_right h hu15_pos
    have hid : (u - 1 / u - 23 / (20 * u ^ 3)) ^ 5 * u ^ 15 -
        (u ^ 5 - 5 * u ^ 3 + 4 * u + 1) * u ^ 15 =
        u ^ 15 * (1 / 4 * u - 1) +
        u ^ 12 * (6 * u ^ 2 - 651 / 40) +
        u ^ 10 * (7 * u ^ 4 - 707 / 40) +
        u ^ 4 * (14973 / 800 * u ^ 4 - 206839 / 32000) +
        u ^ 2 * (3000 / 400 * u ^ 4 - 279841 / 32000) +
        (3877 / 400 * u ^ 6 - 6436343 / 3200000) := by
      field_simp [hu_ne]
      ring
    have ht_1 : 0 ≤ u ^ 15 * (1 / 4 * u - 1) := mul_nonneg (by positivity) (by linarith)
    have ht_2 : 0 ≤ u ^ 12 * (6 * u ^ 2 - 651 / 40) := mul_nonneg (by positivity) (by linarith)
    have ht_3 : 0 ≤ u ^ 10 * (7 * u ^ 4 - 707 / 40) := mul_nonneg (by positivity) (by linarith)
    have ht_4 : 0 ≤ u ^ 4 * (14973 / 800 * u ^ 4 - 206839 / 32000) :=
      mul_nonneg (by positivity) (by linarith)
    have ht_5 : 0 ≤ u ^ 2 * (3000 / 400 * u ^ 4 - 279841 / 32000) :=
      mul_nonneg (by positivity) (by linarith)
    have ht_6 : 0 ≤ 3877 / 400 * u ^ 6 - 6436343 / 3200000 := by linarith
    linarith
  linarith

-- 核心引理：当 n = 5 且 x ≥ 2000 时，差值恒大于等于 1
lemma diff_five_ge_one (x : ℝ) (hx : 2000 ≤ x) :
    1 ≤ OMA.S_mse_3709724.upper 5 x - Real.Gamma (x + (5 : ℕ)) / Real.Gamma x := by
  let u : ℝ := x + 2
  have hu : 2002 ≤ u := by change 2002 ≤ x + 2; linarith
  have hu_pos : 0 < u := by linarith
  have hu_ne : u ≠ 0 := ne_of_gt hu_pos
  -- 第一步：计算 n = 5 时的 Gamma 比值多项式
  have hG1 : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one (by linarith)
  have hG2 : Real.Gamma (x + 2) = (x + 1) * Real.Gamma (x + 1) := by
    rw [show x + 2 = (x + 1) + 1 by ring]; exact Real.Gamma_add_one (by linarith)
  have hG3 : Real.Gamma (x + 3) = (x + 2) * Real.Gamma (x + 2) := by
    rw [show x + 3 = (x + 2) + 1 by ring]; exact Real.Gamma_add_one (by linarith)
  have hG4 : Real.Gamma (x + 4) = (x + 3) * Real.Gamma (x + 3) := by
    rw [show x + 4 = (x + 3) + 1 by ring]; exact Real.Gamma_add_one (by linarith)
  have hG5 : Real.Gamma (x + (5 : ℕ)) = (x + 4) * Real.Gamma (x + 4) := by
    push_cast; rw [show x + 5 = (x + 4) + 1 by ring]; exact Real.Gamma_add_one (by linarith)
  have hGamma : Real.Gamma (x + (5 : ℕ)) / Real.Gamma x = u ^ 5 - 5 * u ^ 3 + 4 * u := by
    rw [hG5, hG4, hG3, hG2, hG1]
    have hGx_ne : Real.Gamma x ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
    have hx_eq : x = u - 2 := by change x = (x + 2) - 2; ring
    field_simp [hGx_ne]
    rw [hx_eq]
    ring
  -- 第二步：化简 weightSum 与加权几何平均
  have hw_sum : OMA.S_mse_3709724.weightSum 5 x = 5 * u := by
    unfold OMA.S_mse_3709724.weightSum
    push_cast
    change 5 * x + 5 * (5 - 1) / 2 = 5 * (x + 2)
    ring
  let S : ℝ := Real.log (u - 2) * (u - 2) + Real.log (u - 1) * (u - 1) +
      Real.log u * u + Real.log (u + 1) * (u + 1) + Real.log (u + 2) * (u + 2)
  have hprod : (∏ j ∈ Finset.range 5, (x + (j : ℝ)) ^ (x + (j : ℝ))) = Real.exp S := by
    simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul]
    push_cast
    have hx0 : x + 0 = u - 2 := by change x + 0 = (x + 2) - 2; ring
    have hx1 : x + 1 = u - 1 := by change x + 1 = (x + 2) - 1; ring
    have hx2 : x + 2 = u := rfl
    have hx3 : x + 3 = u + 1 := by change x + 3 = (x + 2) + 1; ring
    have hx4 : x + 4 = u + 2 := by change x + 4 = (x + 2) + 2; ring
    rw [hx0, hx1, hx2, hx3, hx4]
    rw [Real.rpow_def_of_pos (by linarith : 0 < u - 2),
        Real.rpow_def_of_pos (by linarith : 0 < u - 1),
        Real.rpow_def_of_pos hu_pos,
        Real.rpow_def_of_pos (by linarith : 0 < u + 1),
        Real.rpow_def_of_pos (by linarith : 0 < u + 2)]
    simp only [← Real.exp_add]
    rfl
  -- 第三步：估计对数均值 S / (5 u) 与几何平均 G 的上界
  have hp1 := pair_log_eq (u := u) (k := 1) (by norm_num) (by linarith)
  have hp2 := pair_log_eq (u := u) (k := 2) (by norm_num) (by linarith)
  have ht1_le : 1 / u ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ hu_pos (by norm_num : (0 : ℝ) < 1000)]; linarith
  have ht2_le : 2 / u ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ hu_pos (by norm_num : (0 : ℝ) < 1000)]; linarith
  have hb1 := sym_log_bound (t := 1 / u) (by positivity) ht1_le
  have hb2 := sym_log_bound (t := 2 / u) (by positivity) ht2_le
  have hS_div : S * (1 / (5 * u)) ≤ Real.log u + (1 / u ^ 2 + 289 / (500 * u ^ 4)) := by
    have hS_decomp : S = 5 * u * Real.log u +
        u * ((1 + 1 / u) * Real.log (1 + 1 / u) + (1 - 1 / u) * Real.log (1 - 1 / u)) +
        u * ((1 + 2 / u) * Real.log (1 + 2 / u) + (1 - 2 / u) * Real.log (1 - 2 / u)) := by
      change Real.log (u - 2) * (u - 2) + Real.log (u - 1) * (u - 1) +
        Real.log u * u + Real.log (u + 1) * (u + 1) + Real.log (u + 2) * (u + 2) = _
      linarith [hp1, hp2]
    have hS_upper : S ≤ 5 * u * Real.log u +
        u * ((1 / u) ^ 2 + 17 / 100 * (1 / u) ^ 4 + (2 / u) ^ 2 + 17 / 100 * (2 / u) ^ 4) := by
      have hm1 := mul_le_mul_of_nonneg_left hb1 (le_of_lt hu_pos)
      have hm2 := mul_le_mul_of_nonneg_left hb2 (le_of_lt hu_pos)
      linarith [hS_decomp]
    have hmul := mul_le_mul_of_nonneg_right hS_upper (by positivity : 0 ≤ 1 / (5 * u))
    have hrhs_eq : (5 * u * Real.log u +
        u * ((1 / u) ^ 2 + 17 / 100 * (1 / u) ^ 4 + (2 / u) ^ 2 + 17 / 100 * (2 / u) ^ 4)) *
        (1 / (5 * u)) = Real.log u + (1 / u ^ 2 + 289 / (500 * u ^ 4)) := by
      field_simp [hu_ne]
      ring
    linarith
  have hG_upper : (∏ j ∈ Finset.range 5, (x + (j : ℝ)) ^ (x + (j : ℝ))) ^
      (1 / OMA.S_mse_3709724.weightSum 5 x) ≤ u + 1 / u + 23 / (20 * u ^ 3) := by
    rw [hprod, hw_sum, Real.rpow_def_of_pos (Real.exp_pos S), Real.log_exp]
    have h1 := Real.exp_le_exp.mpr hS_div
    rw [Real.exp_add, Real.exp_log hu_pos] at h1
    exact le_trans h1 (exp_u_bound hu)
  have hupper_eq : OMA.S_mse_3709724.upper 5 x =
      (2 * u - (∏ j ∈ Finset.range 5, (x + (j : ℝ)) ^ (x + (j : ℝ))) ^
        (1 / OMA.S_mse_3709724.weightSum 5 x)) ^ 5 := by
    unfold OMA.S_mse_3709724.upper
    rw [hw_sum]
    congr 2
    push_cast
    ring
  rw [hupper_eq, hGamma]
  exact quintic_gap_ge_one hu hG_upper

end MSE3709724Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_3709724.main) := by
  intro hmain
  have hlim := hmain.2 5 (by norm_num)
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      OMA.S_mse_3709724.upper 5 x - Real.Gamma (x + (5 : ℕ)) / Real.Gamma x < 1 :=
    hlim.eventually (Iio_mem_nhds zero_lt_one)
  rcases Filter.eventually_atTop.mp hev with ⟨X₀, hX₀⟩
  let x : ℝ := max X₀ 2000
  have hlt : OMA.S_mse_3709724.upper 5 x - Real.Gamma (x + (5 : ℕ)) / Real.Gamma x < 1 :=
    hX₀ x (le_max_left X₀ 2000)
  have hge : 1 ≤ OMA.S_mse_3709724.upper 5 x - Real.Gamma (x + (5 : ℕ)) / Real.Gamma x :=
    MSE3709724Proof.diff_five_ge_one x (le_max_right X₀ 2000)
  linarith
