import OMAStatements.S_oeis_a078111

-- Problem: A078111: Greathouse's asymptotic for the expression inside the floor
-- Upstream: formal-conjectures statements/oeis-a078111.lean:0 (declaration OMA.S_oeis_a078111.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Topology

namespace OMA.Aux078111

lemma polyb (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    |2 / 3 * t ^ 3 + 1 / 18 * t ^ 4 - 2 / 9 * t ^ 5 + 2 / 9 * t ^ 6| ≤ t ^ 3 := by
  have ht3 : 0 < t ^ 3 := by positivity
  have e : 2 / 3 * t ^ 3 + 1 / 18 * t ^ 4 - 2 / 9 * t ^ 5 + 2 / 9 * t ^ 6
      = t ^ 3 * (2 / 3 + 1 / 18 * t - 2 / 9 * t ^ 2 + 2 / 9 * t ^ 3) := by ring
  rw [e, abs_mul, abs_of_pos ht3]
  have h2 : t ^ 2 ≤ 1 / 4 := by
    have : t ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ ht.le ht2 2
    linarith
  have h3 : t ^ 3 ≤ 1 / 8 := by
    have : t ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ ht.le ht2 3
    linarith
  have h20 : 0 ≤ t ^ 2 := by positivity
  have : |2 / 3 + 1 / 18 * t - 2 / 9 * t ^ 2 + 2 / 9 * t ^ 3| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  calc t ^ 3 * |2 / 3 + 1 / 18 * t - 2 / 9 * t ^ 2 + 2 / 9 * t ^ 3| ≤ t ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left this ht3.le
    _ = t ^ 3 := mul_one _

lemma alg (t u0 δ R W : ℝ) (hu0 : u0 = -t + 2 * t ^ 2 / 3) (hW : W = δ * (1 + u0 + δ / 2) + R) :
    (1 + t) ^ 2 * (1 + (u0 + δ) + (u0 + δ) ^ 2 / 2 + R) - 1 - t - t ^ 2 / 6
      = (2 / 3 * t ^ 3 + 1 / 18 * t ^ 4 - 2 / 9 * t ^ 5 + 2 / 9 * t ^ 6) + (1 + t) ^ 2 * W := by
  subst hu0 hW
  ring

set_option maxHeartbeats 1000000 in
lemma core (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    |(1 + t) ^ 2 * Real.exp (2 / t * Real.log (1 + t) - 2) - 1 - t - t ^ 2 / 6| ≤ 24 * t ^ 3 := by
  have hlog := Real.abs_log_sub_add_sum_range_le (x := -t) (by rw [abs_neg, abs_of_pos ht]; linarith) 3
  rw [abs_neg, abs_of_pos ht] at hlog
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add] at hlog
  norm_num at hlog
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hb : t ^ 4 / (1 - t) ≤ 2 * t ^ 4 := by
    rw [div_le_iff₀ h1t]
    have : 0 ≤ t ^ 4 := by positivity
    nlinarith
  have hlog2 := abs_le.mp (hlog.trans hb)
  set L := Real.log (1 + t) with hL
  set u := 2 / t * L - 2 with hu
  set u0 := -t + 2 * t ^ 2 / 3 with hu0
  set δ := u - u0 with hδ
  have hδeq : δ = (2 / t) * (L - t + t ^ 2 / 2 - t ^ 3 / 3) := by
    rw [hδ, hu, hu0]; field_simp; ring
  have ht3 : 0 < t ^ 3 := by positivity
  have hδabs : |δ| ≤ 4 * t ^ 3 := by
    rw [hδeq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / t)]
    have hx : |L - t + t ^ 2 / 2 - t ^ 3 / 3| ≤ 2 * t ^ 4 := by
      rw [abs_le]; constructor <;> linarith [hlog2.1, hlog2.2]
    calc 2 / t * |L - t + t ^ 2 / 2 - t ^ 3 / 3| ≤ 2 / t * (2 * t ^ 4) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
      _ = 4 * t ^ 3 := by field_simp; ring
  have hδ2 := abs_le.mp hδabs
  have ht3b : t ^ 3 ≤ 1 / 8 := by
    have : t ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ ht.le ht2 3
    linarith
  have hu0b : -t ≤ u0 ∧ u0 ≤ 0 := by
    rw [hu0]; constructor <;> nlinarith
  have hueq : u = u0 + δ := by rw [hδ]; ring
  have huabs : |u| ≤ 2 * t := by
    rw [abs_le, hueq]
    have : 4 * t ^ 3 ≤ t := by nlinarith
    constructor <;> linarith [hδ2.1, hδ2.2, hu0b.1, hu0b.2]
  have hu1 : |u| ≤ 1 := by linarith
  have hexp := Real.exp_bound hu1 (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hexp
  norm_num [Nat.factorial] at hexp
  set R := Real.exp u - (1 + u + u ^ 2 / 2) with hR
  have hRabs : |R| ≤ 2 * t ^ 3 := by
    have h1 : |R| ≤ |u| ^ 3 * (4 / 18) := by
      have : R = Real.exp u - (1 + u + u ^ 2 / 2) := hR
      rw [this]
      convert hexp using 2 <;> ring
    have h2 : |u| ^ 3 ≤ (2 * t) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) huabs 3
    nlinarith
  have hexpeq : Real.exp u = 1 + u + u ^ 2 / 2 + R := by rw [hR]; ring
  rw [hexpeq, hueq]
  set W := δ * (1 + u0 + δ / 2) + R with hW
  have hWabs : |W| ≤ 7 * t ^ 3 := by
    have ha : |1 + u0 + δ / 2| ≤ 5 / 4 := by
      rw [abs_le]; constructor <;> linarith [hδ2.1, hδ2.2, hu0b.1, hu0b.2]
    have hm : |δ * (1 + u0 + δ / 2)| ≤ 4 * t ^ 3 * (5 / 4) := by
      rw [abs_mul]
      exact mul_le_mul hδabs ha (abs_nonneg _) (by positivity)
    calc |W| ≤ |δ * (1 + u0 + δ / 2)| + |R| := abs_add_le _ _
      _ ≤ 7 * t ^ 3 := by linarith
  have hsq : |(1 + t) ^ 2| ≤ 9 / 4 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  have hprod : |(1 + t) ^ 2 * W| ≤ 9 / 4 * (7 * t ^ 3) := by
    rw [abs_mul]
    exact mul_le_mul hsq hWabs (abs_nonneg _) (by norm_num)
  have hpoly := polyb t ht ht2
  have hfinal : (1 + t) ^ 2 * (1 + (u0 + δ) + (u0 + δ) ^ 2 / 2 + R) - 1 - t - t ^ 2 / 6
      = (2 / 3 * t ^ 3 + 1 / 18 * t ^ 4 - 2 / 9 * t ^ 5 + 2 / 9 * t ^ 6) + (1 + t) ^ 2 * W :=
    alg t u0 δ R W hu0 hW
  rw [hfinal]
  calc _ ≤ |2 / 3 * t ^ 3 + 1 / 18 * t ^ 4 - 2 / 9 * t ^ 5 + 2 / 9 * t ^ 6| + |(1 + t) ^ 2 * W| :=
        abs_add_le _ _
    _ ≤ 24 * t ^ 3 := by linarith

lemma bound (n : ℕ) (hn : 4 ≤ n) :
    |OMA.S_oeis_a078111.quotient n / Real.exp 2 - ((n : ℝ) ^ 2 + 2 * n + 2 / 3)| ≤ 192 / (n : ℝ) := by
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set t : ℝ := 2 / n with ht
  have htpos : 0 < t := by positivity
  have ht2 : t ≤ 1 / 2 := by
    rw [ht, div_le_iff₀ hn0]; linarith
  have hc := core t htpos ht2
  have hnt : (n : ℝ) = 2 / t := by rw [ht]; field_simp
  have h1t : (1 : ℝ) + t = ((n : ℝ) + 2) / n := by rw [ht]; field_simp
  have hpos : (0 : ℝ) < 1 + t := by linarith
  have hq : OMA.S_oeis_a078111.quotient n / Real.exp 2
      = (n : ℝ) ^ 2 * ((1 + t) ^ 2 * Real.exp (2 / t * Real.log (1 + t) - 2)) := by
    unfold OMA.S_oeis_a078111.quotient
    rw [Real.exp_sub, ← hnt, Real.exp_nat_mul, Real.exp_log hpos, h1t, pow_add, div_pow, div_pow]
    field_simp
  rw [hq]
  have he : (n : ℝ) ^ 2 * ((1 + t) ^ 2 * Real.exp (2 / t * Real.log (1 + t) - 2))
      - ((n : ℝ) ^ 2 + 2 * n + 2 / 3)
      = (n : ℝ) ^ 2 * ((1 + t) ^ 2 * Real.exp (2 / t * Real.log (1 + t) - 2) - 1 - t - t ^ 2 / 6) := by
    have e1 : (n : ℝ) ^ 2 * t = 2 * n := by rw [ht]; field_simp
    have e2 : (n : ℝ) ^ 2 * t ^ 2 = 4 := by rw [ht]; field_simp; norm_num
    linear_combination e1 + e2 / 6
  rw [he, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
  calc (n : ℝ) ^ 2 * _ ≤ (n : ℝ) ^ 2 * (24 * t ^ 3) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 192 / (n : ℝ) := by rw [ht]; field_simp; ring

end OMA.Aux078111

theorem OMA.solution : type_of% @OMA.S_oeis_a078111.main := by
  have hlim : Tendsto (fun n : ℕ => (192 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 192
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 4] with n hn
  rw [Real.norm_eq_abs]
  exact OMA.Aux078111.bound n hn
