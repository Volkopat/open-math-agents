import OMAStatements.S_oeis_a200002

/-! The single-block composition gives the lower bound. For the upper bound,
the sum of the squared block sizes never exceeds the square of their sum. -/
open Filter Topology Finset OMA.S_oeis_a200002

namespace A200002Proof

private theorem coeff_nn (n : ℕ) : 0 ≤ logCoeff n := by
  unfold logCoeff
  positivity

private theorem coeff_le (n : ℕ) : logCoeff n ≤ (4:ℝ)^(n^2) := by
  rcases n with _ | k
  · norm_num [logCoeff]
  · have h₁ : (1:ℝ) ≤ (2:ℝ)^(k+1) := one_le_pow₀ (by norm_num)
    have h₂ : (1:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast Nat.succ_pos k
    have hc : ((k+1).centralBinom : ℝ) ≤ (4:ℝ)^(k+1) := by
      exact_mod_cast Nat.centralBinom_le_four_pow (k+1)
    calc
      logCoeff (k+1) ≤ ((k+1).centralBinom : ℝ)^(k+1) :=
        div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le h₁ h₂)
      _ ≤ ((4:ℝ)^(k+1))^(k+1) := by gcongr
      _ = _ := by rw [← pow_mul, sq]

private theorem prod_bound (l : List ℕ) :
    (l.map logCoeff).prod ≤ (4:ℝ)^(l.sum^2) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    calc
      _ ≤ (4:ℝ)^(a^2) * 4^(l.sum^2) :=
        mul_le_mul (coeff_le a) ih (List.prod_nonneg (by simpa using fun i (_ : i ∈ l) => coeff_nn i)) (by positivity)
      _ = (4:ℝ)^(a^2+l.sum^2) := (pow_add ..).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.zero_le (a*l.sum)])

private theorem summand_nn {n : ℕ} (c : Composition n) :
    0 ≤ (c.blocks.map logCoeff).prod / (c.length.factorial : ℝ) := by
  apply div_nonneg _ (by positivity)
  exact List.prod_nonneg (by simpa using fun i (_ : i ∈ c.blocks) => coeff_nn i)

private theorem upper (n : ℕ) : term n ≤ (2:ℝ)^n * (4:ℝ)^(n^2) := by
  calc
    term n ≤ ∑ _c : Composition n, (4:ℝ)^(n^2) := by
      apply sum_le_sum
      intro c _
      refine (div_le_self ?_ (by exact_mod_cast Nat.factorial_pos c.length)).trans ?_
      · exact List.prod_nonneg (by simpa using fun i (_ : i ∈ c.blocks) => coeff_nn i)
      · simpa using prod_bound c.blocks
    _ = (2:ℝ)^(n-1) * (4:ℝ)^(n^2) := by simp [composition_card]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)) (by positivity)

private theorem lower {n : ℕ} (hn : 0 < n) : logCoeff n ≤ term n := by
  have h := Finset.single_le_sum (fun (c : Composition n) (_ : c ∈ univ) => summand_nn c)
    (mem_univ (Composition.single n hn))
  simpa [term, Composition.single_blocks, Composition.single_length] using h

private theorem log_bounds {n : ℕ} (hn : 4 ≤ n) :
    ((n:ℝ)^2 * Real.log 4 - n * Real.log n - n * Real.log 2 - Real.log n ≤ Real.log (term n)) ∧
    (Real.log (term n) ≤ (n:ℝ)^2 * Real.log 4 + n * Real.log 2) := by
  have hnpos : 0 < n := by omega
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hnpos
  have hb : 0 < (n.centralBinom : ℝ) := by exact_mod_cast Nat.centralBinom_pos n
  have hc : 0 < logCoeff n := by unfold logCoeff; positivity
  have ht := hc.trans_le (lower hnpos)
  have hbinom : (4:ℝ)^n ≤ (n:ℝ) * (n.centralBinom:ℝ) := by
    exact_mod_cast (Nat.four_pow_lt_mul_centralBinom n hn).le
  have h₁ := Real.log_le_log (by positivity) hbinom
  rw [Real.log_pow, Real.log_mul hn'.ne' hb.ne'] at h₁
  have h₂ := Real.log_le_log hc (lower hnpos)
  rw [logCoeff, Real.log_div (pow_ne_zero _ hb.ne') (by positivity),
    Real.log_mul (by positivity) hn'.ne', Real.log_pow, Real.log_pow] at h₂
  have h₃ := Real.log_le_log ht (upper n)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Nat.cast_pow] at h₃
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h₁ hn'.le]
  · linarith

private theorem growth :
    Tendsto (fun n : ℕ => (term n)^(1/(n:ℝ)^2)) atTop (𝓝 4) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have lo := (((tendsto_const_nhds (x:=Real.log 4)).sub hratio).sub
    ((tendsto_const_nhds (x:=Real.log 2)).mul hi)).sub (hratio.mul hi)
  have up := (tendsto_const_nhds (x:=Real.log 4)).add ((tendsto_const_nhds (x:=Real.log 2)).mul hi)
  have hlog : Tendsto (fun n : ℕ => Real.log (term n)/(n:ℝ)^2) atTop (𝓝 (Real.log 4)) := by
    simp only [mul_zero, sub_zero, add_zero] at lo up
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lo up
    · filter_upwards [eventually_ge_atTop (4:ℕ)] with n hn
      have hpos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
      calc
        _ = ((n:ℝ)^2 * Real.log 4 - n * Real.log n - n * Real.log 2 - Real.log n)/(n:ℝ)^2 := by
          field_simp
        _ ≤ _ := div_le_div_of_nonneg_right (log_bounds hn).1 (sq_nonneg _)
    · filter_upwards [eventually_ge_atTop (4:ℕ)] with n hn
      have hpos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
      calc
        _ ≤ ((n:ℝ)^2 * Real.log 4 + n * Real.log 2)/(n:ℝ)^2 :=
          div_le_div_of_nonneg_right (log_bounds hn).2 (sq_nonneg _)
        _ = _ := by
          field_simp

  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  rw [Real.exp_log (by norm_num : 0 < (4:ℝ))] at hexp
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hpos : 0 < (n:ℝ) := by exact_mod_cast hn
  have hb : 0 < (n.centralBinom : ℝ) := by exact_mod_cast Nat.centralBinom_pos n
  have hc : 0 < logCoeff n := by unfold logCoeff; positivity
  simp [Real.rpow_def_of_pos (hc.trans_le (lower hn)), div_eq_mul_inv]

end A200002Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a200002.main := A200002Proof.growth
