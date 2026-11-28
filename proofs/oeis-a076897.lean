import OMAStatements.S_oeis_a076897

-- Credit: @oh-meh
open OMA.S_oeis_a076897 Filter Real
open scoped Topology

private theorem errorBound (n : ℕ) (hn : 2 ≤ n) :
    |(a n : ℝ) - 4 * n / 7| ≤ 2 * log n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases htwo : n = 2
    · subst n
      norm_num [a]
      linarith [log_two_gt_d9]
    let q := 3*n/4
    have hq : 2 ≤ q := by dsimp [q]; omega
    have hqn : q < n := by dsimp [q]; omega
    have hs := ih q hqn hq
    have hrec : a n = (n : ℤ) - a q := by
      obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le' hn
      rw [a]
      push_cast
      rfl
    have hr : (a n : ℝ) = (n : ℝ) - (a q : ℝ) := by exact_mod_cast hrec
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hlo : (4 : ℝ)*q ≤ 3*n := by
      exact_mod_cast (show 4*q ≤ 3*n by dsimp [q]; omega)
    have hhi : (3 : ℝ)*n ≤ 4*q + 3 := by
      exact_mod_cast (show 3*n ≤ 4*q + 3 by dsimp [q]; omega)
    have hquot : (q : ℝ)/n ≤ 3/4 := (div_le_iff₀ hn0).2 (by linarith)
    have hlog := log_le_sub_one_of_pos (div_pos hq0 hn0)
    rw [log_div hq0.ne' hn0.ne'] at hlog
    rw [abs_le] at hs ⊢
    constructor <;> linarith [hs.1, hs.2]

theorem OMA.solution : type_of% @OMA.S_oeis_a076897.main := by
  refine ⟨?_, 2, errorBound⟩
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ) / n) atTop (𝓝 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (by
    simpa using hlog.const_mul 2)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  change |(a n : ℝ) / n - 4/7| ≤ 2 * (log n / n)
  rw [show (a n : ℝ)/n - 4/7 = ((a n : ℝ) - 4*n/7)/n by field_simp,
    abs_div, abs_of_pos hp, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (errorBound n hn) hp.le
