import OMAStatements.S_oeis_a092843

/-!
The summatory function equals the triangular number minus a boundary term:
the sum of φ(⌊n/j⌋) over 1 ≤ j ≤ n. This term is at most n times the
nth harmonic number.
-/

namespace ShiftedTotientSum

open Finset Filter Topology Asymptotics OMA.S_oeis_a092843

private def boundary (n : ℕ) : ℝ := ∑ j ∈ Icc 1 n, ((n / j).totient : ℝ)

private def diff (d : ℕ) : ℝ := (d.totient : ℝ) - (d - 1).totient

private theorem sum_diff (n : ℕ) : ∑ d ∈ n.divisors, diff d = (n : ℝ) - a n := by
  have h : a n = ∑ d ∈ n.divisors, (d - 1).totient := by
    rw [a, sum_filter]
    apply sum_congr rfl
    intro d _
    by_cases hd : 1 < d
    · simp [hd]
    · simp [hd, Nat.sub_eq_zero_of_le (by omega : d ≤ 1)]
  unfold diff
  rw [sum_sub_distrib, h]
  push_cast
  congr 1
  exact_mod_cast Nat.sum_totient n

private theorem boundary_step (n : ℕ) :
    boundary (n + 1) - boundary n = (n + 1 : ℕ) - (a (n + 1) : ℝ) := by
  have old : (∑ j ∈ Icc 1 (n + 1), ((n / j).totient : ℝ)) = boundary n := by
    rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    simp [boundary, Nat.div_eq_of_lt (Nat.lt_succ_self n)]
  have ds : (Icc 1 (n + 1)).filter (fun j => j ∣ n + 1) = (n + 1).divisors := by
    ext j
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨h, by omega⟩
    · rintro ⟨h, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h (Nat.succ_pos n),
        Nat.le_of_dvd (Nat.succ_pos n) h⟩, h⟩
  rw [← sum_diff, ← Nat.sum_div_divisors (n + 1) diff, ← ds, sum_filter, ← old]
  unfold boundary
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  by_cases hj : j ∣ n + 1
  · simp [hj, diff, Nat.succ_div_of_dvd hj]
  · simp [hj, Nat.succ_div_of_not_dvd hj]

private theorem exact_sum (n : ℕ) :
    (∑ k ∈ Icc 1 n, (a k : ℝ)) + boundary n = (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp [boundary]
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have h := boundary_step n
    push_cast at h ⊢
    linarith

private theorem inv_sum (n : ℕ) : ∑ j ∈ Icc 1 n, (j : ℝ)⁻¹ = (harmonic n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, harmonic_succ]
    push_cast
    rfl

private theorem boundary_bound (n : ℕ) : boundary n ≤ (n : ℝ) * (1 + Real.log n) := by
  calc
    boundary n ≤ ∑ j ∈ Icc 1 n, (n : ℝ) * (j : ℝ)⁻¹ := by
      apply sum_le_sum
      intro j _
      rw [← div_eq_mul_inv]
      exact (show (((n / j).totient : ℕ) : ℝ) ≤ (n / j : ℕ) by exact_mod_cast Nat.totient_le _).trans Nat.cast_div_le
    _ = (n : ℝ) * (harmonic n : ℝ) := by rw [← mul_sum, inv_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n) (by positivity)

private theorem negligible : Tendsto (fun n : ℕ => boundary n / (n : ℝ)^2) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ => 1 / (n : ℝ) + Real.log n / n) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).add hlog
  apply squeeze_zero' _ _ ht
  · exact Eventually.of_forall (fun n => div_nonneg (Finset.sum_nonneg (by intros; positivity)) (sq_nonneg _))
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have h : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    calc
      _ ≤ (n : ℝ) * (1 + Real.log n) / (n : ℝ)^2 :=
        div_le_div_of_nonneg_right (boundary_bound n) (sq_nonneg _)
      _ = _ := by field_simp

end ShiftedTotientSum

open Filter Topology Asymptotics Finset ShiftedTotientSum OMA.S_oeis_a092843

theorem OMA.solution : type_of% @OMA.S_oeis_a092843.main := by
  apply (isEquivalent_iff_tendsto_one _).mpr
  · have ht : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ) - 2 * (boundary n / (n : ℝ)^2)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ)) |>.add
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).sub (negligible.const_mul 2)
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hp : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have h := exact_sum n
    change _ = (∑ k ∈ Icc 1 n, (a k : ℝ)) / ((n : ℝ)^2 / 2)
    field_simp
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    positivity
