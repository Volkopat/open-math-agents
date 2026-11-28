import OMAStatements.S_oeis_a010786

namespace OMA.S_oeis_a010786_Disproof

open Filter Asymptotics Real OMA.S_oeis_a010786

private lemma hasSum_telescope_from (k₀ : ℕ) (hk₀ : 1 ≤ k₀) :
    HasSum (fun k : ℕ => (1 : ℝ) / ((k + k₀ : ℕ) : ℝ) - 1 / ((k + k₀ + 1 : ℕ) : ℝ))
      (1 / (k₀ : ℝ)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hsum : ∀ n : ℕ,
        ∑ k ∈ Finset.range n, ((1 : ℝ) / ((k + k₀ : ℕ) : ℝ) - 1 / ((k + k₀ + 1 : ℕ) : ℝ)) =
          1 / (k₀ : ℝ) - 1 / ((n + k₀ : ℕ) : ℝ) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
    simp_rw [hsum]
    have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + k₀ : ℕ) : ℝ)) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + (k₀ : ℝ))) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      have h2 := tendsto_const_nhds (x := (1 : ℝ)) |>.div_atTop h1
      simpa [Nat.cast_add] using h2
    simpa using tendsto_const_nhds.sub hlim
  · intro k
    have h1 : (0 : ℝ) < ((k + k₀ : ℕ) : ℝ) := by positivity
    have h2 : ((k + k₀ : ℕ) : ℝ) ≤ ((k + k₀ + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ (k + k₀)
    linarith [one_div_le_one_div_of_le h1 h2]

private lemma summable_one_div_add_two_pow (j : ℕ) :
    Summable (fun k : ℕ => (1 : ℝ) / (((k + 2 : ℕ) : ℝ) ^ (j + 2))) := by
  have h0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (j + 2)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  exact (summable_nat_add_iff 2).mpr h0

private lemma zeta_sub_one_re (j : ℕ) :
    (riemannZeta ((j : ℂ) + 2) - 1).re =
      ∑' k : ℕ, (1 : ℝ) / (((k + 2 : ℕ) : ℝ) ^ (j + 2)) := by
  have hgt : 1 < ((j : ℂ) + 2).re := by
    simp only [Complex.add_re, Complex.natCast_re, Complex.ofReal_re,
      show (2 : ℂ).re = 2 by rfl]
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow hgt
  have hterm : ∀ n : ℕ,
      (1 : ℂ) / ((n : ℂ) + 1) ^ ((j : ℂ) + 2) =
        Complex.ofReal ((1 : ℝ) / ((n : ℝ) + 1) ^ (j + 2)) := by
    intro n
    have hj : ((j : ℂ) + 2) = (((j + 2 : ℕ) : ℂ)) := by push_cast; ring
    rw [hj, Complex.cpow_natCast]
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_add,
      Complex.ofReal_natCast]
  simp_rw [hterm] at hzeta
  rw [← Complex.ofReal_tsum] at hzeta
  have hre : (riemannZeta ((j : ℂ) + 2)).re = ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ (j + 2) := by
    rw [hzeta, Complex.ofReal_re]
  have hs1 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (j + 2)) := by
    have h0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (j + 2)) :=
      Real.summable_one_div_nat_pow.mpr (by omega)
    have h1 := (summable_nat_add_iff 1).mpr h0
    simpa [Nat.cast_add] using h1
  rw [Complex.sub_re, Complex.one_re, hre, hs1.tsum_eq_zero_add]
  have hzero : (1 : ℝ) / (((0 : ℕ) : ℝ) + 1) ^ (j + 2) = 1 := by norm_num
  rw [hzero]
  have hshift : (∑' k : ℕ, (1 : ℝ) / (((k + 1 : ℕ) : ℝ) + 1) ^ (j + 2)) =
      ∑' k : ℕ, (1 : ℝ) / (((k + 2 : ℕ) : ℝ) ^ (j + 2)) := by
    congr 1; ext k; push_cast; ring
  rw [hshift]
  ring

private lemma zeta_sub_one_re_nonneg (j : ℕ) :
    0 ≤ (riemannZeta ((j : ℂ) + 2) - 1).re := by
  rw [zeta_sub_one_re]
  exact tsum_nonneg (fun k => by positivity)

private lemma zeta_two_sub_one_le :
    (riemannZeta ((0 : ℕ) + 2 : ℂ) - 1).re ≤ 97 / 144 := by
  rw [zeta_sub_one_re 0]
  have hs0 := summable_one_div_add_two_pow 0
  have hs1 := (summable_nat_add_iff 1).mpr hs0
  have hs2 := (summable_nat_add_iff 2).mpr hs0
  have hs3 := (summable_nat_add_iff 3).mpr hs0
  rw [hs0.tsum_eq_zero_add]
  have hstep1 : (∑' k : ℕ, (1 : ℝ) / (((k + 1 + 2 : ℕ) : ℝ) ^ 2)) =
      (1 : ℝ) / 9 + ∑' k : ℕ, (1 : ℝ) / (((k + 2 + 2 : ℕ) : ℝ) ^ 2) := by
    rw [hs1.tsum_eq_zero_add]
    congr 1
    norm_num
  have hstep2 : (∑' k : ℕ, (1 : ℝ) / (((k + 2 + 2 : ℕ) : ℝ) ^ 2)) =
      (1 : ℝ) / 16 + ∑' k : ℕ, (1 : ℝ) / (((k + 3 + 2 : ℕ) : ℝ) ^ 2) := by
    rw [hs2.tsum_eq_zero_add]
    congr 1
    norm_num
  have htail : (∑' k : ℕ, (1 : ℝ) / (((k + 3 + 2 : ℕ) : ℝ) ^ 2)) ≤ 1 / 4 := by
    have htel := hasSum_telescope_from 4 (by omega)
    rw [show (1 : ℝ) / 4 = 1 / ((4 : ℕ) : ℝ) by norm_num, ← htel.tsum_eq]
    refine Summable.tsum_le_tsum (fun k => ?_) hs3 htel.summable
    have h1 : (0 : ℝ) < (k : ℝ) + 4 := by positivity
    have h2 : (0 : ℝ) < (k : ℝ) + 5 := by positivity
    have hdiff : (1 : ℝ) / ((k + 4 : ℕ) : ℝ) - 1 / ((k + 4 + 1 : ℕ) : ℝ) =
        1 / (((k : ℝ) + 4) * ((k : ℝ) + 5)) := by
      push_cast; field_simp; ring
    rw [hdiff]
    push_cast
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith
  have h0val : (1 : ℝ) / (((0 + 2 : ℕ) : ℝ) ^ (0 + 2)) = 1 / 4 := by norm_num
  rw [h0val]
  have hrew1 : (∑' k : ℕ, (1 : ℝ) / (((k + 1 + 2 : ℕ) : ℝ) ^ (0 + 2))) =
      ∑' k : ℕ, (1 : ℝ) / (((k + 1 + 2 : ℕ) : ℝ) ^ 2) := by rfl
  rw [hrew1, hstep1, hstep2]
  linarith

private lemma zeta_three_sub_one_le :
    (riemannZeta ((1 : ℕ) + 2 : ℂ) - 1).re ≤ 7 / 24 := by
  rw [zeta_sub_one_re 1]
  have hs0 := summable_one_div_add_two_pow 1
  have hs1 := (summable_nat_add_iff 1).mpr hs0
  rw [hs0.tsum_eq_zero_add]
  have h0val : (1 : ℝ) / (((0 + 2 : ℕ) : ℝ) ^ (1 + 2)) = 1 / 8 := by norm_num
  rw [h0val]
  have htel := (hasSum_telescope_from 2 (by omega)).mul_left (1 / 3 : ℝ)
  have htail : (∑' k : ℕ, (1 : ℝ) / (((k + 1 + 2 : ℕ) : ℝ) ^ (1 + 2))) ≤ 1 / 6 := by
    have hval : (1 / 3 : ℝ) * (1 / ((2 : ℕ) : ℝ)) = 1 / 6 := by norm_num
    rw [← hval, ← htel.tsum_eq]
    refine Summable.tsum_le_tsum (fun k => ?_) hs1 htel.summable
    have h1 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have h2 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
    have hdiff : (1 / 3 : ℝ) * ((1 : ℝ) / ((k + 2 : ℕ) : ℝ) - 1 / ((k + 2 + 1 : ℕ) : ℝ)) =
        1 / (3 * ((k : ℝ) + 2) * ((k : ℝ) + 3)) := by
      push_cast; field_simp; ring
    rw [hdiff]
    push_cast
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [sq_nonneg ((k : ℝ) + 3)]
  linarith

private lemma zeta_sub_one_re_le_geom (j : ℕ) :
    (riemannZeta ((j : ℂ) + 2) - 1).re ≤ (1 / 2 : ℝ) ^ j * (97 / 144) := by
  have hle : (riemannZeta ((j : ℂ) + 2) - 1).re ≤
      (1 / 2 : ℝ) ^ j * (riemannZeta ((0 : ℕ) + 2 : ℂ) - 1).re := by
    rw [zeta_sub_one_re j, zeta_sub_one_re 0, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun k => ?_) (summable_one_div_add_two_pow j)
      ((summable_one_div_add_two_pow 0).mul_left _)
    have hpow : (1 : ℝ) / (((k + 2 : ℕ) : ℝ) ^ (j + 2)) =
        (1 / ((k + 2 : ℕ) : ℝ)) ^ j * (1 / (((k + 2 : ℕ) : ℝ) ^ 2)) := by
      rw [pow_add, one_div_pow, div_mul_div_comm, one_mul]
    rw [hpow]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine pow_le_pow_left₀ (by positivity) ?_ j
    exact one_div_le_one_div_of_le (by norm_num) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])
  have h2 := zeta_two_sub_one_le
  have hpow_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ j := by positivity
  nlinarith

private lemma c_summable :
    Summable (fun j : ℕ => (riemannZeta ((j : ℂ) + 2) - 1).re / ((j : ℝ) + 1)) := by
  refine Summable.of_nonneg_of_le
    (fun j => div_nonneg (zeta_sub_one_re_nonneg j) (by positivity))
    (fun j => ?_)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).mul_right (97 / 144))
  calc (riemannZeta ((j : ℂ) + 2) - 1).re / ((j : ℝ) + 1)
      ≤ (riemannZeta ((j : ℂ) + 2) - 1).re / 1 := by
        exact div_le_div_of_nonneg_left (zeta_sub_one_re_nonneg j) (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) j])
    _ = (riemannZeta ((j : ℂ) + 2) - 1).re := div_one _
    _ ≤ (1 / 2 : ℝ) ^ j * (97 / 144) := zeta_sub_one_re_le_geom j

private lemma c_le : c ≤ 805 / 864 := by
  unfold c
  have hs0 := c_summable
  have hs1 := (summable_nat_add_iff 1).mpr hs0
  have hs2 := (summable_nat_add_iff 2).mpr hs0
  rw [hs0.tsum_eq_zero_add]
  have h1 : (∑' j : ℕ, (riemannZeta (((j + 1 : ℕ) : ℂ) + 2) - 1).re / (((j + 1 : ℕ) : ℝ) + 1)) =
      (riemannZeta ((1 : ℕ) + 2 : ℂ) - 1).re / 2 +
        ∑' j : ℕ, (riemannZeta (((j + 2 : ℕ) : ℂ) + 2) - 1).re / (((j + 2 : ℕ) : ℝ) + 1) := by
    rw [hs1.tsum_eq_zero_add]
    congr 1
    norm_num
  have h0b : (riemannZeta ((0 : ℕ) + 2 : ℂ) - 1).re / ((0 : ℕ) + 1 : ℝ) ≤ 97 / 144 := by
    simpa using zeta_two_sub_one_le
  have h1b : (riemannZeta ((1 : ℕ) + 2 : ℂ) - 1).re / 2 ≤ 7 / 48 := by
    linarith [zeta_three_sub_one_le]
  have hgeom : HasSum (fun j : ℕ => (1 / 3 : ℝ) * ((1 / 2 : ℝ) ^ (j + 2) * (97 / 144))) (97 / 864) := by
    have hg := (hasSum_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1))
    have hmul := hg.mul_left ((1 / 3 : ℝ) * ((1 / 2 : ℝ) ^ 2 * (97 / 144)))
    have hf : (fun j : ℕ => (1 / 3 : ℝ) * ((1 / 2 : ℝ) ^ (j + 2) * (97 / 144))) =
        fun j : ℕ => (1 / 3 : ℝ) * ((1 / 2 : ℝ) ^ 2 * (97 / 144)) * (1 / 2 : ℝ) ^ j := by
      ext j; rw [pow_add]; ring
    have hv : (97 / 864 : ℝ) = (1 / 3 : ℝ) * ((1 / 2 : ℝ) ^ 2 * (97 / 144)) * (1 - 1 / 2 : ℝ)⁻¹ := by
      norm_num
    rw [hf, hv]
    exact hmul
  have htail : (∑' j : ℕ, (riemannZeta (((j + 2 : ℕ) : ℂ) + 2) - 1).re / (((j + 2 : ℕ) : ℝ) + 1)) ≤
      97 / 864 := by
    rw [← hgeom.tsum_eq]
    refine Summable.tsum_le_tsum (fun j => ?_) hs2 hgeom.summable
    have hden : (3 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) + 1 := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]
    have hnum := zeta_sub_one_re_le_geom (j + 2)
    have hdiv : (riemannZeta (((j + 2 : ℕ) : ℂ) + 2) - 1).re / (((j + 2 : ℕ) : ℝ) + 1) ≤
        (riemannZeta (((j + 2 : ℕ) : ℂ) + 2) - 1).re / 3 :=
      div_le_div_of_nonneg_left (zeta_sub_one_re_nonneg (j + 2)) (by norm_num) hden
    linarith
  have hrew : (∑' n : ℕ, (riemannZeta (((n + 1 : ℕ) : ℂ) + 2) - 1).re / (((n + 1 : ℕ) : ℝ) + 1)) =
      (riemannZeta ((1 : ℕ) + 2 : ℂ) - 1).re / 2 +
        ∑' j : ℕ, (riemannZeta (((j + 2 : ℕ) : ℂ) + 2) - 1).re / (((j + 2 : ℕ) : ℝ) + 1) := h1
  rw [hrew]
  linarith

private lemma sum_log_div_le_c (N : ℕ) :
    ∑ m ∈ Finset.Icc 2 N, (1 / (m : ℝ)) * Real.log ((m : ℝ) / ((m : ℝ) - 1)) ≤ c := by
  have hlim : Tendsto
      (fun J : ℕ => ∑ m ∈ Finset.Icc 2 N,
        (1 / (m : ℝ)) * ∑ j ∈ Finset.range J, (1 / (m : ℝ)) ^ (j + 1) / ((j : ℝ) + 1))
      atTop
      (nhds (∑ m ∈ Finset.Icc 2 N, (1 / (m : ℝ)) * Real.log ((m : ℝ) / ((m : ℝ) - 1)))) := by
    refine tendsto_finset_sum _ fun m hm => ?_
    have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
    have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      linarith
    have habs : |(1 / (m : ℝ))| < 1 := by
      rw [abs_of_pos (by positivity)]
      rw [div_lt_one hm_pos]
      exact_mod_cast (by omega : 1 < m)
    have hs := (Real.hasSum_pow_div_log_of_abs_lt_one habs).tendsto_sum_nat
    have hlog_eq : -Real.log (1 - 1 / (m : ℝ)) = Real.log ((m : ℝ) / ((m : ℝ) - 1)) := by
      have hsub : (1 : ℝ) - 1 / (m : ℝ) = ((m : ℝ) - 1) / (m : ℝ) := by field_simp
      rw [hsub, Real.log_div (ne_of_gt hm1_pos) (ne_of_gt hm_pos),
          Real.log_div (ne_of_gt hm_pos) (ne_of_gt hm1_pos)]
      ring
    rw [hlog_eq] at hs
    exact hs.const_mul (1 / (m : ℝ))
  refine le_of_tendsto hlim (Eventually.of_forall fun J => ?_)
  have hswap :
      (∑ m ∈ Finset.Icc 2 N,
        (1 / (m : ℝ)) * ∑ j ∈ Finset.range J, (1 / (m : ℝ)) ^ (j + 1) / ((j : ℝ) + 1)) =
      ∑ j ∈ Finset.range J,
        (∑ m ∈ Finset.Icc 2 N, (1 : ℝ) / (m : ℝ) ^ (j + 2)) / ((j : ℝ) + 1) := by
    simp_rw [Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
    rw [one_div_pow, pow_succ, pow_succ]
    ring
  rw [hswap]
  have hle1 :
      (∑ j ∈ Finset.range J,
        (∑ m ∈ Finset.Icc 2 N, (1 : ℝ) / (m : ℝ) ^ (j + 2)) / ((j : ℝ) + 1)) ≤
      ∑ j ∈ Finset.range J, (riemannZeta ((j : ℂ) + 2) - 1).re / ((j : ℝ) + 1) := by
    refine Finset.sum_le_sum fun j _ => ?_
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rw [zeta_sub_one_re j]
    have hinj : (∑ m ∈ Finset.Icc 2 N, (1 : ℝ) / (m : ℝ) ^ (j + 2)) =
        ∑ k ∈ Finset.range (N - 1), (1 : ℝ) / (((k + 2 : ℕ) : ℝ) ^ (j + 2)) := by
      refine Finset.sum_bij (fun m _ => m - 2) ?_ ?_ ?_ ?_
      · intro m hm; simp only [Finset.mem_Icc] at hm; simp only [Finset.mem_range]; omega
      · intro m₁ hm₁ m₂ hm₂ heq; simp only [Finset.mem_Icc] at hm₁ hm₂; omega
      · intro k hk; simp only [Finset.mem_range] at hk
        refine ⟨k + 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro m hm; simp only [Finset.mem_Icc] at hm
        have hm_eq : m - 2 + 2 = m := by omega
        rw [hm_eq]
    rw [hinj]
    exact (summable_one_div_add_two_pow j).sum_le_tsum (Finset.range (N - 1))
      (fun k _ => by positivity)
  have hle2 :
      (∑ j ∈ Finset.range J, (riemannZeta ((j : ℂ) + 2) - 1).re / ((j : ℝ) + 1)) ≤ c := by
    unfold c
    exact c_summable.sum_le_tsum (Finset.range J)
      (fun j _ => div_nonneg (zeta_sub_one_re_nonneg j) (by positivity))
  exact le_trans hle1 hle2

private lemma log_nat_eq_sum : ∀ q : ℕ, 1 ≤ q →
    Real.log (q : ℝ) = ∑ m ∈ Finset.Icc 2 q, Real.log ((m : ℝ) / ((m : ℝ) - 1)) := by
  intro q hq
  induction q with
  | zero => omega
  | succ q ih =>
    rcases eq_or_lt_of_le (Nat.zero_le q) with rfl | hqpos
    · simp
    · have hq1 : 1 ≤ q := hqpos
      have hIcc : Finset.Icc 2 (q + 1) = insert (q + 1) (Finset.Icc 2 q) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp), ← ih hq1]
      have hq_pos : (0 : ℝ) < (q : ℝ) := by positivity
      have hq1_pos : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
      have hsub : (((q + 1 : ℕ) : ℝ) - 1) = (q : ℝ) := by push_cast; ring
      rw [hsub, Real.log_div (ne_of_gt hq1_pos) (ne_of_gt hq_pos)]
      ring

private lemma log_a_eq (n : ℕ) (hn : 1 ≤ n) :
    Real.log (a n : ℝ) =
      ∑ m ∈ Finset.Icc 2 n, ((n / m : ℕ) : ℝ) * Real.log ((m : ℝ) / ((m : ℝ) - 1)) := by
  unfold a
  rw [Nat.cast_prod, Real.log_prod]
  · have h1 : (∑ k ∈ Finset.Icc 1 n, Real.log ((n / k : ℕ) : ℝ)) =
        ∑ k ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 2 n,
          if m ≤ n / k then Real.log ((m : ℝ) / ((m : ℝ) - 1)) else 0 := by
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_Icc] at hk
      have hq1 : 1 ≤ n / k := Nat.div_pos hk.2 hk.1
      rw [log_nat_eq_sum (n / k) hq1, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext m
      simp only [Finset.mem_Icc, Finset.mem_filter]
      have hdiv_le : n / k ≤ n := Nat.div_le_self n k
      omega
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [Finset.mem_Icc] at hm
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hfilt : (Finset.Icc 1 n).filter (fun k => m ≤ n / k) = Finset.Icc 1 (n / m) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hk1, _⟩, hmk⟩
        have hmul : m * k ≤ n := (Nat.le_div_iff_mul_le hk1).mp hmk
        exact ⟨hk1, (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr (by rw [mul_comm]; exact hmul)⟩
      · rintro ⟨hk1, hkm⟩
        have hmul : k * m ≤ n := (Nat.le_div_iff_mul_le (by omega : 0 < m)).mp hkm
        exact ⟨⟨hk1, le_trans hkm (Nat.div_le_self n m)⟩,
          (Nat.le_div_iff_mul_le hk1).mpr (by rw [mul_comm]; exact hmul)⟩
    rw [hfilt, Nat.card_Icc]
    simp
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have hq1 : 1 ≤ n / k := Nat.div_pos hk.2 hk.1
    exact ne_of_gt (by exact_mod_cast hq1 : (0 : ℝ) < ((n / k : ℕ) : ℝ))

private lemma c_mul_sub_log_a_ge {N n : ℕ} (hN : 2 ≤ N) (hNn : N ≤ n) :
    ∑ m ∈ Finset.Icc 2 N, (((n % m : ℕ) : ℝ) / (m : ℝ)) * Real.log ((m : ℝ) / ((m : ℝ) - 1)) ≤
      c * (n : ℝ) - Real.log (a n : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hc := sum_log_div_le_c n
  have hcmul : (∑ m ∈ Finset.Icc 2 n, ((n : ℝ) / (m : ℝ)) * Real.log ((m : ℝ) / ((m : ℝ) - 1))) ≤
      c * (n : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg n)
    rw [Finset.sum_mul] at h1
    refine le_trans (le_of_eq ?_) h1
    refine Finset.sum_congr rfl fun m _ => by ring
  rw [log_a_eq n hn1]
  have hsub :
      (∑ m ∈ Finset.Icc 2 n, (((n % m : ℕ) : ℝ) / (m : ℝ)) * Real.log ((m : ℝ) / ((m : ℝ) - 1))) =
      (∑ m ∈ Finset.Icc 2 n, ((n : ℝ) / (m : ℝ)) * Real.log ((m : ℝ) / ((m : ℝ) - 1))) -
      (∑ m ∈ Finset.Icc 2 n, ((n / m : ℕ) : ℝ) * Real.log ((m : ℝ) / ((m : ℝ) - 1))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm_ne : (m : ℝ) ≠ 0 := by positivity
    have hdivmod : (n : ℝ) = (m : ℝ) * ((n / m : ℕ) : ℝ) + ((n % m : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod n m).symm
    have hfrac : ((n % m : ℕ) : ℝ) / (m : ℝ) = (n : ℝ) / (m : ℝ) - ((n / m : ℕ) : ℝ) := by
      field_simp [hm_ne]; linarith
    rw [hfrac]; ring
  have hsub_le :
      (∑ m ∈ Finset.Icc 2 N, (((n % m : ℕ) : ℝ) / (m : ℝ)) * Real.log ((m : ℝ) / ((m : ℝ) - 1))) ≤
      ∑ m ∈ Finset.Icc 2 n, (((n % m : ℕ) : ℝ) / (m : ℝ)) * Real.log ((m : ℝ) / ((m : ℝ) - 1)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right hNn) (fun m hm _ => ?_)
    have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
    have hlog_nn : 0 ≤ Real.log ((m : ℝ) / ((m : ℝ) - 1)) := by
      have hm_r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      apply Real.log_nonneg
      rw [one_le_div (by linarith)]
      linarith
    exact mul_nonneg (by positivity) hlog_nn
  linarith

private lemma sum_mod_Ico_block (start m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Finset.Ico start (start + m), (n % m) = m * (m - 1) / 2 := by
  have hbij : ∑ n ∈ Finset.Ico start (start + m), (n % m) = ∑ r ∈ Finset.range m, r := by
    refine Finset.sum_bij (fun n _ => n % m) ?_ ?_ ?_ ?_
    · intro n _; exact Finset.mem_range.mpr (Nat.mod_lt n hm)
    · intro n₁ hn₁ n₂ hn₂ heq
      simp only [Finset.mem_Ico] at hn₁ hn₂
      have h1 : n₁ / m = n₂ / m := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have : n₁ + m ≤ n₂ := by
            have := Nat.div_add_mod n₁ m
            have := Nat.div_add_mod n₂ m
            nlinarith
          omega
        · have : n₂ + m ≤ n₁ := by
            have := Nat.div_add_mod n₁ m
            have := Nat.div_add_mod n₂ m
            nlinarith
          omega
      have := Nat.div_add_mod n₁ m
      have := Nat.div_add_mod n₂ m
      nlinarith
    · intro r hr
      simp only [Finset.mem_range] at hr
      have hmod_lt : start % m < m := Nat.mod_lt start hm
      let k := if start % m ≤ r then start + (r - start % m) else start + m + r - start % m
      refine ⟨k, Finset.mem_Ico.mpr ?_, ?_⟩
      · dsimp only [k]; split_ifs <;> omega
      · dsimp only [k]
        split_ifs with hle
        · have h1 : start + (r - start % m) = m * (start / m) + r := by
            have := Nat.div_add_mod start m; omega
          rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
        · have h1 : start + m + r - start % m = m * (start / m + 1) + r := by
            have := Nat.div_add_mod start m
            have : m * (start / m + 1) = m * (start / m) + m := by ring
            omega
          rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    · intro n _; rfl
  rw [hbij, Finset.sum_range_id]

private lemma sum_mod_Ico_multi (start m q : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Finset.Ico start (start + q * m), (n % m) = q * (m * (m - 1) / 2) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : Finset.Ico start (start + (q + 1) * m) =
        Finset.Ico start (start + q * m) ∪ Finset.Ico (start + q * m) (start + q * m + m) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_union]
      have : (q + 1) * m = q * m + m := by ring
      omega
    have hdisj : Disjoint (Finset.Ico start (start + q * m))
        (Finset.Ico (start + q * m) (start + q * m + m)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_Ico] at hx1 hx2
      omega
    rw [hsplit, Finset.sum_union hdisj, ih, sum_mod_Ico_block (start + q * m) m hm]
    ring

private lemma sum_mod_Ico_real_ge (N m : ℕ) (hm : 2 ≤ m) :
    ((N : ℝ) / (m : ℝ) - 1) * ((m : ℝ) - 1) / 2 ≤
      ∑ n ∈ Finset.Ico N (2 * N), ((n % m : ℕ) : ℝ) / (m : ℝ) := by
  have hsub : Finset.Ico N (N + (N / m) * m) ⊆ Finset.Ico N (2 * N) := by
    intro x hx
    simp only [Finset.mem_Ico] at hx ⊢
    have hmul : (N / m) * m ≤ N := Nat.div_mul_le_self N m
    omega
  have hnat : (N / m) * (m * (m - 1) / 2) ≤ ∑ n ∈ Finset.Ico N (2 * N), (n % m) := by
    rw [← sum_mod_Ico_multi N m (N / m) (by omega)]
    exact Finset.sum_le_sum_of_subset hsub
  have hnat_r : (((N / m : ℕ) : ℝ) * ((m * (m - 1) / 2 : ℕ) : ℝ)) ≤
      ∑ n ∈ Finset.Ico N (2 * N), ((n % m : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have heven : 2 ∣ m * (m - 1) := by
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨k * (k + k - 1), by ring⟩
    · refine ⟨(2 * k + 1) * k, ?_⟩
      have : 2 * k + 1 - 1 = 2 * k := by omega
      rw [this]; ring
  have hhalf : ((m * (m - 1) / 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    have h2 : 2 * (m * (m - 1) / 2) = m * (m - 1) := Nat.mul_div_cancel' heven
    have h2r : (2 : ℝ) * ((m * (m - 1) / 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
      have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
      rw [← hm1]; exact_mod_cast h2
    linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hdiv_ge : (N : ℝ) / (m : ℝ) - 1 ≤ ((N / m : ℕ) : ℝ) := by
    have hlt : N < (N / m + 1) * m := by
      have := Nat.div_add_mod N m
      have := Nat.mod_lt N (by omega : 0 < m)
      nlinarith
    have hltr : (N : ℝ) < (((N / m : ℕ) : ℝ) + 1) * (m : ℝ) := by exact_mod_cast hlt
    rw [div_sub_one (ne_of_gt hm_pos), div_le_iff₀ hm_pos]
    linarith
  have hm1_nn : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  rw [← Finset.sum_div]
  rw [le_div_iff₀ hm_pos]
  calc ((N : ℝ) / (m : ℝ) - 1) * ((m : ℝ) - 1) / 2 * (m : ℝ)
      = ((N : ℝ) / (m : ℝ) - 1) * ((m : ℝ) * ((m : ℝ) - 1) / 2) := by ring
    _ ≤ ((N / m : ℕ) : ℝ) * ((m : ℝ) * ((m : ℝ) - 1) / 2) := by
        exact mul_le_mul_of_nonneg_right hdiv_ge (by positivity)
    _ = ((N / m : ℕ) : ℝ) * ((m * (m - 1) / 2 : ℕ) : ℝ) := by rw [hhalf]
    _ ≤ ∑ n ∈ Finset.Ico N (2 * N), ((n % m : ℕ) : ℝ) := hnat_r

private lemma exists_large_deficit (N : ℕ) (hN : 2 ≤ N) :
    ∃ n ∈ Finset.Ico N (2 * N),
      (1 / 2 : ℝ) * Real.log (N : ℝ) - 3 / 2 ≤ c * (n : ℝ) - Real.log (a n : ℝ) := by
  have hsum_ge :
      (N : ℝ) * ((1 / 2 : ℝ) * Real.log (N : ℝ) - 3 / 2) ≤
        ∑ n ∈ Finset.Ico N (2 * N), (c * (n : ℝ) - Real.log (a n : ℝ)) := by
    have h1 :
        (∑ m ∈ Finset.Icc 2 N,
          (∑ n ∈ Finset.Ico N (2 * N), ((n % m : ℕ) : ℝ) / (m : ℝ)) *
            Real.log ((m : ℝ) / ((m : ℝ) - 1))) ≤
        ∑ n ∈ Finset.Ico N (2 * N), (c * (n : ℝ) - Real.log (a n : ℝ)) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun n hn => ?_
      exact c_mul_sub_log_a_ge hN (Finset.mem_Ico.mp hn).1
    have h2 :
        (∑ m ∈ Finset.Icc 2 N,
          (((N : ℝ) / (m : ℝ) - 1) * ((m : ℝ) - 1) / 2) *
            Real.log ((m : ℝ) / ((m : ℝ) - 1))) ≤
        ∑ m ∈ Finset.Icc 2 N,
          (∑ n ∈ Finset.Ico N (2 * N), ((n % m : ℕ) : ℝ) / (m : ℝ)) *
            Real.log ((m : ℝ) / ((m : ℝ) - 1)) := by
      refine Finset.sum_le_sum fun m hm => ?_
      have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
      have hlog_nn : 0 ≤ Real.log ((m : ℝ) / ((m : ℝ) - 1)) := by
        have hm_r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
        apply Real.log_nonneg
        rw [one_le_div (by linarith)]
        linarith
      exact mul_le_mul_of_nonneg_right (sum_mod_Ico_real_ge N m hm2) hlog_nn
    have h3 :
        (∑ m ∈ Finset.Icc 2 N,
          (((N : ℝ) / (m : ℝ) - 1) * ((m : ℝ) - 1) / 2) *
            Real.log ((m : ℝ) / ((m : ℝ) - 1))) =
        ((N : ℝ) / 2) * (∑ m ∈ Finset.Icc 2 N, Real.log ((m : ℝ) / ((m : ℝ) - 1))) -
        ((N : ℝ) / 2) * (∑ m ∈ Finset.Icc 2 N, (1 / (m : ℝ)) * Real.log ((m : ℝ) / ((m : ℝ) - 1))) -
        (1 / 2 : ℝ) * (∑ m ∈ Finset.Icc 2 N, ((m : ℝ) - 1) * Real.log ((m : ℝ) / ((m : ℝ) - 1))) := by
      simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
      have hm_ne : (m : ℝ) ≠ 0 := by positivity
      field_simp [hm_ne]
    have hterm1 : ∑ m ∈ Finset.Icc 2 N, Real.log ((m : ℝ) / ((m : ℝ) - 1)) = Real.log (N : ℝ) :=
      (log_nat_eq_sum N (by omega)).symm
    have hterm2 : ∑ m ∈ Finset.Icc 2 N, (1 / (m : ℝ)) * Real.log ((m : ℝ) / ((m : ℝ) - 1)) ≤ 1 :=
      le_trans (sum_log_div_le_c N) (by linarith [c_le])
    have hterm3 : ∑ m ∈ Finset.Icc 2 N, ((m : ℝ) - 1) * Real.log ((m : ℝ) / ((m : ℝ) - 1)) ≤ (N : ℝ) := by
      have hle_one : ∀ m ∈ Finset.Icc 2 N, ((m : ℝ) - 1) * Real.log ((m : ℝ) / ((m : ℝ) - 1)) ≤ 1 := by
        intro m hm
        have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
        have hm_r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
        have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by linarith
        have hlog_le := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < (m : ℝ)) hm1_pos)
        have hmul := mul_le_mul_of_nonneg_left hlog_le (le_of_lt hm1_pos)
        have hsimp : ((m : ℝ) - 1) * ((m : ℝ) / ((m : ℝ) - 1) - 1) = 1 := by
          field_simp [ne_of_gt hm1_pos]; ring
        linarith
      calc ∑ m ∈ Finset.Icc 2 N, ((m : ℝ) - 1) * Real.log ((m : ℝ) / ((m : ℝ) - 1))
          ≤ ∑ _m ∈ Finset.Icc 2 N, (1 : ℝ) := Finset.sum_le_sum hle_one
        _ = ((Finset.Icc 2 N).card : ℝ) := by simp
        _ ≤ (N : ℝ) := by rw [Nat.card_Icc]; exact_mod_cast (by omega : N + 1 - 2 ≤ N)
    have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    rw [h3, hterm1] at h2
    nlinarith
  by_contra hall
  push Not at hall
  have hlt : (∑ n ∈ Finset.Ico N (2 * N), (c * (n : ℝ) - Real.log (a n : ℝ))) <
      ∑ _n ∈ Finset.Ico N (2 * N), ((1 / 2 : ℝ) * Real.log (N : ℝ) - 3 / 2) := by
    refine Finset.sum_lt_sum_of_nonempty ?_ hall
    exact ⟨N, Finset.mem_Ico.mpr ⟨le_refl N, by omega⟩⟩
  rw [Finset.sum_const, Nat.card_Ico, show 2 * N - N = N by omega, nsmul_eq_mul] at hlt
  linarith

theorem disproof_proof :
    ¬ ((fun n : ℕ => Real.log (a n) - c * (n - Real.log (2 * Real.pi * n) / 2)) =o[atTop]
      fun n : ℕ => Real.log (n : ℝ)) := by
  intro hmain
  have hbound := (Asymptotics.isLittleO_iff.mp hmain) (show (0 : ℝ) < 1 / 100 by norm_num)
  rw [Filter.eventually_atTop] at hbound
  obtain ⟨N₀, hN₀⟩ := hbound
  let N : ℕ := max (max N₀ 2) (Nat.ceil (Real.exp 1000))
  have hN2 : 2 ≤ N := le_trans (le_max_right N₀ 2) (le_max_left _ _)
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left N₀ 2) (le_max_left _ _)
  have hNexp : Real.exp 1000 ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right (max N₀ 2) _)
  have hlogN : (1000 : ℝ) ≤ Real.log (N : ℝ) := by
    have := Real.log_le_log (Real.exp_pos 1000) hNexp
    rwa [Real.log_exp] at this
  obtain ⟨n, hn_mem, hdef⟩ := exists_large_deficit N hN2
  simp only [Finset.mem_Ico] at hn_mem
  have hnN₀ : N₀ ≤ n := le_trans hNN₀ hn_mem.1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : 2 ≤ n := by omega
    positivity
  have hlogn_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hmain_n := hN₀ n hnN₀
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogn_nn] at hmain_n
  have hlow := (abs_le.mp hmain_n).1
  have hlog_mul : Real.log (2 * Real.pi * (n : ℝ)) = Real.log (2 * Real.pi) + Real.log (n : ℝ) :=
    Real.log_mul (by positivity) (ne_of_gt hn_pos)
  have hlog2pi : Real.log (2 * Real.pi) ≤ 8 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)
    linarith [Real.pi_lt_four]
  have hlogn_le : Real.log (n : ℝ) ≤ Real.log (N : ℝ) + 1 := by
    have hlt : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast (le_of_lt hn_mem.2)
    have h1 := Real.log_le_log hn_pos hlt
    rw [Real.log_mul (by norm_num) (by positivity)] at h1
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    linarith
  have hc_nn : 0 ≤ c := by
    unfold c
    exact tsum_nonneg (fun j => div_nonneg (zeta_sub_one_re_nonneg j) (by positivity))
  have hc_ub : c ≤ 805 / 864 := c_le
  rw [hlog_mul] at hlow
  nlinarith

end OMA.S_oeis_a010786_Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a010786.main) :=
  OMA.S_oeis_a010786_Disproof.disproof_proof
