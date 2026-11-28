import OMAReductions.R_OeisA217785_conjecture_3_R1_H2_R1

/-! A divisor a = u X + v of polyS n = 1 + 2 X + ... + (n+1) X^n of degree at most one has
v a unit, since the constant term of polyS n is 1. If u is also a unit, the reduction's lemma
`PolyDisk.unit_of_unit_lead` makes a a unit. Otherwise |u| ≥ 2 and r = -v/u is a real root of
polyS n with |r| ≤ 1/2. Multiplying by (1 - r)^2 gives 1 - (n+2) r^(n+1) + (n+1) r^(n+2) = 0,
so 1 ≤ (n+2) |r|^(n+1) + (n+1) |r|^(n+2) ≤ (3n+5)/2^(n+2), false for n ≥ 2. -/

namespace OMA.A217785Lin

theorem closed_form (r : ℝ) (n : ℕ) :
    (1 - r) ^ 2 * ∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1) * r ^ k =
      1 - ((n : ℝ) + 2) * r ^ (n + 1) + ((n : ℝ) + 1) * r ^ (n + 2) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem pow_bound (n : ℕ) (hn : 2 ≤ n) : 3 * n + 5 < 2 ^ (n + 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h : 2 ^ (n + 1 + 2) = 2 * 2 ^ (n + 2) := by ring
    omega

end OMA.A217785Lin

open Polynomial in
theorem OMA.solution : OMA.R_OeisA217785_conjecture_3_R1_H2_R1.H1 := by
  intro n hn a ha hdeg
  by_cases hu : IsUnit a.leadingCoeff
  · exact PolyDisk.unit_of_unit_lead a ha hu
  exfalso
  obtain ⟨u, hu_def⟩ : ∃ u, u = a.coeff 1 := ⟨_, rfl⟩
  obtain ⟨v, hv_def⟩ : ∃ v, v = a.coeff 0 := ⟨_, rfl⟩
  have ha' : a = C u * X + C v := by
    rw [hu_def, hv_def]; exact eq_X_add_C_of_natDegree_le_one hdeg
  have hv : IsUnit v := by
    rw [hv_def]
    apply isUnit_of_dvd_one
    simpa [Polynomial.eval_zero, ← Polynomial.coeff_zero_eq_eval_zero] using
      (show (eval 0 a) ∣ 1 from (PolyDisk.eval_zero n) ▸ eval_dvd (x := 0) ha)
  have hu0 : u ≠ 0 := by
    intro h0
    apply hu
    have hC : a = C v := by rw [ha', h0]; simp
    rw [hC, leadingCoeff_C]
    exact hv
  have hnd : a.natDegree = 1 := natDegree_eq_of_le_of_coeff_ne_zero hdeg (hu_def ▸ hu0)
  have hlead : a.leadingCoeff = u := by rw [leadingCoeff, hnd, hu_def]
  rw [hlead] at hu
  have hu2 : 2 ≤ |u| := by
    have h1 : |u| ≠ 1 := fun h => hu (Int.isUnit_iff_abs_eq.mpr h)
    have h2 : 0 < |u| := abs_pos.mpr hu0
    omega
  have hv1 : |v| = 1 := Int.isUnit_iff_abs_eq.mp hv
  have hur : (u : ℝ) ≠ 0 := by exact_mod_cast hu0
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = -(v : ℝ) / (u : ℝ) := ⟨_, rfl⟩
  have hroot_a : eval₂ (Int.castRingHom ℝ) r a = 0 := by
    rw [ha', eval₂_add, eval₂_mul, eval₂_C, eval₂_C, eval₂_X, eq_intCast, eq_intCast, hr_def]
    field_simp
    try ring
  have hroot : eval₂ (Int.castRingHom ℝ) r (OeisA217785.polyS n) = 0 := by
    obtain ⟨b, hb⟩ := ha
    rw [hb, eval₂_mul, hroot_a, zero_mul]
  have hS : ∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1) * r ^ k = 0 := by
    simpa [OeisA217785.polyS, eval₂_finsetSum] using hroot
  have key : 1 - ((n : ℝ) + 2) * r ^ (n + 1) + ((n : ℝ) + 1) * r ^ (n + 2) = 0 := by
    have h := OMA.A217785Lin.closed_form r n
    rw [hS, mul_zero] at h
    linarith
  have hvr : |(v : ℝ)| = 1 := by rw [← Int.cast_abs, hv1, Int.cast_one]
  have hur2 : (2 : ℝ) ≤ |(u : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast hu2
  have hr : |r| ≤ 1 / 2 := by
    rw [hr_def, abs_div, abs_neg, hvr]
    exact one_div_le_one_div_of_le (by norm_num) hur2
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 2) * |r| ^ (n + 1) + ((n : ℝ) + 1) * |r| ^ (n + 2) := by
    have e : (1 : ℝ) = ((n : ℝ) + 2) * r ^ (n + 1) - ((n : ℝ) + 1) * r ^ (n + 2) := by linarith
    calc (1 : ℝ) = |((n : ℝ) + 2) * r ^ (n + 1) - ((n : ℝ) + 1) * r ^ (n + 2)| := by
          rw [← e, abs_one]
      _ ≤ |((n : ℝ) + 2) * r ^ (n + 1)| + |((n : ℝ) + 1) * r ^ (n + 2)| := abs_sub _ _
      _ = ((n : ℝ) + 2) * |r| ^ (n + 1) + ((n : ℝ) + 1) * |r| ^ (n + 2) := by
          rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 2),
            abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  have hb1 : |r| ^ (n + 1) ≤ (1 / 2) ^ (n + 1) := pow_le_pow_left₀ (abs_nonneg r) hr _
  have hb2 : |r| ^ (n + 2) ≤ (1 / 2) ^ (n + 2) := pow_le_pow_left₀ (abs_nonneg r) hr _
  have hq : ((1 : ℝ) / 2) ^ (n + 1) * 2 ^ (n + 1) = 1 := by rw [← mul_pow]; norm_num
  have hq2 : ((1 : ℝ) / 2) ^ (n + 2) = ((1 : ℝ) / 2) ^ (n + 1) / 2 := by rw [pow_succ]; ring
  have hc1 : ((n : ℝ) + 2) * |r| ^ (n + 1) ≤ ((n : ℝ) + 2) * ((1 : ℝ) / 2) ^ (n + 1) :=
    mul_le_mul_of_nonneg_left hb1 (by positivity)
  have hc2 : ((n : ℝ) + 1) * |r| ^ (n + 2) ≤ ((n : ℝ) + 1) * ((1 : ℝ) / 2) ^ (n + 2) :=
    mul_le_mul_of_nonneg_left hb2 (by positivity)
  rw [hq2] at hc2
  have hfinal : (1 : ℝ) ≤ ((3 * (n : ℝ) + 5) / 2) * ((1 : ℝ) / 2) ^ (n + 1) := by linarith
  have hQpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have hm := mul_le_mul_of_nonneg_right hfinal hQpos.le
  rw [one_mul, mul_assoc, hq, mul_one] at hm
  have hP : ((3 * n + 5 : ℕ) : ℝ) < ((2 ^ (n + 2) : ℕ) : ℝ) := by
    exact_mod_cast OMA.A217785Lin.pow_bound n hn
  push_cast at hP
  rw [pow_succ] at hP
  linarith
