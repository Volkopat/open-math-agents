import OMAStatements.S_oeis_a227776

-- Problem: A227776: a(n) = 6*n^2 + 1.
-- Upstream: formal-conjectures statements/oeis-a227776.lean:0 (declaration OMA.S_oeis_a227776.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for m >= 1 and t = 1/m, t - t^3/6 < sin t < t (Real.sin_gt_sub_cube, Real.sin_lt)
-- and sin t <= t - t^3/6 + t^5/100 (Real.sin_bound). Hence 1 - 1/(6m^2) < s(m) < 1 and
-- s(m)(6m^2+1) <= 6m^2. So c/d = 6n^2/(6n^2+1) splits s(n) < s(n+1), and for d <= 6n^2 every
-- c/d < 1 has c/d <= 1 - 1/d <= 1 - 1/(6n^2) < s(n).

namespace M03A227776

open OMA.S_oeis_a227776

theorem sbounds (m : ℕ) (hm : 1 ≤ m) :
    1 - (1 / (m : ℝ)) ^ 2 / 6 < s m ∧ s m < 1 ∧
      s m * (6 * (m : ℝ) ^ 2 + 1) ≤ 6 * (m : ℝ) ^ 2 := by
  have hM : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < (m : ℝ) := by linarith [hM]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / (m : ℝ) := ⟨_, rfl⟩
  have hs : s m = (m : ℝ) * Real.sin t := by
    unfold s
    rw [ht]
  rw [hs, ← ht]
  have h : (m : ℝ) * t = 1 := by
    rw [ht, mul_one_div_cancel hM0.ne']
  have ht0 : 0 < t := by
    rw [ht]
    exact one_div_pos.mpr hM0
  have ht1 : t ≤ 1 := by
    have hmt := mul_nonneg (sub_nonneg.mpr hM) ht0.le
    linarith [hmt, h]
  have hsl : t - t ^ 3 / 6 < Real.sin t := Real.sin_gt_sub_cube ht0
  have hslt : Real.sin t < t := Real.sin_lt ht0
  have hsu0 := Real.sin_bound (show |t| ≤ 1 by rw [abs_of_pos ht0]; exact ht1)
  rw [abs_of_pos ht0] at hsu0
  have hsu : Real.sin t ≤ t - t ^ 3 / 6 + t ^ 5 / 100 := by
    have hh := (abs_le.mp hsu0).2
    linarith [hh]
  have hA : Real.sin t * (6 + t ^ 2) ≤ 6 * t := by
    have p1 := mul_le_mul_of_nonneg_right hsu (by positivity : (0 : ℝ) ≤ 6 + t ^ 2)
    have e3 : (t - t ^ 3 / 6 + t ^ 5 / 100) * (6 + t ^ 2) =
        6 * t - t ^ 5 * (8 / 75 - t ^ 2 / 100) := by
      ring
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht0, ht1]
    have p2 : 0 ≤ t ^ 5 * (8 / 75 - t ^ 2 / 100) :=
      mul_nonneg (pow_nonneg ht0.le 5) (by linarith [ht2])
    linarith [p1, e3, p2]
  have e0 : (m : ℝ) * (t - t ^ 3 / 6) = 1 - t ^ 2 / 6 := by
    linear_combination (1 - t ^ 2 / 6) * h
  have e1 : (m : ℝ) * Real.sin t * (6 * (m : ℝ) ^ 2 + 1) =
      (m : ℝ) ^ 3 * (Real.sin t * (6 + t ^ 2)) := by
    linear_combination (-(Real.sin t) * (m : ℝ) * ((m : ℝ) * t + 1)) * h
  have e2 : 6 * (m : ℝ) ^ 2 = (m : ℝ) ^ 3 * (6 * t) := by
    linear_combination (-6 * (m : ℝ) ^ 2) * h
  have p3 := mul_le_mul_of_nonneg_left hA (pow_nonneg hM0.le 3)
  have p4 := mul_lt_mul_of_pos_left hsl hM0
  have p5 := mul_lt_mul_of_pos_left hslt hM0
  refine ⟨?_, ?_, ?_⟩
  · linarith [p4, e0]
  · linarith [p5, h]
  · linarith [e1, e2, p3]

theorem main' (n : ℕ) (hn : 1 ≤ n) :
    s n < s (n + 1) ∧ IsLeast {d : ℕ | IsSplitter (s n) (s (n + 1)) d} (a n) := by
  have hN : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < (n : ℝ) := by linarith [hN]
  obtain ⟨hl1, -, hU1⟩ := sbounds n hn
  obtain ⟨hl2, hu2, -⟩ := sbounds (n + 1) (by omega)
  have hl2' : 1 - (1 / ((n : ℝ) + 1)) ^ 2 / 6 < s (n + 1) := by exact_mod_cast hl2
  have hpos : (0 : ℝ) < 6 * (n : ℝ) ^ 2 + 1 := by positivity
  have hmid1 : s n ≤ 6 * (n : ℝ) ^ 2 / (6 * (n : ℝ) ^ 2 + 1) := by
    rw [le_div_iff₀ hpos]
    exact hU1
  have hmid2 : 6 * (n : ℝ) ^ 2 / (6 * (n : ℝ) ^ 2 + 1) < s (n + 1) := by
    have hq : 6 * (n : ℝ) ^ 2 / (6 * (n : ℝ) ^ 2 + 1) ≤
        1 - (1 / ((n : ℝ) + 1)) ^ 2 / 6 := by
      rw [div_le_iff₀ hpos]
      obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
      rw [← hu]
      have hmu : ((n : ℝ) + 1) * u = 1 := by
        rw [hu, mul_one_div_cancel (by positivity)]
      have hmu2 : ((n : ℝ) + 1) ^ 2 * u ^ 2 = 1 := by
        linear_combination (((n : ℝ) + 1) * u + 1) * hmu
      have hle : u ^ 2 * (6 * (n : ℝ) ^ 2 + 1) ≤ u ^ 2 * (6 * ((n : ℝ) + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hN0]) (sq_nonneg u)
      linarith [hle, hmu2]
    linarith [hq, hl2']
  refine ⟨by linarith [hmid1, hmid2], ?_, fun d hd => ?_⟩
  · show IsSplitter (s n) (s (n + 1)) (a n)
    unfold IsSplitter
    refine ⟨by unfold a; positivity, 6 * (n : ℤ) ^ 2, ?_, ?_⟩
    · unfold a
      push_cast
      linarith [hmid1]
    · unfold a
      push_cast
      linarith [hmid2]
  · have hd' : 0 < d ∧ ∃ c : ℤ, s n ≤ (c : ℝ) / (d : ℝ) ∧
        (c : ℝ) / (d : ℝ) < s (n + 1) := hd
    obtain ⟨hd0, c, hc1, hc2⟩ := hd'
    unfold a
    by_contra hlt
    have hdle : d ≤ 6 * n ^ 2 := by omega
    have hD0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hDle : (d : ℝ) ≤ 6 * (n : ℝ) ^ 2 := by exact_mod_cast hdle
    have hcd : (c : ℝ) < (d : ℝ) := by
      have h1 : (c : ℝ) / (d : ℝ) < 1 := by linarith [hc2, hu2]
      rw [div_lt_iff₀ hD0] at h1
      linarith [h1]
    have hcd' : c ≤ (d : ℤ) - 1 := by
      have hcz : c < (d : ℤ) := by exact_mod_cast hcd
      omega
    have hcd'' : (c : ℝ) ≤ (d : ℝ) - 1 := by exact_mod_cast hcd'
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / (n : ℝ) := ⟨_, rfl⟩
    rw [← ht] at hl1
    have hnt : (n : ℝ) * t = 1 := by
      rw [ht, mul_one_div_cancel hN0.ne']
    have hnt2 : (n : ℝ) ^ 2 * t ^ 2 = 1 := by
      linear_combination ((n : ℝ) * t + 1) * hnt
    have hDt : (d : ℝ) * t ^ 2 ≤ 6 := by
      have hh := mul_le_mul_of_nonneg_right hDle (sq_nonneg t)
      linarith [hh, hnt2]
    have hcD : (c : ℝ) / (d : ℝ) ≤ 1 - t ^ 2 / 6 := by
      rw [div_le_iff₀ hD0]
      linarith [hcd'', hDt]
    linarith [hc1, hcD, hl1]

end M03A227776

open OMA.S_oeis_a227776 M03A227776 in
theorem OMA.solution : type_of% @OMA.S_oeis_a227776.main := by
  intro n hn
  exact main' n hn
