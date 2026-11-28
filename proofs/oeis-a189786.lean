import OMAStatements.S_oeis_a189786

-- Problem: A189786: a(n) = n + [nr/t] + [ns/t]; r=Pi/2, s=arcsin(5/13), t=arcsin(12/13).
-- Upstream: formal-conjectures statements/oeis-a189786.lean:0 (declaration OMA.S_oeis_a189786.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: s = arcsin(5/13) and t = arcsin(12/13) satisfy t = Pi/2 - s, because cos s = 12/13.
-- Real.sin_bound and the monotonicity of sin give 0.3939 < s < 0.3956; with 3.1415 < Pi < 3.1416
-- this gives 117 <= 350*s/t < 118 and 467 <= 350*(Pi/2)/t < 468, so a(350) = 350 + 467 + 117 = 934,
-- a positive even number of the form 8*116+6. (The entry itself notes a(143) = 382 = 8*47+6.)

namespace S08A189786

theorem t_eq : Real.arcsin (12 / 13) = Real.pi / 2 - Real.arcsin (5 / 13) := by
  have hs0 : 0 ≤ Real.arcsin (5 / 13) := Real.arcsin_nonneg.mpr (by norm_num)
  have hs1 : Real.arcsin (5 / 13) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hc : Real.cos (Real.arcsin (5 / 13)) = 12 / 13 := by
    rw [Real.cos_arcsin, show (1 : ℝ) - (5 / 13) ^ 2 = (12 / 13) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h2 : Real.sin (Real.pi / 2 - Real.arcsin (5 / 13)) = 12 / 13 := by
    rw [Real.sin_pi_div_two_sub, hc]
  calc Real.arcsin (12 / 13) = Real.arcsin (Real.sin (Real.pi / 2 - Real.arcsin (5 / 13))) := by
        rw [h2]
    _ = Real.pi / 2 - Real.arcsin (5 / 13) :=
        Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)

theorem s_lo : (3939 / 10000 : ℝ) < Real.arcsin (5 / 13) := by
  by_contra hle
  rw [not_lt] at hle
  have h1 := Real.sin_le_sin_of_le_of_le_pi_div_two (Real.neg_pi_div_two_le_arcsin (5 / 13))
    (by linarith [Real.pi_gt_three]) hle
  rw [Real.sin_arcsin (x := 5 / 13) (by norm_num) (by norm_num)] at h1
  have h2 := Real.sin_bound (x := 3939 / 10000) (abs_le.mpr ⟨by norm_num, by norm_num⟩)
  rw [abs_of_pos (show (0 : ℝ) < 3939 / 10000 by norm_num)] at h2
  have h3 := (abs_le.mp h2).2
  have key : (3939 / 10000 : ℝ) - (3939 / 10000) ^ 3 / 6 + (3939 / 10000) ^ 5 / 100 < 5 / 13 := by
    norm_num
  linarith

theorem s_hi : Real.arcsin (5 / 13) < (3956 / 10000 : ℝ) := by
  by_contra hle
  rw [not_lt] at hle
  have h1 := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
    (Real.arcsin_le_pi_div_two (5 / 13)) hle
  rw [Real.sin_arcsin (x := 5 / 13) (by norm_num) (by norm_num)] at h1
  have h2 := Real.sin_bound (x := 3956 / 10000) (abs_le.mpr ⟨by norm_num, by norm_num⟩)
  rw [abs_of_pos (show (0 : ℝ) < 3956 / 10000 by norm_num)] at h2
  have h3 := (abs_le.mp h2).1
  have key : (5 / 13 : ℝ) < 3956 / 10000 - (3956 / 10000) ^ 3 / 6 - (3956 / 10000) ^ 5 / 100 := by
    norm_num
  linarith

theorem pi_lo : (31415 / 10000 : ℝ) < Real.pi := by
  have h := Real.pi_gt_d4
  have e : (3.1415 : ℝ) = 31415 / 10000 := by norm_num
  rw [e] at h
  exact h

theorem pi_hi : Real.pi < (31416 / 10000 : ℝ) := by
  have h := Real.pi_lt_d4
  have e : (3.1416 : ℝ) = 31416 / 10000 := by norm_num
  rw [e] at h
  exact h

theorem t_pos : 0 < Real.arcsin (12 / 13) := by
  have hs2 := s_hi
  have hp1 := pi_lo
  rw [t_eq]
  linarith

theorem fl1 : ⌊(350 : ℝ) * Real.arcsin (5 / 13) / Real.arcsin (12 / 13)⌋ = 117 := by
  have hs1 := s_lo
  have hs2 := s_hi
  have hp1 := pi_lo
  have hp2 := pi_hi
  rw [Int.floor_eq_iff, le_div_iff₀ t_pos, div_lt_iff₀ t_pos, t_eq]
  constructor
  · push_cast
    linarith
  · push_cast
    linarith

theorem fl2 : ⌊(350 : ℝ) * (Real.pi / 2) / Real.arcsin (12 / 13)⌋ = 467 := by
  have hs1 := s_lo
  have hs2 := s_hi
  have hp1 := pi_lo
  have hp2 := pi_hi
  rw [Int.floor_eq_iff, le_div_iff₀ t_pos, div_lt_iff₀ t_pos, t_eq]
  constructor
  · push_cast
    linarith
  · push_cast
    linarith

theorem a350 : OMA.S_oeis_a189786.a 350 = 934 := by
  unfold OMA.S_oeis_a189786.a
  rw [show ((350 : ℕ) : ℝ) = 350 by norm_num, show ((350 : ℕ) : ℤ) = 350 by norm_num]
  linear_combination fl2 + fl1

end S08A189786

open OMA.S_oeis_a189786 S08A189786 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a189786.main) := by
  intro h
  obtain ⟨-, -, hx⟩ := (h 934).mp ⟨350, by norm_num, a350⟩
  exact hx ⟨116, by norm_num⟩
