import OMAReductions.R_Bloch_blochConstant_upper_bound_R1
import Mathlib

-- Step H2 of Bloch.blochConstant_upper_bound.R1.
-- Credit: @LordMike

namespace OMA.R_Bloch_blochConstant_upper_bound_R1

/-- Covering of the unit-norm triangular lattice: the four corner candidates contain one with
`x ^ 2 + x * y + y ^ 2 ≤ 1 / 3`. -/
lemma oma_bloch_key (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (x ^ 2 + x * y + y ^ 2 ≤ 1 / 3) ∨ ((x - 1) ^ 2 + (x - 1) * y + y ^ 2 ≤ 1 / 3) ∨
    (x ^ 2 + x * (y - 1) + (y - 1) ^ 2 ≤ 1 / 3) ∨
    ((x - 1) ^ 2 + (x - 1) * (y - 1) + (y - 1) ^ 2 ≤ 1 / 3) := by
  rcases le_total (x + y) 1 with hs | hs <;> rcases le_total y x with hyx | hxy
  · by_cases h : x ^ 2 + x * y + y ^ 2 ≤ 1 / 3
    · exact Or.inl h
    · exact Or.inr (Or.inl (by nlinarith))
  · by_cases h : x ^ 2 + x * y + y ^ 2 ≤ 1 / 3
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl (by nlinarith)))
  · by_cases h : (x - 1) ^ 2 + (x - 1) * (y - 1) + (y - 1) ^ 2 ≤ 1 / 3
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl (by nlinarith))
  · by_cases h : (x - 1) ^ 2 + (x - 1) * (y - 1) + (y - 1) ^ 2 ≤ 1 / 3
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl (by nlinarith)))

end OMA.R_Bloch_blochConstant_upper_bound_R1

theorem OMA.solution : OMA.R_Bloch_blochConstant_upper_bound_R1.H2 := by
  unfold OMA.R_Bloch_blochConstant_upper_bound_R1.H2
  intro c hc x r hr
  have ht : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (x.re - c) / c := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = x.im / c := ⟨_, rfl⟩
  have hXc : c * X = x.re - c := by
    rw [hX]; field_simp
  have hYc : c * Y = x.im := by
    rw [hY]; field_simp
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = -X / 3 + Y * Real.sqrt 3 / 3 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = -X / 3 - Y * Real.sqrt 3 / 3 := ⟨_, rfl⟩
  have claim : ∀ m n : ℤ, (α - m) ^ 2 + (α - m) * (β - n) + (β - n) ^ 2 ≤ 1 / 3 →
      ∃ w : ℂ, (∃ m n : ℤ, w = ((c : ℝ) : ℂ) *
        (1 + (m : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) - 1) +
          (n : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 2 - 1))) ∧ w ∈ Metric.ball x r := by
    intro m n hmn
    refine ⟨((c : ℝ) : ℂ) *
        (1 + (m : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) - 1) +
          (n : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 2 - 1)), ⟨m, n, rfl⟩, ?_⟩
    have hre : (((c : ℝ) : ℂ) *
        (1 + (m : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) - 1) +
          (n : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 2 - 1))).re
        = c * (1 - 3 / 2 * ((m : ℝ) + n)) := by
      simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im]
      linear_combination (-(c * (n : ℝ)) / 4) * ht
    have him : (((c : ℝ) : ℂ) *
        (1 + (m : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) - 1) +
          (n : ℂ) * ((⟨-1 / 2, Real.sqrt 3 / 2⟩ : ℂ) ^ 2 - 1))).im
        = c * (Real.sqrt 3 * ((m : ℝ) - n) / 2) := by
      simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im]
      ring
    rw [Metric.mem_ball, Complex.dist_eq_re_im]
    refine lt_of_le_of_lt ?_ hr
    rw [Real.sqrt_le_iff]
    refine ⟨hc.le, ?_⟩
    rw [hre, him]
    have hdr : c * (1 - 3 / 2 * ((m : ℝ) + n)) - x.re
        = -(c * (3 / 2 * ((m : ℝ) + n) + X)) := by linear_combination hXc
    have hdi : c * (Real.sqrt 3 * ((m : ℝ) - n) / 2) - x.im
        = c * (Real.sqrt 3 * ((m : ℝ) - n) / 2 - Y) := by linear_combination hYc
    rw [hdr, hdi]
    have hbr : (3 / 2 * ((m : ℝ) + n) + X) ^ 2 + (Real.sqrt 3 * ((m : ℝ) - n) / 2 - Y) ^ 2
        = 3 * ((α - m) ^ 2 + (α - m) * (β - n) + (β - n) ^ 2) := by
      rw [hα, hβ]
      linear_combination (((m : ℝ) - n) ^ 2 / 4 - Y ^ 2 / 3) * ht
    have hsum : (-(c * (3 / 2 * ((m : ℝ) + n) + X))) ^ 2
        + (c * (Real.sqrt 3 * ((m : ℝ) - n) / 2 - Y)) ^ 2
        = c ^ 2 * ((3 / 2 * ((m : ℝ) + n) + X) ^ 2 + (Real.sqrt 3 * ((m : ℝ) - n) / 2 - Y) ^ 2) := by
      ring
    rw [hsum, hbr]
    nlinarith [sq_nonneg c]
  have hc3 : (0 : ℝ) ≤ 1 := zero_le_one
  have hfa := Int.fract_nonneg α
  have hfa1 := (Int.fract_lt_one α).le
  have hfb := Int.fract_nonneg β
  have hfb1 := (Int.fract_lt_one β).le
  have hkey := OMA.R_Bloch_blochConstant_upper_bound_R1.oma_bloch_key
    (Int.fract α) (Int.fract β) hfa hfa1 hfb hfb1
  have ea : Int.fract α = α - ⌊α⌋ := (Int.self_sub_floor α).symm
  have eb : Int.fract β = β - ⌊β⌋ := (Int.self_sub_floor β).symm
  rw [ea, eb] at hkey
  rcases hkey with h | h | h | h
  · exact claim ⌊α⌋ ⌊β⌋ h
  · exact claim (⌊α⌋ + 1) ⌊β⌋ (by push_cast; nlinarith [h])
  · exact claim ⌊α⌋ (⌊β⌋ + 1) (by push_cast; nlinarith [h])
  · exact claim (⌊α⌋ + 1) (⌊β⌋ + 1) (by push_cast; nlinarith [h])
