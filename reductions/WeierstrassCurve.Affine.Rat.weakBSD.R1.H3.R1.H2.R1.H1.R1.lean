import OMAReductions.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H3_R1_H2_R1

-- Reduction WeierstrassCurve.Affine.Rat.weakBSD.R1.H3.R1.H2.R1.H1.R1 of step WeierstrassCurve.Affine.Rat.weakBSD.R1.H3.R1.H2.R1.H1
-- Credit: @Karataam

/-! Splits off the absolute convergence (already proved as `weakBSD.R1.H3.R1.H1`) and reduces the
twist continuations from all rationals `r` to `0 ≤ r < 1`: the additive character
`n ↦ e(n r)` only depends on `r` modulo `1`, so the twisted series for `r` and for
`r - ⌊r⌋` are the same function. -/

namespace OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H3_R1_H2_R1_H1_R1

-- Absolute convergence of the L-series on `Re s > 3/2`.
def H1 : Prop :=
  ∀ (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic],
    ∀ s : ℂ, 3 / 2 < s.re → LSeriesSummable (fun n : ℕ ↦ (E.LFunction n : ℂ)) s

-- Entire, strip-bounded continuations of the completed additive twists, for `0 ≤ r < 1`.
def H2 : Prop :=
  ∀ (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic],
    ∀ r : ℚ, 0 ≤ r → r < 1 → ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      (∃ M : ℝ, ∀ s : ℂ, s.re ∈ Set.Icc (0 : ℝ) 2 → ‖L s‖ ≤ M) ∧
      ∀ s : ℂ, 3 / 2 < s.re →
        L s = ((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s *
          LSeries (fun n : ℕ ↦ (E.LFunction n : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * n * ((r : ℝ) : ℂ))) s

lemma exp_twist_int_shift (n : ℕ) (r : ℚ) (k : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * n * (((r + k : ℚ) : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * n * ((r : ℝ) : ℂ)) := by
  have h : 2 * Real.pi * Complex.I * n * (((r + k : ℚ) : ℝ) : ℂ) =
      2 * Real.pi * Complex.I * n * ((r : ℝ) : ℂ) + ((n * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem main : H1 → H2 → OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H3_R1_H2_R1.H1 := by
  intro conv twist E hE
  refine ⟨@conv E hE, fun r => ?_⟩
  set r' : ℚ := r - ⌊r⌋ with hr'
  have h0 : 0 ≤ r' := Int.fract_nonneg r
  have h1 : r' < 1 := Int.fract_lt_one r
  obtain ⟨L, hL, hM, heq⟩ := @twist E hE r' h0 h1
  refine ⟨L, hL, hM, fun s hs => ?_⟩
  rw [heq s hs]
  have hr : r = r' + (⌊r⌋ : ℤ) := by rw [hr']; ring
  congr 3
  funext n
  rw [hr, exp_twist_int_shift]

end OMA.R_WeierstrassCurve_Affine_Rat_weakBSD_R1_H3_R1_H2_R1_H1_R1
