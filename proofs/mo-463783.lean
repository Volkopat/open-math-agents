import OMAStatements.S_mo_463783

/-! Retains @RiverMint78’s complete earlier exact-target proof,
e32c883cf537c319354c4fd7519ccac0088dfa4a/proofs/mo-463783.lean,
linked in statement #32384. Taking real parts replaces the final
contradiction via z=6 and its quadratic relation; Real.sqrt_eq_one
replaces the separate squared-norm implication. Main #33235 by
@rexmhall09 and pending #36900 by @caa1982 use another witness. -/

namespace MO463783

private noncomputable def z : ℂ := ⟨-1 / 4, Real.sqrt 15 / 4⟩

private theorem unit_norm : ‖z‖ = 1 := by
  have h := Real.sq_sqrt (show 0 ≤ (15 : ℝ) by norm_num)
  rw [Complex.norm_def, Real.sqrt_eq_one, Complex.normSq_apply]
  change (-1/4 : ℝ) * (-1/4) + (Real.sqrt 15 / 4) * (Real.sqrt 15 / 4) = 1
  nlinarith

private theorem quadratic : 2 * z ^ 2 + z + 2 = 0 := by
  have h := Real.sq_sqrt (show 0 ≤ (15 : ℝ) by norm_num)
  apply Complex.ext <;>
    norm_num [z, pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith

private theorem not_fifth : z ^ 5 ≠ 1 := by
  intro h
  have hr : 16 * z ^ 5 = 5 * z - 14 := by
    linear_combination (8*z^3 - 4*z^2 - 6*z + 7) * quadratic
  rw [h] at hr
  have hre := congrArg Complex.re hr
  norm_num [z] at hre

end MO463783

open MO463783

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_463783.main) := by
  intro h
  apply not_fifth
  apply h (Polynomial.X ^ 2 + 1) 5 (by decide) z unit_norm
  norm_num [Finset.sum_range_succ, Polynomial.eval_add, Polynomial.eval_pow]
  simp only [show (2 : ℤ).toNat = 2 from rfl]
  linear_combination quadratic

