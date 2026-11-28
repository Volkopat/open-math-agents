import OMAReductions.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H2_R1

-- Reduction EllipticDivisibilitySequence.silverman_eds_primitive_prime_divisors.R1.H2.R1.H1.R1 of step EllipticDivisibilitySequence.silverman_eds_primitive_prime_divisors.R1.H2.R1.H1
-- Credit: @marcusbuffett

namespace OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H2_R1_H1_R1

open EllipticDivisibilitySequence Filter Real

/-- Denominator height along the multiples of a rational non-torsion point,
expressed using the division-polynomial formula for their abscissas. -/
def H1 : Prop := ∀ (E : WeierstrassCurve ℚ) (x y : ℚ),
  E.Δ ≠ 0 → E.toAffine.Equation x y →
  (∀ i : ℤ, i ≠ 0 → (E.ψ i).evalEval x y ≠ 0) →
  let X (n : ℕ) := (E.φ (n : ℤ)).evalEval x y / ((E.ψ (n : ℤ)).evalEval x y)^2
  ∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => log (X n).den / (n:ℝ)^2) atTop (nhds c)

/-- A fixed rational translation and reflection preserve quadratic denominator growth. -/
def H2 : Prop := ∀ (x : ℚ) (X : ℕ → ℚ) (c : ℝ),
  Tendsto (fun n : ℕ => log (X n).den / (n:ℝ)^2) atTop (nhds c) →
  Tendsto (fun n : ℕ => log (x - X n).den / (n:ℝ)^2) atTop (nhds c)

theorem main : H1 → H2 → OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H2_R1.H1 := by
  intro height translate W hW hne
  obtain ⟨_, _, E, x, y, hdisc, hxy, hw⟩ := hW
  have nz (i : ℤ) (hi : i ≠ 0) : (E.ψ i).evalEval x y ≠ 0 := by
    rw [← hw]; exact_mod_cast hne i hi
  let X (n : ℕ) := (E.φ (n : ℤ)).evalEval x y / ((E.ψ (n : ℤ)).evalEval x y)^2
  obtain ⟨c, hc, hlim⟩ := height E x y hdisc hxy nz
  refine ⟨c, hc, (translate x X c hlim).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  congr 2
  have hn' : (n : ℤ) ≠ 0 := by omega
  have minus : ((n - 1 : ℕ) : ℤ) = (n : ℤ)-1 := by omega
  have eqn : x - X n = Rat.divInt (W (n+1) * W (n-1)) (W n ^ 2) := by
    unfold X WeierstrassCurve.φ
    simp only [Polynomial.evalEval_sub, Polynomial.evalEval_mul, Polynomial.evalEval_pow,
      Polynomial.evalEval_C, Polynomial.eval_X, ← hw, Rat.divInt_eq_div, Int.cast_pow, Int.cast_mul]
    field_simp [hne _ hn'] <;> ring
  rw [eqn, Rat.den_divInt, if_neg (pow_ne_zero _ (hne _ hn'))]
  simp [Int.gcd, Int.natAbs_pow, Int.natAbs_mul, minus, Nat.gcd_comm]

end OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H2_R1_H1_R1
