import OMAReductions.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H2_R1_H1_R1

/-! Denominators of x - X n and X n divide each other's products with den x (`Rat.add_den_dvd`),
so |log den (x - X n) - log den (X n)| ≤ log den x for every n. Dividing by n² and using
log den x / n² → 0, the two sequences have the same limit (squeeze). -/

open Filter Topology in
theorem OMA.solution :
    OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H2_R1_H1_R1.H2 := by
  intro x X c hX
  have hbound : ∀ n : ℕ, |Real.log ((x - X n).den : ℝ) - Real.log ((X n).den : ℝ)| ≤
      Real.log (x.den : ℝ) := by
    intro n
    have h1 : (x - X n).den ∣ x.den * (X n).den := by
      have := Rat.add_den_dvd x (-X n)
      rwa [Rat.neg_den, ← sub_eq_add_neg] at this
    have h2 : (X n).den ∣ x.den * (x - X n).den := by
      have := Rat.add_den_dvd x (-(x - X n))
      rwa [Rat.neg_den, show x + -(x - X n) = X n by ring] at this
    have r0 : (0 : ℝ) < (x.den : ℝ) := by exact_mod_cast x.den_pos
    have r1 : (0 : ℝ) < ((x - X n).den : ℝ) := by exact_mod_cast (x - X n).den_pos
    have r2 : (0 : ℝ) < ((X n).den : ℝ) := by exact_mod_cast (X n).den_pos
    have l1 : ((x - X n).den : ℝ) ≤ (x.den : ℝ) * ((X n).den : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.mul_pos x.den_pos (X n).den_pos) h1
    have l2 : ((X n).den : ℝ) ≤ (x.den : ℝ) * ((x - X n).den : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.mul_pos x.den_pos (x - X n).den_pos) h2
    have q1 := Real.log_le_log r1 l1
    have q2 := Real.log_le_log r2 l2
    rw [Real.log_mul r0.ne' r2.ne'] at q1
    rw [Real.log_mul r0.ne' r1.ne'] at q2
    rw [abs_le]
    constructor <;> linarith
  have hD : Tendsto (fun n : ℕ => Real.log (x.den : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
  have hlo := hX.sub hD
  have hhi := hX.add hD
  rw [sub_zero] at hlo
  rw [add_zero] at hhi
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun n => ?_) (fun n => ?_)
  · have hb := (abs_le.1 (hbound n)).1
    simp only
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · have hb := (abs_le.1 (hbound n)).2
    simp only
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
