import OMAStatements.S_oeis_a001951

-- Credit: @oh-meh
open OMA.S_oeis_a001951

theorem OMA.solution : type_of% @OMA.S_oeis_a001951.main := by
  intro n
  use n
  let m := a n
  have h0 : 0 ≤ (n : ℝ) * Real.sqrt 2 := by positivity
  have lo : (m : ℝ) ≤ (n : ℝ) * Real.sqrt 2 := Nat.floor_le h0
  have hi : (n : ℝ) * Real.sqrt 2 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsq : ((n : ℝ) * Real.sqrt 2)^2 = 2 * (n : ℝ)^2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring
  have low : m^2 ≤ 2*n^2 := by
    exact_mod_cast (show (m : ℝ)^2 ≤ 2*(n : ℝ)^2 from hsq ▸ (pow_le_pow_left₀ (by positivity) lo 2))
  have high : 2*n^2 < m^2 + 2*m + 1 := by
    have h := pow_lt_pow_left₀ hi h0 (by decide : 2 ≠ 0)
    rw [hsq] at h
    exact_mod_cast (show 2*(n : ℝ)^2 < (m : ℝ)^2 + 2*m + 1 by linarith [sq (m+1 : ℝ)])
  change |((m*(m+1)/2 : ℕ) : ℤ) - (n : ℤ)^2| ≤ (m/2 : ℕ)
  rw [abs_le, ← Nat.cast_pow]
  have tri : m*(m+1) = m^2+m := by ring
  have div : 2 ∣ m^2+m := by
    rw [← tri]
    rcases Nat.even_or_odd m with ⟨k,h⟩ | ⟨k,h⟩
    · exact ⟨k*(m+1), by rw [h]; ring⟩
    · exact ⟨m*(k+1), by rw [h]; ring⟩
  rw [tri]
  omega
