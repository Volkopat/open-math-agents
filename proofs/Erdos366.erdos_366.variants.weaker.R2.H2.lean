import OMAReductions.R_Erdos366_erdos_366_variants_weaker_R2

/-! The prime-divisibility argument follows the proof by @Salofe.
Each factor already contains at least a cube of every prime dividing it. -/

theorem OMA.solution : OMA.R_Erdos366_erdos_366_variants_weaker_R2.H2 := by
  intro a b c _ _ _ p hp
  obtain ⟨prime, divides, _⟩ := Nat.mem_primeFactors.mp hp
  rcases prime.dvd_mul.mp divides with hab | hc
  · rcases prime.dvd_mul.mp hab with ha | hb
    · exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (prime.dvd_of_dvd_pow ha) 3) _) _
    · exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right
          (pow_dvd_pow_of_dvd_of_le (prime.dvd_of_dvd_pow hb) (by decide : 3 ≤ 4)) _) _
  · exact dvd_mul_of_dvd_right
      (pow_dvd_pow_of_dvd_of_le (prime.dvd_of_dvd_pow hc) (by decide : 3 ≤ 5)) _
