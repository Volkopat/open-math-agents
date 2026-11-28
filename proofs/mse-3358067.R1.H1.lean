import OMAReductions.R_mse_3358067_R1

-- Step mse-3358067.R1.H1: hypothesis H1 of reduction mse-3358067.R1
-- Credit: @futurum-dev

/-! If a prime `p > 2n` divides `j² + 1` for some `1 ≤ j ≤ n`, then `p` divides no other
`i² + 1` with `i ≤ n` (it would divide `(i - j)(i + j)`, whose factors lie strictly between `-p`
and `p`), and `p² ∤ j² + 1` (as `j² + 1 < p²`). So `p` divides `(1² + 1)⋯(n² + 1)` exactly once and
the product is not a square. For each `4 ≤ n ≤ 200` an explicit pair `(j, p)` is given. -/

namespace OMA.ArctanH1

open Finset

lemma not_sq (n j p : ℕ) (hp : p.Prime) (hj1 : 1 ≤ j) (hjn : j ≤ n) (hpn : 2 * n < p)
    (hdvd : p ∣ j ^ 2 + 1) : ¬ IsSquare (∏ i ∈ Finset.Icc 1 n, (i ^ 2 + 1)) := by
  have hjmem : j ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨hj1, hjn⟩
  rw [← Finset.mul_prod_erase _ _ hjmem]
  set R := ∏ i ∈ (Finset.Icc 1 n).erase j, (i ^ 2 + 1)
  have hR : ¬ p ∣ R := by
    intro h
    obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
    obtain ⟨hij, hi'⟩ := Finset.mem_erase.1 hi
    obtain ⟨hi1, hin⟩ := Finset.mem_Icc.1 hi'
    have hz : (p : ℤ) ∣ ((i : ℤ) - j) * ((i : ℤ) + j) := by
      have h1 : (p : ℤ) ∣ ((i ^ 2 + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hpi
      have h2 : (p : ℤ) ∣ ((j ^ 2 + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hdvd
      have he : ((i : ℤ) - j) * ((i : ℤ) + j) = ((i ^ 2 + 1 : ℕ) : ℤ) - ((j ^ 2 + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rw [he]
      exact dvd_sub h1 h2
    rcases (Int.prime_iff_natAbs_prime.2 (by simpa using hp)).dvd_or_dvd hz with h3 | h3
    · have h4 := Int.natAbs_dvd_natAbs.2 h3
      simp only [Int.natAbs_natCast] at h4
      have h5 : ((i : ℤ) - j).natAbs ≠ 0 := by omega
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero h5) h4
      omega
    · have h4 := Int.natAbs_dvd_natAbs.2 h3
      simp only [Int.natAbs_natCast] at h4
      have h5 : ((i : ℤ) + j).natAbs = i + j := by omega
      rw [h5] at h4
      have := Nat.le_of_dvd (by omega) h4
      omega
  have hsq : ¬ p ^ 2 ∣ j ^ 2 + 1 := by
    intro h
    have := Nat.le_of_dvd (by positivity) h
    have : j ^ 2 + 1 < p ^ 2 := by nlinarith
    omega
  rintro ⟨m, hm⟩
  have hpm : p ∣ m := by
    have : p ∣ m * m := hm ▸ dvd_mul_of_dvd_left hdvd _
    rcases (Nat.Prime.dvd_mul hp).1 this with h | h <;> exact h
  have hp2 : p ^ 2 ∣ (j ^ 2 + 1) * R := by
    rw [hm, pow_two]
    exact Nat.mul_dvd_mul hpm hpm
  have hcop : Nat.Coprime (p ^ 2) R := Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hR)
  exact hsq (hcop.dvd_of_dvd_mul_right hp2)

theorem H1_proof : OMA.R_mse_3358067_R1.H1 := by
  intro n h4 h200
  rcases (show (4 ≤ n ∧ n ≤ 5) ∨ (6 ≤ n ∧ n ≤ 8) ∨ (9 ≤ n ∧ n ≤ 9) ∨ (10 ≤ n ∧ n ≤ 13) ∨ (14 ≤ n ∧ n ≤ 15) ∨ (16 ≤ n ∧ n ≤ 19) ∨ (20 ≤ n ∧ n ≤ 23) ∨ (24 ≤ n ∧ n ≤ 25) ∨ (26 ≤ n ∧ n ≤ 35) ∨ (36 ≤ n ∧ n ≤ 39) ∨ (40 ≤ n ∧ n ≤ 53) ∨ (54 ≤ n ∧ n ≤ 55) ∨ (56 ≤ n ∧ n ≤ 65) ∨ (66 ≤ n ∧ n ≤ 73) ∨ (74 ≤ n ∧ n ≤ 83) ∨ (84 ≤ n ∧ n ≤ 89) ∨ (90 ≤ n ∧ n ≤ 93) ∨ (94 ≤ n ∧ n ≤ 109) ∨ (110 ≤ n ∧ n ≤ 115) ∨ (116 ≤ n ∧ n ≤ 119) ∨ (120 ≤ n ∧ n ≤ 123) ∨ (124 ≤ n ∧ n ≤ 125) ∨ (126 ≤ n ∧ n ≤ 129) ∨ (130 ≤ n ∧ n ≤ 133) ∨ (134 ≤ n ∧ n ≤ 145) ∨ (146 ≤ n ∧ n ≤ 149) ∨ (150 ≤ n ∧ n ≤ 155) ∨ (156 ≤ n ∧ n ≤ 159) ∨ (160 ≤ n ∧ n ≤ 169) ∨ (170 ≤ n ∧ n ≤ 175) ∨ (176 ≤ n ∧ n ≤ 179) ∨ (180 ≤ n ∧ n ≤ 183) ∨ (184 ≤ n ∧ n ≤ 200) by omega) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact not_sq n 4 17 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 6 37 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 9 41 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 10 101 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 14 197 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 16 257 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 20 401 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 24 577 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 26 677 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 36 1297 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 40 1601 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 54 2917 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 56 3137 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 66 4357 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 74 5477 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 84 7057 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 90 8101 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 94 8837 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 110 12101 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 116 13457 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 120 14401 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 124 15377 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 126 15877 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 130 16901 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 134 17957 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 146 21317 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 150 22501 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 156 24337 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 160 25601 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 170 28901 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 176 30977 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 180 32401 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)
  · exact not_sq n 184 33857 (by norm_num) (by norm_num) (by omega) (by omega) (by norm_num)

end OMA.ArctanH1

theorem OMA.solution : OMA.R_mse_3358067_R1.H1 := OMA.ArctanH1.H1_proof
