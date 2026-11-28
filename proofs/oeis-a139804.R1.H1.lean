import OMAReductions.R_oeis_a139804_R1

theorem OMA.solution : OMA.R_oeis_a139804_R1.H1 := by
  intro n m hvalid hm1
  obtain ⟨hm_ge, hprime⟩ := hvalid
  have hgt : ∀ q : ℕ, q.Prime → q ∣ m → 3 ^ n < q := by
    intro q hq hqm
    by_contra hle
    push_neg at hle
    have hq_fac : q ∣ (3 ^ n).factorial := Nat.dvd_factorial hq.pos hle
    have hq_sum : q ∣ (3 ^ n).factorial + m := Nat.dvd_add hq_fac hqm
    rcases (Nat.dvd_prime hprime).mp hq_sum with h1 | heq
    · exact hq.ne_one h1
    · have hsf : 3 ^ n ≤ (3 ^ n).factorial := Nat.self_le_factorial (3 ^ n)
      omega
  refine ⟨hgt, ?_⟩
  by_cases hmp : m.Prime
  · exact Or.inl hmp
  · right
    set q := m.minFac
    have hq_prime : q.Prime := Nat.minFac_prime hm1
    have hq_dvd : q ∣ m := Nat.minFac_dvd m
    have hq_gt : 3 ^ n < q := hgt q hq_prime hq_dvd
    obtain ⟨k, hk⟩ := hq_dvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      omega
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [mul_one] at hk
      exact hmp (hk ▸ hq_prime)
    have hkm_prime : k.minFac.Prime := Nat.minFac_prime hk1
    have hkm_dvd_m : k.minFac ∣ m := (Nat.minFac_dvd k).trans ⟨q, by rw [hk, mul_comm]⟩
    have hq_le_kmin : q ≤ k.minFac := Nat.minFac_le_of_dvd hkm_prime.two_le hkm_dvd_m
    have hkmin_le_k : k.minFac ≤ k := Nat.minFac_le (Nat.pos_of_ne_zero hk0)
    have hq_sq : q * q ≤ m := by
      calc q * q ≤ q * k := Nat.mul_le_mul_left q (hq_le_kmin.trans hkmin_le_k)
        _ = m := hk.symm
    have h3q : 3 ^ n + 1 ≤ q := by omega
    rw [sq]
    exact (Nat.mul_le_mul h3q h3q).trans hq_sq
