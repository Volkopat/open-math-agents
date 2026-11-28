import OMAStatements.S_oeis_a333197

namespace OMA.P_oeis_a333197

open OMA.S_oeis_a333197

/-- Every odd divisor `d > 1` of a term is prime: an odd nonprime `d > 1` has even neighbours,
which would have to equal `2`. -/
theorem odd_dvd_prime {k d : ℕ} (h : IsTerm k) (hd : d ∣ k) (hodd : Odd d) (h1 : 1 < d) :
    d.Prime := by
  by_contra hp
  have hk : k ≠ 0 := by have := h.1; omega
  rcases h.2.2 d (Nat.mem_divisors.2 ⟨hd, hk⟩) hp with h' | h'
  · have := (Nat.Prime.even_iff h').1 hodd.add_one
    omega
  · have := (Nat.Prime.even_iff h').1 (Nat.Odd.sub_odd hodd odd_one)
    have hd3 : d = 3 := by omega
    exact hp (hd3 ▸ Nat.prime_three)

end OMA.P_oeis_a333197

open OMA.S_oeis_a333197 OMA.P_oeis_a333197 in
theorem OMA.solution : type_of% @OMA.S_oeis_a333197.main := by
  intro k h
  have hk : k ≠ 0 := by have := h.1; omega
  obtain ⟨i, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · have hmp := odd_dvd_prime h (dvd_mul_left _ _) hm h1
    have hi : i ≠ 0 := by
      rintro rfl
      exact h.2.1 (by simpa using hmp)
    have h2d : 2 * m ∣ 2 ^ i * m := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      exact ⟨2 ^ j, by rw [pow_succ]; ring⟩
    have h2np : ¬ (2 * m).Prime := Nat.not_prime_mul (by omega) (by omega)
    have hm2 : m ≠ 2 := by
      rintro rfl
      exact (by decide : ¬ Odd 2) hm
    have hA := h.2.2 _ (Nat.mem_divisors.2 ⟨h2d, hk⟩) h2np
    right; right; right; right
    exact ⟨i, 1, m, ⟨hmp, hA.symm⟩, hm2, by ring⟩
  · have hm1 : m = 1 := by
      obtain ⟨r, rfl⟩ := hm
      omega
    subst hm1
    rcases Nat.lt_or_ge i 6 with hi | hi
    · interval_cases i
      · right; right; right; right
        exact ⟨0, 0, 3, ⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
      · exact absurd (by norm_num) h.2.1
      · left; norm_num
      · right; left; norm_num
      · right; right; left; norm_num
      · right; right; right; left; norm_num
    · exfalso
      have h64 : 64 ∣ 2 ^ i * 1 := by
        rw [mul_one]
        exact (Nat.pow_dvd_pow 2 hi : 2 ^ 6 ∣ 2 ^ i)
      rcases h.2.2 64 (Nat.mem_divisors.2 ⟨h64, hk⟩) (by norm_num) with h' | h' <;>
        norm_num at h'
