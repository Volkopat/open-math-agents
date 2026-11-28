import OMAReductions.R_oeis_a074777_R1

-- Step oeis-a074777.R1.H2: hypothesis H2 of reduction oeis-a074777.R1
-- Credit: @luciusacarr
-- H2 := ∀ n : ℕ, n = 2 ∨ n = 6 ∨ n = 30 ∨ n = 510 ∨ n = 131070 ∨ n = 8589934590 →   2 * sigma 1 (Nat.totient n) = n

/-! Each listed `n` is `2` times a product of the Fermat primes `3, 5, 17, 257, 65537`, so
multiplicativity of `φ` gives `φ(n) = 2^k` (`k = 0, 1, 3, 7, 15, 31`), and
`σ(2^k) = 2^(k+1) - 1`, hence `2 σ(φ(n)) = 2^(k+2) - 2 = n`. -/

open ArithmeticFunction

namespace OMA.S74777H2

theorem phi_mul_prime (m p : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    Nat.totient (m * p) = Nat.totient m * (p - 1) := by
  rw [Nat.totient_mul ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm))),
    Nat.totient_prime hp]

theorem sigma_two_pow (k : ℕ) : sigma 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rw [sigma_one_apply_prime_pow Nat.prime_two, Nat.geomSum_eq (le_refl 2)]
  simp

theorem p65537 : Nat.Prime 65537 := by norm_num
theorem p257 : Nat.Prime 257 := by norm_num

theorem phi2 : Nat.totient 2 = 2 ^ 0 := by decide
theorem phi6 : Nat.totient 6 = 2 ^ 1 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, phi_mul_prime 2 3 (by norm_num) (by norm_num), phi2]
  norm_num
theorem phi30 : Nat.totient 30 = 2 ^ 3 := by
  rw [show (30 : ℕ) = 6 * 5 by norm_num, phi_mul_prime 6 5 (by norm_num) (by norm_num), phi6]
  norm_num
theorem phi510 : Nat.totient 510 = 2 ^ 7 := by
  rw [show (510 : ℕ) = 30 * 17 by norm_num, phi_mul_prime 30 17 (by norm_num) (by norm_num), phi30]
  norm_num
theorem phi131070 : Nat.totient 131070 = 2 ^ 15 := by
  rw [show (131070 : ℕ) = 510 * 257 by norm_num, phi_mul_prime 510 257 p257 (by norm_num), phi510]
  norm_num
theorem phiBig : Nat.totient 8589934590 = 2 ^ 31 := by
  rw [show (8589934590 : ℕ) = 131070 * 65537 by norm_num,
    phi_mul_prime 131070 65537 p65537 (by norm_num), phi131070]
  norm_num

end OMA.S74777H2

open OMA.S74777H2 in
theorem OMA.solution : OMA.R_oeis_a074777_R1.H2 := by
  intro n hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [phi2, sigma_two_pow]; norm_num
  · rw [phi6, sigma_two_pow]; norm_num
  · rw [phi30, sigma_two_pow]; norm_num
  · rw [phi510, sigma_two_pow]; norm_num
  · rw [phi131070, sigma_two_pow]; norm_num
  · rw [phiBig, sigma_two_pow]; norm_num
