import OMAStatements.S_oeis_a086004
import Mathlib

open OMA.S_oeis_a086004

-- R. J. Mathar's block factorization from OEIS A086004, Conjecture 1.
theorem OMA.solution : type_of% @OMA.S_oeis_a086004.main := by
  rintro p hp ⟨h, hh⟩
  have hd : numDigits p = 2 * h := by omega
  have h0 : h ≠ 0 := by
    rintro rfl
    exact hp.ne_zero (by simpa [numDigits, Nat.digits_eq_nil_iff_eq_zero] using hd)
  have e := Nat.mod_add_div p (10 ^ h)
  have : rot p = p % 10 ^ h * 10 ^ h + p / 10 ^ h := by
    simp [rot, hd, show 2 * h / 2 = h by omega, show 2 * h - h = h by omega, Nat.mod_one]
  rw [this, show p + _ = (10 ^ h + 1) * (p % 10 ^ h + p / 10 ^ h) by nth_rw 1 [← e]; ring]
  have := Nat.le_self_pow h0 10
  have : 2 ∣ 10 ^ h := dvd_pow (by norm_num) h0
  have := hp.eq_one_or_self_of_dvd 2
  have := hp.two_le
  refine Nat.not_prime_mul (by omega) fun s => ?_
  generalize p % 10 ^ h = r at e s
  generalize p / 10 ^ h = q at e s
  obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
  all_goals omega
