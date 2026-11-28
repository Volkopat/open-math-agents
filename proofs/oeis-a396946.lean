import OMAStatements.S_oeis_a396946
import Mathlib

namespace OMA.P_oeis_a396946

private lemma mod_pow_double {a e e2 m v w : ℕ} (he : e2 = 2 * e) (hv : a ^ e % m = v) (hw : v * v % m = w) :
    a ^ e2 % m = w := by
  rw [he, show 2 * e = e + e by omega, pow_add, Nat.mul_mod, hv, hw]

private lemma mod_pow_succ {a e e1 m v w : ℕ} (he : e1 = e + 1) (hv : a ^ e % m = v) (hw : v * a % m = w) :
    a ^ e1 % m = w := by
  rw [he, pow_succ, Nat.mul_mod, hv]
  have h1 : (v * (a % m)) % m = (v * a) % m := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  rw [h1, hw]

private lemma zmod_pow_eq_one {a e m : ℕ} (h : a ^ e % m = 1) :
    ((a : ℕ) : ZMod m) ^ e = 1 := by
  have h1 : ((a ^ e % m : ℕ) : ZMod m) = (1 : ZMod m) := by rw [h]; norm_num
  rw [ZMod.natCast_mod, Nat.cast_pow] at h1
  exact h1

private lemma zmod_pow_ne_one {a e m r : ℕ} (h : a ^ e % m = r) (hr : r ≠ 1 % m) :
    ((a : ℕ) : ZMod m) ^ e ≠ 1 := by
  intro heq
  have hmod : a ^ e ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one]
    exact heq
  have hmod' : a ^ e % m = 1 % m := hmod
  rw [h] at hmod'
  exact hr hmod'

private lemma prime_3463 : Nat.Prime 3463 := by
  apply lucas_primality 3463 ((3 : ℕ) : ZMod 3463)
  · rw [show (3463 - 1 : ℕ) = 3462 by norm_num]

    have h0_0 : 3 ^ 0 % 3463 = 1 := by norm_num
    have h0_1 : 3 ^ 0 % 3463 = 1 := mod_pow_double (by norm_num) h0_0 (by norm_num)
    have h0_2 : 3 ^ 1 % 3463 = 3 := mod_pow_succ (by norm_num) h0_1 (by norm_num)
    have h0_3 : 3 ^ 2 % 3463 = 9 := mod_pow_double (by norm_num) h0_2 (by norm_num)
    have h0_4 : 3 ^ 3 % 3463 = 27 := mod_pow_succ (by norm_num) h0_3 (by norm_num)
    have h0_5 : 3 ^ 6 % 3463 = 729 := mod_pow_double (by norm_num) h0_4 (by norm_num)
    have h0_6 : 3 ^ 12 % 3463 = 1602 := mod_pow_double (by norm_num) h0_5 (by norm_num)
    have h0_7 : 3 ^ 13 % 3463 = 1343 := mod_pow_succ (by norm_num) h0_6 (by norm_num)
    have h0_8 : 3 ^ 26 % 3463 = 2889 := mod_pow_double (by norm_num) h0_7 (by norm_num)
    have h0_9 : 3 ^ 27 % 3463 = 1741 := mod_pow_succ (by norm_num) h0_8 (by norm_num)
    have h0_10 : 3 ^ 54 % 3463 = 956 := mod_pow_double (by norm_num) h0_9 (by norm_num)
    have h0_11 : 3 ^ 108 % 3463 = 3167 := mod_pow_double (by norm_num) h0_10 (by norm_num)
    have h0_12 : 3 ^ 216 % 3463 = 1041 := mod_pow_double (by norm_num) h0_11 (by norm_num)
    have h0_13 : 3 ^ 432 % 3463 = 3225 := mod_pow_double (by norm_num) h0_12 (by norm_num)
    have h0_14 : 3 ^ 864 % 3463 = 1236 := mod_pow_double (by norm_num) h0_13 (by norm_num)
    have h0_15 : 3 ^ 865 % 3463 = 245 := mod_pow_succ (by norm_num) h0_14 (by norm_num)
    have h0_16 : 3 ^ 1730 % 3463 = 1154 := mod_pow_double (by norm_num) h0_15 (by norm_num)
    have h0_17 : 3 ^ 1731 % 3463 = 3462 := mod_pow_succ (by norm_num) h0_16 (by norm_num)
    have h0_18 : 3 ^ 3462 % 3463 = 1 := mod_pow_double (by norm_num) h0_17 (by norm_num)
    exact zmod_pow_eq_one h0_18
  · intro q hq hdvd
    have hfac : (3463 - 1 : ℕ) = 2 * (3 * 577) := by norm_num
    rw [hfac] at hdvd
    have hq_mem : q = 2 ∨ q = 3 ∨ q = 577 := by
      rcases hq.dvd_mul.mp hdvd with h2 | hrest
      · left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h2
      · rcases hq.dvd_mul.mp hrest with h3 | h577
        · right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h3
        · right; right; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h577
    rcases hq_mem with rfl | rfl | rfl

    · rw [show (3463 - 1) / 2 = 1731 by norm_num]
      have hq2_0 : 3 ^ 0 % 3463 = 1 := by norm_num
      have hq2_1 : 3 ^ 0 % 3463 = 1 := mod_pow_double (by norm_num) hq2_0 (by norm_num)
      have hq2_2 : 3 ^ 1 % 3463 = 3 := mod_pow_succ (by norm_num) hq2_1 (by norm_num)
      have hq2_3 : 3 ^ 2 % 3463 = 9 := mod_pow_double (by norm_num) hq2_2 (by norm_num)
      have hq2_4 : 3 ^ 3 % 3463 = 27 := mod_pow_succ (by norm_num) hq2_3 (by norm_num)
      have hq2_5 : 3 ^ 6 % 3463 = 729 := mod_pow_double (by norm_num) hq2_4 (by norm_num)
      have hq2_6 : 3 ^ 12 % 3463 = 1602 := mod_pow_double (by norm_num) hq2_5 (by norm_num)
      have hq2_7 : 3 ^ 13 % 3463 = 1343 := mod_pow_succ (by norm_num) hq2_6 (by norm_num)
      have hq2_8 : 3 ^ 26 % 3463 = 2889 := mod_pow_double (by norm_num) hq2_7 (by norm_num)
      have hq2_9 : 3 ^ 27 % 3463 = 1741 := mod_pow_succ (by norm_num) hq2_8 (by norm_num)
      have hq2_10 : 3 ^ 54 % 3463 = 956 := mod_pow_double (by norm_num) hq2_9 (by norm_num)
      have hq2_11 : 3 ^ 108 % 3463 = 3167 := mod_pow_double (by norm_num) hq2_10 (by norm_num)
      have hq2_12 : 3 ^ 216 % 3463 = 1041 := mod_pow_double (by norm_num) hq2_11 (by norm_num)
      have hq2_13 : 3 ^ 432 % 3463 = 3225 := mod_pow_double (by norm_num) hq2_12 (by norm_num)
      have hq2_14 : 3 ^ 864 % 3463 = 1236 := mod_pow_double (by norm_num) hq2_13 (by norm_num)
      have hq2_15 : 3 ^ 865 % 3463 = 245 := mod_pow_succ (by norm_num) hq2_14 (by norm_num)
      have hq2_16 : 3 ^ 1730 % 3463 = 1154 := mod_pow_double (by norm_num) hq2_15 (by norm_num)
      have hq2_17 : 3 ^ 1731 % 3463 = 3462 := mod_pow_succ (by norm_num) hq2_16 (by norm_num)
      exact zmod_pow_ne_one hq2_17 (by norm_num)
    · rw [show (3463 - 1) / 3 = 1154 by norm_num]
      have hq3_0 : 3 ^ 0 % 3463 = 1 := by norm_num
      have hq3_1 : 3 ^ 0 % 3463 = 1 := mod_pow_double (by norm_num) hq3_0 (by norm_num)
      have hq3_2 : 3 ^ 1 % 3463 = 3 := mod_pow_succ (by norm_num) hq3_1 (by norm_num)
      have hq3_3 : 3 ^ 2 % 3463 = 9 := mod_pow_double (by norm_num) hq3_2 (by norm_num)
      have hq3_4 : 3 ^ 4 % 3463 = 81 := mod_pow_double (by norm_num) hq3_3 (by norm_num)
      have hq3_5 : 3 ^ 8 % 3463 = 3098 := mod_pow_double (by norm_num) hq3_4 (by norm_num)
      have hq3_6 : 3 ^ 9 % 3463 = 2368 := mod_pow_succ (by norm_num) hq3_5 (by norm_num)
      have hq3_7 : 3 ^ 18 % 3463 = 827 := mod_pow_double (by norm_num) hq3_6 (by norm_num)
      have hq3_8 : 3 ^ 36 % 3463 = 1718 := mod_pow_double (by norm_num) hq3_7 (by norm_num)
      have hq3_9 : 3 ^ 72 % 3463 = 1048 := mod_pow_double (by norm_num) hq3_8 (by norm_num)
      have hq3_10 : 3 ^ 144 % 3463 = 533 := mod_pow_double (by norm_num) hq3_9 (by norm_num)
      have hq3_11 : 3 ^ 288 % 3463 = 123 := mod_pow_double (by norm_num) hq3_10 (by norm_num)
      have hq3_12 : 3 ^ 576 % 3463 = 1277 := mod_pow_double (by norm_num) hq3_11 (by norm_num)
      have hq3_13 : 3 ^ 577 % 3463 = 368 := mod_pow_succ (by norm_num) hq3_12 (by norm_num)
      have hq3_14 : 3 ^ 1154 % 3463 = 367 := mod_pow_double (by norm_num) hq3_13 (by norm_num)
      exact zmod_pow_ne_one hq3_14 (by norm_num)
    · rw [show (3463 - 1) / 577 = 6 by norm_num]
      have hq577_0 : 3 ^ 0 % 3463 = 1 := by norm_num
      have hq577_1 : 3 ^ 0 % 3463 = 1 := mod_pow_double (by norm_num) hq577_0 (by norm_num)
      have hq577_2 : 3 ^ 1 % 3463 = 3 := mod_pow_succ (by norm_num) hq577_1 (by norm_num)
      have hq577_3 : 3 ^ 2 % 3463 = 9 := mod_pow_double (by norm_num) hq577_2 (by norm_num)
      have hq577_4 : 3 ^ 3 % 3463 = 27 := mod_pow_succ (by norm_num) hq577_3 (by norm_num)
      have hq577_5 : 3 ^ 6 % 3463 = 729 := mod_pow_double (by norm_num) hq577_4 (by norm_num)
      exact zmod_pow_ne_one hq577_5 (by norm_num)

private lemma prime_5736805801 : Nat.Prime 5736805801 := by
  apply lucas_primality 5736805801 ((35 : ℕ) : ZMod 5736805801)
  · rw [show (5736805801 - 1 : ℕ) = 5736805800 by norm_num]

    have hp0_0 : 35 ^ 0 % 5736805801 = 1 := by norm_num
    have hp0_1 : 35 ^ 0 % 5736805801 = 1 := mod_pow_double (by norm_num) hp0_0 (by norm_num)
    have hp0_2 : 35 ^ 1 % 5736805801 = 35 := mod_pow_succ (by norm_num) hp0_1 (by norm_num)
    have hp0_3 : 35 ^ 2 % 5736805801 = 1225 := mod_pow_double (by norm_num) hp0_2 (by norm_num)
    have hp0_4 : 35 ^ 4 % 5736805801 = 1500625 := mod_pow_double (by norm_num) hp0_3 (by norm_num)
    have hp0_5 : 35 ^ 5 % 5736805801 = 52521875 := mod_pow_succ (by norm_num) hp0_4 (by norm_num)
    have hp0_6 : 35 ^ 10 % 5736805801 = 4284104775 := mod_pow_double (by norm_num) hp0_5 (by norm_num)
    have hp0_7 : 35 ^ 20 % 5736805801 = 1925918070 := mod_pow_double (by norm_num) hp0_6 (by norm_num)
    have hp0_8 : 35 ^ 21 % 5736805801 = 4302268639 := mod_pow_succ (by norm_num) hp0_7 (by norm_num)
    have hp0_9 : 35 ^ 42 % 5736805801 = 476115606 := mod_pow_double (by norm_num) hp0_8 (by norm_num)
    have hp0_10 : 35 ^ 84 % 5736805801 = 4026089901 := mod_pow_double (by norm_num) hp0_9 (by norm_num)
    have hp0_11 : 35 ^ 85 % 5736805801 = 3229807311 := mod_pow_succ (by norm_num) hp0_10 (by norm_num)
    have hp0_12 : 35 ^ 170 % 5736805801 = 1633560087 := mod_pow_double (by norm_num) hp0_11 (by norm_num)
    have hp0_13 : 35 ^ 340 % 5736805801 = 3673276815 := mod_pow_double (by norm_num) hp0_12 (by norm_num)
    have hp0_14 : 35 ^ 341 % 5736805801 = 2354960903 := mod_pow_succ (by norm_num) hp0_13 (by norm_num)
    have hp0_15 : 35 ^ 682 % 5736805801 = 3647601288 := mod_pow_double (by norm_num) hp0_14 (by norm_num)
    have hp0_16 : 35 ^ 683 % 5736805801 = 1456317458 := mod_pow_succ (by norm_num) hp0_15 (by norm_num)
    have hp0_17 : 35 ^ 1366 % 5736805801 = 246057338 := mod_pow_double (by norm_num) hp0_16 (by norm_num)
    have hp0_18 : 35 ^ 1367 % 5736805801 = 2875201029 := mod_pow_succ (by norm_num) hp0_17 (by norm_num)
    have hp0_19 : 35 ^ 2734 % 5736805801 = 3146174007 := mod_pow_double (by norm_num) hp0_18 (by norm_num)
    have hp0_20 : 35 ^ 2735 % 5736805801 = 1116780026 := mod_pow_succ (by norm_num) hp0_19 (by norm_num)
    have hp0_21 : 35 ^ 5470 % 5736805801 = 5226141080 := mod_pow_double (by norm_num) hp0_20 (by norm_num)
    have hp0_22 : 35 ^ 5471 % 5736805801 = 5073957969 := mod_pow_succ (by norm_num) hp0_21 (by norm_num)
    have hp0_23 : 35 ^ 10942 % 5736805801 = 1258583988 := mod_pow_double (by norm_num) hp0_22 (by norm_num)
    have hp0_24 : 35 ^ 21884 % 5736805801 = 3047177439 := mod_pow_double (by norm_num) hp0_23 (by norm_num)
    have hp0_25 : 35 ^ 43768 % 5736805801 = 3910123830 := mod_pow_double (by norm_num) hp0_24 (by norm_num)
    have hp0_26 : 35 ^ 87536 % 5736805801 = 1312182672 := mod_pow_double (by norm_num) hp0_25 (by norm_num)
    have hp0_27 : 35 ^ 175072 % 5736805801 = 1817090737 := mod_pow_double (by norm_num) hp0_26 (by norm_num)
    have hp0_28 : 35 ^ 175073 % 5736805801 = 493311984 := mod_pow_succ (by norm_num) hp0_27 (by norm_num)
    have hp0_29 : 35 ^ 350146 % 5736805801 = 225369210 := mod_pow_double (by norm_num) hp0_28 (by norm_num)
    have hp0_30 : 35 ^ 700292 % 5736805801 = 238794918 := mod_pow_double (by norm_num) hp0_29 (by norm_num)
    have hp0_31 : 35 ^ 700293 % 5736805801 = 2621016329 := mod_pow_succ (by norm_num) hp0_30 (by norm_num)
    have hp0_32 : 35 ^ 1400586 % 5736805801 = 1985788585 := mod_pow_double (by norm_num) hp0_31 (by norm_num)
    have hp0_33 : 35 ^ 1400587 % 5736805801 = 660930863 := mod_pow_succ (by norm_num) hp0_32 (by norm_num)
    have hp0_34 : 35 ^ 2801174 % 5736805801 = 162646077 := mod_pow_double (by norm_num) hp0_33 (by norm_num)
    have hp0_35 : 35 ^ 5602348 % 5736805801 = 3876133097 := mod_pow_double (by norm_num) hp0_34 (by norm_num)
    have hp0_36 : 35 ^ 5602349 % 5736805801 = 3718124972 := mod_pow_succ (by norm_num) hp0_35 (by norm_num)
    have hp0_37 : 35 ^ 11204698 % 5736805801 = 150646444 := mod_pow_double (by norm_num) hp0_36 (by norm_num)
    have hp0_38 : 35 ^ 22409396 % 5736805801 = 548747415 := mod_pow_double (by norm_num) hp0_37 (by norm_num)
    have hp0_39 : 35 ^ 22409397 % 5736805801 = 1995742122 := mod_pow_succ (by norm_num) hp0_38 (by norm_num)
    have hp0_40 : 35 ^ 44818794 % 5736805801 = 3294085220 := mod_pow_double (by norm_num) hp0_39 (by norm_num)
    have hp0_41 : 35 ^ 44818795 % 5736805801 = 556866680 := mod_pow_succ (by norm_num) hp0_40 (by norm_num)
    have hp0_42 : 35 ^ 89637590 % 5736805801 = 3126137243 := mod_pow_double (by norm_num) hp0_41 (by norm_num)
    have hp0_43 : 35 ^ 179275180 % 5736805801 = 4924210567 := mod_pow_double (by norm_num) hp0_42 (by norm_num)
    have hp0_44 : 35 ^ 179275181 % 5736805801 = 243195815 := mod_pow_succ (by norm_num) hp0_43 (by norm_num)
    have hp0_45 : 35 ^ 358550362 % 5736805801 = 2663495620 := mod_pow_double (by norm_num) hp0_44 (by norm_num)
    have hp0_46 : 35 ^ 717100724 % 5736805801 = 4663687151 := mod_pow_double (by norm_num) hp0_45 (by norm_num)
    have hp0_47 : 35 ^ 717100725 % 5736805801 = 2598487857 := mod_pow_succ (by norm_num) hp0_46 (by norm_num)
    have hp0_48 : 35 ^ 1434201450 % 5736805801 = 846818 := mod_pow_double (by norm_num) hp0_47 (by norm_num)
    have hp0_49 : 35 ^ 2868402900 % 5736805801 = 5736805800 := mod_pow_double (by norm_num) hp0_48 (by norm_num)
    have hp0_50 : 35 ^ 5736805800 % 5736805801 = 1 := mod_pow_double (by norm_num) hp0_49 (by norm_num)
    exact zmod_pow_eq_one hp0_50
  · intro q hq hdvd
    have hfac : (5736805801 - 1 : ℕ) = 2 ^ 3 * (3 * (5 ^ 2 * (11 * (251 * 3463)))) := by norm_num
    rw [hfac] at hdvd
    have hq_mem : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 11 ∨ q = 251 ∨ q = 3463 := by
      rcases hq.dvd_mul.mp hdvd with h2 | h1
      · left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h2)
      · rcases hq.dvd_mul.mp h1 with h3 | h2
        · right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h3
        · rcases hq.dvd_mul.mp h2 with h5 | h3
          · right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h5)
          · rcases hq.dvd_mul.mp h3 with h11 | h4
            · right; right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h11
            · rcases hq.dvd_mul.mp h4 with h251 | h3463
              · right; right; right; right; left; exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h251
              · right; right; right; right; right; exact (Nat.prime_dvd_prime_iff_eq hq prime_3463).mp h3463
    rcases hq_mem with rfl | rfl | rfl | rfl | rfl | rfl

    · rw [show (5736805801 - 1) / 2 = 2868402900 by norm_num]
      have hpq2_0 : 35 ^ 0 % 5736805801 = 1 := by norm_num
      have hpq2_1 : 35 ^ 0 % 5736805801 = 1 := mod_pow_double (by norm_num) hpq2_0 (by norm_num)
      have hpq2_2 : 35 ^ 1 % 5736805801 = 35 := mod_pow_succ (by norm_num) hpq2_1 (by norm_num)
      have hpq2_3 : 35 ^ 2 % 5736805801 = 1225 := mod_pow_double (by norm_num) hpq2_2 (by norm_num)
      have hpq2_4 : 35 ^ 4 % 5736805801 = 1500625 := mod_pow_double (by norm_num) hpq2_3 (by norm_num)
      have hpq2_5 : 35 ^ 5 % 5736805801 = 52521875 := mod_pow_succ (by norm_num) hpq2_4 (by norm_num)
      have hpq2_6 : 35 ^ 10 % 5736805801 = 4284104775 := mod_pow_double (by norm_num) hpq2_5 (by norm_num)
      have hpq2_7 : 35 ^ 20 % 5736805801 = 1925918070 := mod_pow_double (by norm_num) hpq2_6 (by norm_num)
      have hpq2_8 : 35 ^ 21 % 5736805801 = 4302268639 := mod_pow_succ (by norm_num) hpq2_7 (by norm_num)
      have hpq2_9 : 35 ^ 42 % 5736805801 = 476115606 := mod_pow_double (by norm_num) hpq2_8 (by norm_num)
      have hpq2_10 : 35 ^ 84 % 5736805801 = 4026089901 := mod_pow_double (by norm_num) hpq2_9 (by norm_num)
      have hpq2_11 : 35 ^ 85 % 5736805801 = 3229807311 := mod_pow_succ (by norm_num) hpq2_10 (by norm_num)
      have hpq2_12 : 35 ^ 170 % 5736805801 = 1633560087 := mod_pow_double (by norm_num) hpq2_11 (by norm_num)
      have hpq2_13 : 35 ^ 340 % 5736805801 = 3673276815 := mod_pow_double (by norm_num) hpq2_12 (by norm_num)
      have hpq2_14 : 35 ^ 341 % 5736805801 = 2354960903 := mod_pow_succ (by norm_num) hpq2_13 (by norm_num)
      have hpq2_15 : 35 ^ 682 % 5736805801 = 3647601288 := mod_pow_double (by norm_num) hpq2_14 (by norm_num)
      have hpq2_16 : 35 ^ 683 % 5736805801 = 1456317458 := mod_pow_succ (by norm_num) hpq2_15 (by norm_num)
      have hpq2_17 : 35 ^ 1366 % 5736805801 = 246057338 := mod_pow_double (by norm_num) hpq2_16 (by norm_num)
      have hpq2_18 : 35 ^ 1367 % 5736805801 = 2875201029 := mod_pow_succ (by norm_num) hpq2_17 (by norm_num)
      have hpq2_19 : 35 ^ 2734 % 5736805801 = 3146174007 := mod_pow_double (by norm_num) hpq2_18 (by norm_num)
      have hpq2_20 : 35 ^ 2735 % 5736805801 = 1116780026 := mod_pow_succ (by norm_num) hpq2_19 (by norm_num)
      have hpq2_21 : 35 ^ 5470 % 5736805801 = 5226141080 := mod_pow_double (by norm_num) hpq2_20 (by norm_num)
      have hpq2_22 : 35 ^ 5471 % 5736805801 = 5073957969 := mod_pow_succ (by norm_num) hpq2_21 (by norm_num)
      have hpq2_23 : 35 ^ 10942 % 5736805801 = 1258583988 := mod_pow_double (by norm_num) hpq2_22 (by norm_num)
      have hpq2_24 : 35 ^ 21884 % 5736805801 = 3047177439 := mod_pow_double (by norm_num) hpq2_23 (by norm_num)
      have hpq2_25 : 35 ^ 43768 % 5736805801 = 3910123830 := mod_pow_double (by norm_num) hpq2_24 (by norm_num)
      have hpq2_26 : 35 ^ 87536 % 5736805801 = 1312182672 := mod_pow_double (by norm_num) hpq2_25 (by norm_num)
      have hpq2_27 : 35 ^ 175072 % 5736805801 = 1817090737 := mod_pow_double (by norm_num) hpq2_26 (by norm_num)
      have hpq2_28 : 35 ^ 175073 % 5736805801 = 493311984 := mod_pow_succ (by norm_num) hpq2_27 (by norm_num)
      have hpq2_29 : 35 ^ 350146 % 5736805801 = 225369210 := mod_pow_double (by norm_num) hpq2_28 (by norm_num)
      have hpq2_30 : 35 ^ 700292 % 5736805801 = 238794918 := mod_pow_double (by norm_num) hpq2_29 (by norm_num)
      have hpq2_31 : 35 ^ 700293 % 5736805801 = 2621016329 := mod_pow_succ (by norm_num) hpq2_30 (by norm_num)
      have hpq2_32 : 35 ^ 1400586 % 5736805801 = 1985788585 := mod_pow_double (by norm_num) hpq2_31 (by norm_num)
      have hpq2_33 : 35 ^ 1400587 % 5736805801 = 660930863 := mod_pow_succ (by norm_num) hpq2_32 (by norm_num)
      have hpq2_34 : 35 ^ 2801174 % 5736805801 = 162646077 := mod_pow_double (by norm_num) hpq2_33 (by norm_num)
      have hpq2_35 : 35 ^ 5602348 % 5736805801 = 3876133097 := mod_pow_double (by norm_num) hpq2_34 (by norm_num)
      have hpq2_36 : 35 ^ 5602349 % 5736805801 = 3718124972 := mod_pow_succ (by norm_num) hpq2_35 (by norm_num)
      have hpq2_37 : 35 ^ 11204698 % 5736805801 = 150646444 := mod_pow_double (by norm_num) hpq2_36 (by norm_num)
      have hpq2_38 : 35 ^ 22409396 % 5736805801 = 548747415 := mod_pow_double (by norm_num) hpq2_37 (by norm_num)
      have hpq2_39 : 35 ^ 22409397 % 5736805801 = 1995742122 := mod_pow_succ (by norm_num) hpq2_38 (by norm_num)
      have hpq2_40 : 35 ^ 44818794 % 5736805801 = 3294085220 := mod_pow_double (by norm_num) hpq2_39 (by norm_num)
      have hpq2_41 : 35 ^ 44818795 % 5736805801 = 556866680 := mod_pow_succ (by norm_num) hpq2_40 (by norm_num)
      have hpq2_42 : 35 ^ 89637590 % 5736805801 = 3126137243 := mod_pow_double (by norm_num) hpq2_41 (by norm_num)
      have hpq2_43 : 35 ^ 179275180 % 5736805801 = 4924210567 := mod_pow_double (by norm_num) hpq2_42 (by norm_num)
      have hpq2_44 : 35 ^ 179275181 % 5736805801 = 243195815 := mod_pow_succ (by norm_num) hpq2_43 (by norm_num)
      have hpq2_45 : 35 ^ 358550362 % 5736805801 = 2663495620 := mod_pow_double (by norm_num) hpq2_44 (by norm_num)
      have hpq2_46 : 35 ^ 717100724 % 5736805801 = 4663687151 := mod_pow_double (by norm_num) hpq2_45 (by norm_num)
      have hpq2_47 : 35 ^ 717100725 % 5736805801 = 2598487857 := mod_pow_succ (by norm_num) hpq2_46 (by norm_num)
      have hpq2_48 : 35 ^ 1434201450 % 5736805801 = 846818 := mod_pow_double (by norm_num) hpq2_47 (by norm_num)
      have hpq2_49 : 35 ^ 2868402900 % 5736805801 = 5736805800 := mod_pow_double (by norm_num) hpq2_48 (by norm_num)
      exact zmod_pow_ne_one hpq2_49 (by norm_num)
    · rw [show (5736805801 - 1) / 3 = 1912268600 by norm_num]
      have hpq3_0 : 35 ^ 0 % 5736805801 = 1 := by norm_num
      have hpq3_1 : 35 ^ 0 % 5736805801 = 1 := mod_pow_double (by norm_num) hpq3_0 (by norm_num)
      have hpq3_2 : 35 ^ 1 % 5736805801 = 35 := mod_pow_succ (by norm_num) hpq3_1 (by norm_num)
      have hpq3_3 : 35 ^ 2 % 5736805801 = 1225 := mod_pow_double (by norm_num) hpq3_2 (by norm_num)
      have hpq3_4 : 35 ^ 3 % 5736805801 = 42875 := mod_pow_succ (by norm_num) hpq3_3 (by norm_num)
      have hpq3_5 : 35 ^ 6 % 5736805801 = 1838265625 := mod_pow_double (by norm_num) hpq3_4 (by norm_num)
      have hpq3_6 : 35 ^ 7 % 5736805801 = 1234433064 := mod_pow_succ (by norm_num) hpq3_5 (by norm_num)
      have hpq3_7 : 35 ^ 14 % 5736805801 = 3780015546 := mod_pow_double (by norm_num) hpq3_6 (by norm_num)
      have hpq3_8 : 35 ^ 28 % 5736805801 = 1693279336 := mod_pow_double (by norm_num) hpq3_7 (by norm_num)
      have hpq3_9 : 35 ^ 56 % 5736805801 = 2685311665 := mod_pow_double (by norm_num) hpq3_8 (by norm_num)
      have hpq3_10 : 35 ^ 112 % 5736805801 = 5433209620 := mod_pow_double (by norm_num) hpq3_9 (by norm_num)
      have hpq3_11 : 35 ^ 113 % 5736805801 = 847745267 := mod_pow_succ (by norm_num) hpq3_10 (by norm_num)
      have hpq3_12 : 35 ^ 226 % 5736805801 = 1487007389 := mod_pow_double (by norm_num) hpq3_11 (by norm_num)
      have hpq3_13 : 35 ^ 227 % 5736805801 = 414006406 := mod_pow_succ (by norm_num) hpq3_12 (by norm_num)
      have hpq3_14 : 35 ^ 454 % 5736805801 = 3625775356 := mod_pow_double (by norm_num) hpq3_13 (by norm_num)
      have hpq3_15 : 35 ^ 455 % 5736805801 = 692409838 := mod_pow_succ (by norm_num) hpq3_14 (by norm_num)
      have hpq3_16 : 35 ^ 910 % 5736805801 = 221420507 := mod_pow_double (by norm_num) hpq3_15 (by norm_num)
      have hpq3_17 : 35 ^ 911 % 5736805801 = 2012911944 := mod_pow_succ (by norm_num) hpq3_16 (by norm_num)
      have hpq3_18 : 35 ^ 1822 % 5736805801 = 1736027076 := mod_pow_double (by norm_num) hpq3_17 (by norm_num)
      have hpq3_19 : 35 ^ 1823 % 5736805801 = 3392889650 := mod_pow_succ (by norm_num) hpq3_18 (by norm_num)
      have hpq3_20 : 35 ^ 3646 % 5736805801 = 5271145966 := mod_pow_double (by norm_num) hpq3_19 (by norm_num)
      have hpq3_21 : 35 ^ 3647 % 5736805801 = 912323178 := mod_pow_succ (by norm_num) hpq3_20 (by norm_num)
      have hpq3_22 : 35 ^ 7294 % 5736805801 = 1430322696 := mod_pow_double (by norm_num) hpq3_21 (by norm_num)
      have hpq3_23 : 35 ^ 14588 % 5736805801 = 5339574209 := mod_pow_double (by norm_num) hpq3_22 (by norm_num)
      have hpq3_24 : 35 ^ 14589 % 5736805801 = 3307311683 := mod_pow_succ (by norm_num) hpq3_23 (by norm_num)
      have hpq3_25 : 35 ^ 29178 % 5736805801 = 275283434 := mod_pow_double (by norm_num) hpq3_24 (by norm_num)
      have hpq3_26 : 35 ^ 58356 % 5736805801 = 1757884746 := mod_pow_double (by norm_num) hpq3_25 (by norm_num)
      have hpq3_27 : 35 ^ 58357 % 5736805801 = 4157908100 := mod_pow_succ (by norm_num) hpq3_26 (by norm_num)
      have hpq3_28 : 35 ^ 116714 % 5736805801 = 4065673321 := mod_pow_double (by norm_num) hpq3_27 (by norm_num)
      have hpq3_29 : 35 ^ 116715 % 5736805801 = 4615227011 := mod_pow_succ (by norm_num) hpq3_28 (by norm_num)
      have hpq3_30 : 35 ^ 233430 % 5736805801 = 958689945 := mod_pow_double (by norm_num) hpq3_29 (by norm_num)
      have hpq3_31 : 35 ^ 233431 % 5736805801 = 4870119070 := mod_pow_succ (by norm_num) hpq3_30 (by norm_num)
      have hpq3_32 : 35 ^ 466862 % 5736805801 = 4488344846 := mod_pow_double (by norm_num) hpq3_31 (by norm_num)
      have hpq3_33 : 35 ^ 933724 % 5736805801 = 4645992593 := mod_pow_double (by norm_num) hpq3_32 (by norm_num)
      have hpq3_34 : 35 ^ 1867448 % 5736805801 = 4946454018 := mod_pow_double (by norm_num) hpq3_33 (by norm_num)
      have hpq3_35 : 35 ^ 1867449 % 5736805801 = 1021716600 := mod_pow_succ (by norm_num) hpq3_34 (by norm_num)
      have hpq3_36 : 35 ^ 3734898 % 5736805801 = 1601575790 := mod_pow_double (by norm_num) hpq3_35 (by norm_num)
      have hpq3_37 : 35 ^ 3734899 % 5736805801 = 4423900441 := mod_pow_succ (by norm_num) hpq3_36 (by norm_num)
      have hpq3_38 : 35 ^ 7469798 % 5736805801 = 5652816461 := mod_pow_double (by norm_num) hpq3_37 (by norm_num)
      have hpq3_39 : 35 ^ 7469799 % 5736805801 = 2797178901 := mod_pow_succ (by norm_num) hpq3_38 (by norm_num)
      have hpq3_40 : 35 ^ 14939598 % 5736805801 = 88953285 := mod_pow_double (by norm_num) hpq3_39 (by norm_num)
      have hpq3_41 : 35 ^ 29879196 % 5736805801 = 2459864741 := mod_pow_double (by norm_num) hpq3_40 (by norm_num)
      have hpq3_42 : 35 ^ 59758392 % 5736805801 = 5233594749 := mod_pow_double (by norm_num) hpq3_41 (by norm_num)
      have hpq3_43 : 35 ^ 59758393 % 5736805801 = 5334836384 := mod_pow_succ (by norm_num) hpq3_42 (by norm_num)
      have hpq3_44 : 35 ^ 119516786 % 5736805801 = 5043057693 := mod_pow_double (by norm_num) hpq3_43 (by norm_num)
      have hpq3_45 : 35 ^ 119516787 % 5736805801 = 4402845225 := mod_pow_succ (by norm_num) hpq3_44 (by norm_num)
      have hpq3_46 : 35 ^ 239033574 % 5736805801 = 2021184913 := mod_pow_double (by norm_num) hpq3_45 (by norm_num)
      have hpq3_47 : 35 ^ 239033575 % 5736805801 = 1899802343 := mod_pow_succ (by norm_num) hpq3_46 (by norm_num)
      have hpq3_48 : 35 ^ 478067150 % 5736805801 = 689866131 := mod_pow_double (by norm_num) hpq3_47 (by norm_num)
      have hpq3_49 : 35 ^ 956134300 % 5736805801 = 648993727 := mod_pow_double (by norm_num) hpq3_48 (by norm_num)
      have hpq3_50 : 35 ^ 1912268600 % 5736805801 = 648993726 := mod_pow_double (by norm_num) hpq3_49 (by norm_num)
      exact zmod_pow_ne_one hpq3_50 (by norm_num)
    · rw [show (5736805801 - 1) / 5 = 1147361160 by norm_num]
      have hpq5_0 : 35 ^ 0 % 5736805801 = 1 := by norm_num
      have hpq5_1 : 35 ^ 0 % 5736805801 = 1 := mod_pow_double (by norm_num) hpq5_0 (by norm_num)
      have hpq5_2 : 35 ^ 1 % 5736805801 = 35 := mod_pow_succ (by norm_num) hpq5_1 (by norm_num)
      have hpq5_3 : 35 ^ 2 % 5736805801 = 1225 := mod_pow_double (by norm_num) hpq5_2 (by norm_num)
      have hpq5_4 : 35 ^ 4 % 5736805801 = 1500625 := mod_pow_double (by norm_num) hpq5_3 (by norm_num)
      have hpq5_5 : 35 ^ 8 % 5736805801 = 3047516633 := mod_pow_double (by norm_num) hpq5_4 (by norm_num)
      have hpq5_6 : 35 ^ 16 % 5736805801 = 916762443 := mod_pow_double (by norm_num) hpq5_5 (by norm_num)
      have hpq5_7 : 35 ^ 17 % 5736805801 = 3402656500 := mod_pow_succ (by norm_num) hpq5_6 (by norm_num)
      have hpq5_8 : 35 ^ 34 % 5736805801 = 5413308922 := mod_pow_double (by norm_num) hpq5_7 (by norm_num)
      have hpq5_9 : 35 ^ 68 % 5736805801 = 4455090343 := mod_pow_double (by norm_num) hpq5_8 (by norm_num)
      have hpq5_10 : 35 ^ 136 % 5736805801 = 803753075 := mod_pow_double (by norm_num) hpq5_9 (by norm_num)
      have hpq5_11 : 35 ^ 272 % 5736805801 = 620072095 := mod_pow_double (by norm_num) hpq5_10 (by norm_num)
      have hpq5_12 : 35 ^ 273 % 5736805801 = 4492105922 := mod_pow_succ (by norm_num) hpq5_11 (by norm_num)
      have hpq5_13 : 35 ^ 546 % 5736805801 = 1244586336 := mod_pow_double (by norm_num) hpq5_12 (by norm_num)
      have hpq5_14 : 35 ^ 547 % 5736805801 = 3402881153 := mod_pow_succ (by norm_num) hpq5_13 (by norm_num)
      have hpq5_15 : 35 ^ 1094 % 5736805801 = 2433672826 := mod_pow_double (by norm_num) hpq5_14 (by norm_num)
      have hpq5_16 : 35 ^ 2188 % 5736805801 = 3807562640 := mod_pow_double (by norm_num) hpq5_15 (by norm_num)
      have hpq5_17 : 35 ^ 4376 % 5736805801 = 2088779655 := mod_pow_double (by norm_num) hpq5_16 (by norm_num)
      have hpq5_18 : 35 ^ 8752 % 5736805801 = 3123200399 := mod_pow_double (by norm_num) hpq5_17 (by norm_num)
      have hpq5_19 : 35 ^ 8753 % 5736805801 = 312703746 := mod_pow_succ (by norm_num) hpq5_18 (by norm_num)
      have hpq5_20 : 35 ^ 17506 % 5736805801 = 1619813755 := mod_pow_double (by norm_num) hpq5_19 (by norm_num)
      have hpq5_21 : 35 ^ 17507 % 5736805801 = 5062229216 := mod_pow_succ (by norm_num) hpq5_20 (by norm_num)
      have hpq5_22 : 35 ^ 35014 % 5736805801 = 1695897659 := mod_pow_double (by norm_num) hpq5_21 (by norm_num)
      have hpq5_23 : 35 ^ 70028 % 5736805801 = 1919531603 := mod_pow_double (by norm_num) hpq5_22 (by norm_num)
      have hpq5_24 : 35 ^ 70029 % 5736805801 = 4078742294 := mod_pow_succ (by norm_num) hpq5_23 (by norm_num)
      have hpq5_25 : 35 ^ 140058 % 5736805801 = 3074000497 := mod_pow_double (by norm_num) hpq5_24 (by norm_num)
      have hpq5_26 : 35 ^ 280116 % 5736805801 = 1752206286 := mod_pow_double (by norm_num) hpq5_25 (by norm_num)
      have hpq5_27 : 35 ^ 280117 % 5736805801 = 3959162000 := mod_pow_succ (by norm_num) hpq5_26 (by norm_num)
      have hpq5_28 : 35 ^ 560234 % 5736805801 = 2423213580 := mod_pow_double (by norm_num) hpq5_27 (by norm_num)
      have hpq5_29 : 35 ^ 1120468 % 5736805801 = 3566561356 := mod_pow_double (by norm_num) hpq5_28 (by norm_num)
      have hpq5_30 : 35 ^ 1120469 % 5736805801 = 4356725639 := mod_pow_succ (by norm_num) hpq5_29 (by norm_num)
      have hpq5_31 : 35 ^ 2240938 % 5736805801 = 835400143 := mod_pow_double (by norm_num) hpq5_30 (by norm_num)
      have hpq5_32 : 35 ^ 2240939 % 5736805801 = 554976000 := mod_pow_succ (by norm_num) hpq5_31 (by norm_num)
      have hpq5_33 : 35 ^ 4481878 % 5736805801 = 2157575273 := mod_pow_double (by norm_num) hpq5_32 (by norm_num)
      have hpq5_34 : 35 ^ 4481879 % 5736805801 = 936659142 := mod_pow_succ (by norm_num) hpq5_33 (by norm_num)
      have hpq5_35 : 35 ^ 8963758 % 5736805801 = 359802253 := mod_pow_double (by norm_num) hpq5_34 (by norm_num)
      have hpq5_36 : 35 ^ 8963759 % 5736805801 = 1119467253 := mod_pow_succ (by norm_num) hpq5_35 (by norm_num)
      have hpq5_37 : 35 ^ 17927518 % 5736805801 = 5216398913 := mod_pow_double (by norm_num) hpq5_36 (by norm_num)
      have hpq5_38 : 35 ^ 35855036 % 5736805801 = 36033509 := mod_pow_double (by norm_num) hpq5_37 (by norm_num)
      have hpq5_39 : 35 ^ 71710072 % 5736805801 = 2513912751 := mod_pow_double (by norm_num) hpq5_38 (by norm_num)
      have hpq5_40 : 35 ^ 143420144 % 5736805801 = 2209710956 := mod_pow_double (by norm_num) hpq5_39 (by norm_num)
      have hpq5_41 : 35 ^ 143420145 % 5736805801 = 2761408047 := mod_pow_succ (by norm_num) hpq5_40 (by norm_num)
      have hpq5_42 : 35 ^ 286840290 % 5736805801 = 3739690895 := mod_pow_double (by norm_num) hpq5_41 (by norm_num)
      have hpq5_43 : 35 ^ 573680580 % 5736805801 = 4908147105 := mod_pow_double (by norm_num) hpq5_42 (by norm_num)
      have hpq5_44 : 35 ^ 1147361160 % 5736805801 = 3105371976 := mod_pow_double (by norm_num) hpq5_43 (by norm_num)
      exact zmod_pow_ne_one hpq5_44 (by norm_num)
    · rw [show (5736805801 - 1) / 11 = 521527800 by norm_num]
      have hpq11_0 : 35 ^ 0 % 5736805801 = 1 := by norm_num
      have hpq11_1 : 35 ^ 0 % 5736805801 = 1 := mod_pow_double (by norm_num) hpq11_0 (by norm_num)
      have hpq11_2 : 35 ^ 1 % 5736805801 = 35 := mod_pow_succ (by norm_num) hpq11_1 (by norm_num)
      have hpq11_3 : 35 ^ 2 % 5736805801 = 1225 := mod_pow_double (by norm_num) hpq11_2 (by norm_num)
      have hpq11_4 : 35 ^ 3 % 5736805801 = 42875 := mod_pow_succ (by norm_num) hpq11_3 (by norm_num)
      have hpq11_5 : 35 ^ 6 % 5736805801 = 1838265625 := mod_pow_double (by norm_num) hpq11_4 (by norm_num)
      have hpq11_6 : 35 ^ 7 % 5736805801 = 1234433064 := mod_pow_succ (by norm_num) hpq11_5 (by norm_num)
      have hpq11_7 : 35 ^ 14 % 5736805801 = 3780015546 := mod_pow_double (by norm_num) hpq11_6 (by norm_num)
      have hpq11_8 : 35 ^ 15 % 5736805801 = 354010687 := mod_pow_succ (by norm_num) hpq11_7 (by norm_num)
      have hpq11_9 : 35 ^ 30 % 5736805801 = 3280292439 := mod_pow_double (by norm_num) hpq11_8 (by norm_num)
      have hpq11_10 : 35 ^ 31 % 5736805801 = 74119345 := mod_pow_succ (by norm_num) hpq11_9 (by norm_num)
      have hpq11_11 : 35 ^ 62 % 5736805801 = 3068881206 := mod_pow_double (by norm_num) hpq11_10 (by norm_num)
      have hpq11_12 : 35 ^ 124 % 5736805801 = 4412665970 := mod_pow_double (by norm_num) hpq11_11 (by norm_num)
      have hpq11_13 : 35 ^ 248 % 5736805801 = 1647474257 := mod_pow_double (by norm_num) hpq11_12 (by norm_num)
      have hpq11_14 : 35 ^ 496 % 5736805801 = 3795811405 := mod_pow_double (by norm_num) hpq11_13 (by norm_num)
      have hpq11_15 : 35 ^ 497 % 5736805801 = 906865752 := mod_pow_succ (by norm_num) hpq11_14 (by norm_num)
      have hpq11_16 : 35 ^ 994 % 5736805801 = 5636815912 := mod_pow_double (by norm_num) hpq11_15 (by norm_num)
      have hpq11_17 : 35 ^ 1988 % 5736805801 = 4698782944 := mod_pow_double (by norm_num) hpq11_16 (by norm_num)
      have hpq11_18 : 35 ^ 1989 % 5736805801 = 3826840612 := mod_pow_succ (by norm_num) hpq11_17 (by norm_num)
      have hpq11_19 : 35 ^ 3978 % 5736805801 = 433250337 := mod_pow_double (by norm_num) hpq11_18 (by norm_num)
      have hpq11_20 : 35 ^ 7956 % 5736805801 = 1107553193 := mod_pow_double (by norm_num) hpq11_19 (by norm_num)
      have hpq11_21 : 35 ^ 7957 % 5736805801 = 4343526949 := mod_pow_succ (by norm_num) hpq11_20 (by norm_num)
      have hpq11_22 : 35 ^ 15914 % 5736805801 = 1891984526 := mod_pow_double (by norm_num) hpq11_21 (by norm_num)
      have hpq11_23 : 35 ^ 15915 % 5736805801 = 3114594599 := mod_pow_succ (by norm_num) hpq11_22 (by norm_num)
      have hpq11_24 : 35 ^ 31830 % 5736805801 = 5221144879 := mod_pow_double (by norm_num) hpq11_23 (by norm_num)
      have hpq11_25 : 35 ^ 31831 % 5736805801 = 4899090934 := mod_pow_succ (by norm_num) hpq11_24 (by norm_num)
      have hpq11_26 : 35 ^ 63662 % 5736805801 = 1068347097 := mod_pow_double (by norm_num) hpq11_25 (by norm_num)
      have hpq11_27 : 35 ^ 63663 % 5736805801 = 2971313589 := mod_pow_succ (by norm_num) hpq11_26 (by norm_num)
      have hpq11_28 : 35 ^ 127326 % 5736805801 = 183426701 := mod_pow_double (by norm_num) hpq11_27 (by norm_num)
      have hpq11_29 : 35 ^ 254652 % 5736805801 = 4031505178 := mod_pow_double (by norm_num) hpq11_28 (by norm_num)
      have hpq11_30 : 35 ^ 509304 % 5736805801 = 2730827686 := mod_pow_double (by norm_num) hpq11_29 (by norm_num)
      have hpq11_31 : 35 ^ 1018608 % 5736805801 = 5406996549 := mod_pow_double (by norm_num) hpq11_30 (by norm_num)
      have hpq11_32 : 35 ^ 2037216 % 5736805801 = 2113488754 := mod_pow_double (by norm_num) hpq11_31 (by norm_num)
      have hpq11_33 : 35 ^ 2037217 % 5736805801 = 5130436778 := mod_pow_succ (by norm_num) hpq11_32 (by norm_num)
      have hpq11_34 : 35 ^ 4074434 % 5736805801 = 235447723 := mod_pow_double (by norm_num) hpq11_33 (by norm_num)
      have hpq11_35 : 35 ^ 4074435 % 5736805801 = 2503864504 := mod_pow_succ (by norm_num) hpq11_34 (by norm_num)
      have hpq11_36 : 35 ^ 8148870 % 5736805801 = 5256549811 := mod_pow_double (by norm_num) hpq11_35 (by norm_num)
      have hpq11_37 : 35 ^ 8148871 % 5736805801 = 401457753 := mod_pow_succ (by norm_num) hpq11_36 (by norm_num)
      have hpq11_38 : 35 ^ 16297742 % 5736805801 = 2576829070 := mod_pow_double (by norm_num) hpq11_37 (by norm_num)
      have hpq11_39 : 35 ^ 16297743 % 5736805801 = 4136930435 := mod_pow_succ (by norm_num) hpq11_38 (by norm_num)
      have hpq11_40 : 35 ^ 32595486 % 5736805801 = 3989207519 := mod_pow_double (by norm_num) hpq11_39 (by norm_num)
      have hpq11_41 : 35 ^ 32595487 % 5736805801 = 1938923941 := mod_pow_succ (by norm_num) hpq11_40 (by norm_num)
      have hpq11_42 : 35 ^ 65190974 % 5736805801 = 3150179337 := mod_pow_double (by norm_num) hpq11_41 (by norm_num)
      have hpq11_43 : 35 ^ 65190975 % 5736805801 = 1256966576 := mod_pow_succ (by norm_num) hpq11_42 (by norm_num)
      have hpq11_44 : 35 ^ 130381950 % 5736805801 = 1735765495 := mod_pow_double (by norm_num) hpq11_43 (by norm_num)
      have hpq11_45 : 35 ^ 260763900 % 5736805801 = 281739261 := mod_pow_double (by norm_num) hpq11_44 (by norm_num)
      have hpq11_46 : 35 ^ 521527800 % 5736805801 = 1773997074 := mod_pow_double (by norm_num) hpq11_45 (by norm_num)
      exact zmod_pow_ne_one hpq11_46 (by norm_num)
    · rw [show (5736805801 - 1) / 251 = 22855800 by norm_num]
      have hpq251_0 : 35 ^ 0 % 5736805801 = 1 := by norm_num
      have hpq251_1 : 35 ^ 0 % 5736805801 = 1 := mod_pow_double (by norm_num) hpq251_0 (by norm_num)
      have hpq251_2 : 35 ^ 1 % 5736805801 = 35 := mod_pow_succ (by norm_num) hpq251_1 (by norm_num)
      have hpq251_3 : 35 ^ 2 % 5736805801 = 1225 := mod_pow_double (by norm_num) hpq251_2 (by norm_num)
      have hpq251_4 : 35 ^ 4 % 5736805801 = 1500625 := mod_pow_double (by norm_num) hpq251_3 (by norm_num)
      have hpq251_5 : 35 ^ 5 % 5736805801 = 52521875 := mod_pow_succ (by norm_num) hpq251_4 (by norm_num)
      have hpq251_6 : 35 ^ 10 % 5736805801 = 4284104775 := mod_pow_double (by norm_num) hpq251_5 (by norm_num)
      have hpq251_7 : 35 ^ 20 % 5736805801 = 1925918070 := mod_pow_double (by norm_num) hpq251_6 (by norm_num)
      have hpq251_8 : 35 ^ 21 % 5736805801 = 4302268639 := mod_pow_succ (by norm_num) hpq251_7 (by norm_num)
      have hpq251_9 : 35 ^ 42 % 5736805801 = 476115606 := mod_pow_double (by norm_num) hpq251_8 (by norm_num)
      have hpq251_10 : 35 ^ 43 % 5736805801 = 5190434608 := mod_pow_succ (by norm_num) hpq251_9 (by norm_num)
      have hpq251_11 : 35 ^ 86 % 5736805801 = 4043945666 := mod_pow_double (by norm_num) hpq251_10 (by norm_num)
      have hpq251_12 : 35 ^ 87 % 5736805801 = 3854759086 := mod_pow_succ (by norm_num) hpq251_11 (by norm_num)
      have hpq251_13 : 35 ^ 174 % 5736805801 = 1039563871 := mod_pow_double (by norm_num) hpq251_12 (by norm_num)
      have hpq251_14 : 35 ^ 348 % 5736805801 = 1792233363 := mod_pow_double (by norm_num) hpq251_13 (by norm_num)
      have hpq251_15 : 35 ^ 696 % 5736805801 = 1289228212 := mod_pow_double (by norm_num) hpq251_14 (by norm_num)
      have hpq251_16 : 35 ^ 697 % 5736805801 = 4965346813 := mod_pow_succ (by norm_num) hpq251_15 (by norm_num)
      have hpq251_17 : 35 ^ 1394 % 5736805801 = 661365924 := mod_pow_double (by norm_num) hpq251_16 (by norm_num)
      have hpq251_18 : 35 ^ 1395 % 5736805801 = 200584136 := mod_pow_succ (by norm_num) hpq251_17 (by norm_num)
      have hpq251_19 : 35 ^ 2790 % 5736805801 = 3859460987 := mod_pow_double (by norm_num) hpq251_18 (by norm_num)
      have hpq251_20 : 35 ^ 5580 % 5736805801 = 441649049 := mod_pow_double (by norm_num) hpq251_19 (by norm_num)
      have hpq251_21 : 35 ^ 11160 % 5736805801 = 1211692568 := mod_pow_double (by norm_num) hpq251_20 (by norm_num)
      have hpq251_22 : 35 ^ 22320 % 5736805801 = 4979383230 := mod_pow_double (by norm_num) hpq251_21 (by norm_num)
      have hpq251_23 : 35 ^ 44640 % 5736805801 = 960586382 := mod_pow_double (by norm_num) hpq251_22 (by norm_num)
      have hpq251_24 : 35 ^ 89280 % 5736805801 = 209252525 := mod_pow_double (by norm_num) hpq251_23 (by norm_num)
      have hpq251_25 : 35 ^ 178560 % 5736805801 = 1471890647 := mod_pow_double (by norm_num) hpq251_24 (by norm_num)
      have hpq251_26 : 35 ^ 357120 % 5736805801 = 1919141641 := mod_pow_double (by norm_num) hpq251_25 (by norm_num)
      have hpq251_27 : 35 ^ 357121 % 5736805801 = 4065093624 := mod_pow_succ (by norm_num) hpq251_26 (by norm_num)
      have hpq251_28 : 35 ^ 714242 % 5736805801 = 2582583971 := mod_pow_double (by norm_num) hpq251_27 (by norm_num)
      have hpq251_29 : 35 ^ 714243 % 5736805801 = 4338351970 := mod_pow_succ (by norm_num) hpq251_28 (by norm_num)
      have hpq251_30 : 35 ^ 1428486 % 5736805801 = 1220902455 := mod_pow_double (by norm_num) hpq251_29 (by norm_num)
      have hpq251_31 : 35 ^ 1428487 % 5736805801 = 2573945318 := mod_pow_succ (by norm_num) hpq251_30 (by norm_num)
      have hpq251_32 : 35 ^ 2856974 % 5736805801 = 3944458399 := mod_pow_double (by norm_num) hpq251_31 (by norm_num)
      have hpq251_33 : 35 ^ 2856975 % 5736805801 = 372704741 := mod_pow_succ (by norm_num) hpq251_32 (by norm_num)
      have hpq251_34 : 35 ^ 5713950 % 5736805801 = 5495084864 := mod_pow_double (by norm_num) hpq251_33 (by norm_num)
      have hpq251_35 : 35 ^ 11427900 % 5736805801 = 5719738432 := mod_pow_double (by norm_num) hpq251_34 (by norm_num)
      have hpq251_36 : 35 ^ 22855800 % 5736805801 = 3033230585 := mod_pow_double (by norm_num) hpq251_35 (by norm_num)
      exact zmod_pow_ne_one hpq251_36 (by norm_num)
    · rw [show (5736805801 - 1) / 3463 = 1656600 by norm_num]
      have hpq3463_0 : 35 ^ 0 % 5736805801 = 1 := by norm_num
      have hpq3463_1 : 35 ^ 0 % 5736805801 = 1 := mod_pow_double (by norm_num) hpq3463_0 (by norm_num)
      have hpq3463_2 : 35 ^ 1 % 5736805801 = 35 := mod_pow_succ (by norm_num) hpq3463_1 (by norm_num)
      have hpq3463_3 : 35 ^ 2 % 5736805801 = 1225 := mod_pow_double (by norm_num) hpq3463_2 (by norm_num)
      have hpq3463_4 : 35 ^ 3 % 5736805801 = 42875 := mod_pow_succ (by norm_num) hpq3463_3 (by norm_num)
      have hpq3463_5 : 35 ^ 6 % 5736805801 = 1838265625 := mod_pow_double (by norm_num) hpq3463_4 (by norm_num)
      have hpq3463_6 : 35 ^ 12 % 5736805801 = 4587847261 := mod_pow_double (by norm_num) hpq3463_5 (by norm_num)
      have hpq3463_7 : 35 ^ 24 % 5736805801 = 4250977572 := mod_pow_double (by norm_num) hpq3463_6 (by norm_num)
      have hpq3463_8 : 35 ^ 25 % 5736805801 = 5364069995 := mod_pow_succ (by norm_num) hpq3463_7 (by norm_num)
      have hpq3463_9 : 35 ^ 50 % 5736805801 = 3120658782 := mod_pow_double (by norm_num) hpq3463_8 (by norm_num)
      have hpq3463_10 : 35 ^ 100 % 5736805801 = 5480071527 := mod_pow_double (by norm_num) hpq3463_9 (by norm_num)
      have hpq3463_11 : 35 ^ 101 % 5736805801 = 2487912012 := mod_pow_succ (by norm_num) hpq3463_10 (by norm_num)
      have hpq3463_12 : 35 ^ 202 % 5736805801 = 704007107 := mod_pow_double (by norm_num) hpq3463_11 (by norm_num)
      have hpq3463_13 : 35 ^ 404 % 5736805801 = 4758509379 := mod_pow_double (by norm_num) hpq3463_12 (by norm_num)
      have hpq3463_14 : 35 ^ 808 % 5736805801 = 943878578 := mod_pow_double (by norm_num) hpq3463_13 (by norm_num)
      have hpq3463_15 : 35 ^ 1616 % 5736805801 = 1516989026 := mod_pow_double (by norm_num) hpq3463_14 (by norm_num)
      have hpq3463_16 : 35 ^ 1617 % 5736805801 = 1463363701 := mod_pow_succ (by norm_num) hpq3463_15 (by norm_num)
      have hpq3463_17 : 35 ^ 3234 % 5736805801 = 944703671 := mod_pow_double (by norm_num) hpq3463_16 (by norm_num)
      have hpq3463_18 : 35 ^ 3235 % 5736805801 = 4380599480 := mod_pow_succ (by norm_num) hpq3463_17 (by norm_num)
      have hpq3463_19 : 35 ^ 6470 % 5736805801 = 5535268856 := mod_pow_double (by norm_num) hpq3463_18 (by norm_num)
      have hpq3463_20 : 35 ^ 6471 % 5736805801 = 4419818527 := mod_pow_succ (by norm_num) hpq3463_19 (by norm_num)
      have hpq3463_21 : 35 ^ 12942 % 5736805801 = 3358916687 := mod_pow_double (by norm_num) hpq3463_20 (by norm_num)
      have hpq3463_22 : 35 ^ 25884 % 5736805801 = 3926668160 := mod_pow_double (by norm_num) hpq3463_21 (by norm_num)
      have hpq3463_23 : 35 ^ 51768 % 5736805801 = 1155607708 := mod_pow_double (by norm_num) hpq3463_22 (by norm_num)
      have hpq3463_24 : 35 ^ 103536 % 5736805801 = 2372541559 := mod_pow_double (by norm_num) hpq3463_23 (by norm_num)
      have hpq3463_25 : 35 ^ 103537 % 5736805801 = 2723673351 := mod_pow_succ (by norm_num) hpq3463_24 (by norm_num)
      have hpq3463_26 : 35 ^ 207074 % 5736805801 = 2673642628 := mod_pow_double (by norm_num) hpq3463_25 (by norm_num)
      have hpq3463_27 : 35 ^ 207075 % 5736805801 = 1788599164 := mod_pow_succ (by norm_num) hpq3463_26 (by norm_num)
      have hpq3463_28 : 35 ^ 414150 % 5736805801 = 5368318555 := mod_pow_double (by norm_num) hpq3463_27 (by norm_num)
      have hpq3463_29 : 35 ^ 828300 % 5736805801 = 266419796 := mod_pow_double (by norm_num) hpq3463_28 (by norm_num)
      have hpq3463_30 : 35 ^ 1656600 % 5736805801 = 196521563 := mod_pow_double (by norm_num) hpq3463_29 (by norm_num)
      exact zmod_pow_ne_one hpq3463_30 (by norm_num)

lemma disprove_a396946 :
    ¬ (∀ p : ℕ, Nat.Prime p →
        (∃ x y : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ y ^ 2 = x ^ 3 + (p : ℤ) ^ 2) →
        (∃ x y : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ y ^ 2 = x ^ 3 - (p : ℤ) ^ 2) →
        (∃ m : ℤ, (p : ℤ) = 4 * m ^ 2 + 1 ∨ (p : ℤ) = 12 * m ^ 2 - 1)) := by
  intro h
  have hplus : ∃ x y : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ y ^ 2 = x ^ 3 + (5736805801 : ℤ) ^ 2 :=
    ⟨9415620, 29455769801, by norm_num, by norm_num, by norm_num⟩
  have hminus : ∃ x y : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ y ^ 2 = x ^ 3 - (5736805801 : ℤ) ^ 2 :=
    ⟨28684029005, 4858030414791218, by norm_num, by norm_num, by norm_num⟩
  obtain ⟨m, hm | hm⟩ := h 5736805801 prime_5736805801 hplus hminus
  · norm_num at hm
    have hsq : m ^ 2 = 1434201450 := by linarith
    rcases le_or_gt 0 m with hm0 | hm0
    · by_cases hle : m ≤ 37870
      · nlinarith
      · have hge : 37871 ≤ m := by omega
        nlinarith
    · by_cases hle : -m ≤ 37870
      · nlinarith
      · have hge : 37871 ≤ -m := by omega
        nlinarith
  · norm_num at hm; omega

end OMA.P_oeis_a396946

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a396946.main) :=
  OMA.P_oeis_a396946.disprove_a396946
