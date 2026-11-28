import OMAReductions.R_oeis_a397683_R1

/-! Following @luciusacarr (#27330), retain the odd/even order obstruction.
Use the general lifting lemma employed by @sntntHb (#28139), and use the
negative-one power parity equivalence for the reduction modulo 3. -/

open OMA.S_oeis_a397683

theorem OMA.solution : OMA.R_oeis_a397683_R1.H3 := by
  intro k hk
  have hne : 3 ^ k ≠ 1 := by
    have : 3 ≤ 3 ^ k := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  unfold f
  rw [if_neg hne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x - ⟨hx, hx1, hord⟩
  have h3dvd : 3 ∣ 3 ^ k := dvd_pow_self 3 (by omega)
  have hx3 : ¬ 3 ∣ x := fun h =>
    absurd (Nat.dvd_gcd h h3dvd) (by rw [hx]; norm_num)
  have hx13 : ¬ 3 ∣ x + 1 := fun h =>
    absurd (Nat.dvd_gcd h h3dvd) (by rw [hx1]; norm_num)
  have hxmod : x % 3 = 1 := by omega
  -- order of x is odd
  have hodd : Odd (orderOf (x : ZMod (3 ^ k))) := by
    have hdvd : (3 : ℤ) ^ (k - 1 + 1) ∣ (x : ℤ) ^ (3 ^ (k - 1)) - 1 :=
      by simpa using dvd_sub_pow_of_dvd_sub (show (3 : ℤ) ∣ (x : ℤ) - 1 by omega) (k - 1)
    rw [show k - 1 + 1 = k by omega] at hdvd
    have hpow : (x : ZMod (3 ^ k)) ^ (3 ^ (k - 1)) = 1 := by
      have h0 : (((x : ℤ) ^ (3 ^ (k - 1)) - 1 : ℤ) : ZMod (3 ^ k)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact_mod_cast hdvd
      push_cast at h0
      exact sub_eq_zero.mp h0
    have hd := orderOf_dvd_of_pow_eq_one hpow
    exact Odd.of_dvd_nat (Odd.pow (by decide)) hd
  -- order of x + 1 is even
  have heven : Even (orderOf (((x + 1 : ℕ) : ZMod (3 ^ k)))) := by
    set d := orderOf (((x + 1 : ℕ) : ZMod (3 ^ k)))
    have hp : (((x + 1 : ℕ) : ZMod (3 ^ k))) ^ d = 1 := pow_orderOf_eq_one _
    have hmap := congrArg (ZMod.castHom h3dvd (ZMod 3)) hp
    rw [map_pow, map_natCast, map_one] at hmap
    have h2 : (((x + 1 : ℕ)) : ZMod 3) = 2 := by
      rw [← ZMod.natCast_mod, show (x + 1) % 3 = 2 by omega]
      rfl
    rw [h2] at hmap
    rw [show (2 : ZMod 3) = -1 by decide] at hmap
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mp hmap
  rw [hord] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) heven
