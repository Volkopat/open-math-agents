import OMAReductions.R_Erdos936_erdos_936_variants_two_pow_add_one_R1

/-! Compare two evaluations of the valuation at the common exponent
`2 * n * (p - 1)`. Only the plus factor in the difference of squares is divisible by
the odd prime. This streamlines the original LTE proof by @Raimo33. -/

open OMA.R_Erdos936_erdos_936_variants_two_pow_add_one_R1

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_two_pow_add_one_R1.H1 := by
  intro p n hp hp2 h
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have htwo : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have hn : n ≠ 0 := by
    rintro rfl
    exact htwo (by simpa using h)
  have hpow := Nat.one_lt_two_pow hn
  have lift (s t : ℕ) (hs : s ≠ 0) (ht : t ≠ 0) (hd : p ∣ 2 ^ s - 1) :
      padicValNat p (2 ^ (s * t) - 1) = padicValNat p (2 ^ s - 1) + padicValNat p t := by
    simpa only [← pow_mul, one_pow] using
      padicValNat.pow_sub_pow (hp.odd_of_ne_two hp2) (Nat.one_lt_two_pow hs) hd
        (fun hdiv => htwo (hp.dvd_of_dvd_pow hdiv)) ht
  have factor : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    simpa only [pow_mul', one_pow] using Nat.pow_two_sub_pow_two (2 ^ n) 1
  have hminus : ¬ p ∣ 2 ^ n - 1 := by
    intro hd
    have d := Nat.dvd_sub h hd
    apply htwo
    simpa only [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by omega] using d
  have fromSquare := lift (2 * n) (p - 1) (by omega) (by omega) (by rw [factor]; exact h.mul_right _)
  have fromFermat := lift (p - 1) (2 * n) (by omega) (by omega) (dvd_two_pow_pred_sub_one hp hp2)
  rw [mul_comm (p - 1)] at fromFermat
  rw [factor, padicValNat.mul (by omega) (by omega),
    padicValNat.eq_zero_of_not_dvd hminus, padicValNat.eq_zero_of_not_dvd
      (Nat.not_dvd_of_pos_of_lt (by omega : 0 < p - 1) (by omega : p - 1 < p))] at fromSquare
  rw [padicValNat.mul (by decide) hn, padicValNat.eq_zero_of_not_dvd htwo] at fromFermat
  omega
