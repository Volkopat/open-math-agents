import OMAReductions.R_oeis_a007691_R1

/-!
# Proof of `oeis-a007691.R1.H1`

Euclid's theorem on even perfect numbers: if `p = 2 ^ (k + 1) - 1` is prime, then `2 ^ k * p`
is a perfect number.
-/

private lemma sigma_one_two_pow (k : ℕ) :
    ArithmeticFunction.sigma 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ 2 (k + 1)]
    omega

theorem OMA.solution : OMA.R_oeis_a007691_R1.H1 := by
  intro k hp
  set p := 2 ^ (k + 1) - 1
  have h2pos : 2 ≤ 2 ^ (k + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hp_add : p + 1 = 2 ^ (k + 1) := Nat.sub_add_cancel (by omega)
  have h2dvd : 2 ∣ 2 ^ (k + 1) := by
    rw [pow_succ]
    exact dvd_mul_left 2 _
  have hnot2 : ¬ (2 ∣ p) := by
    intro h
    have : 2 ∣ p + 1 - p := Nat.dvd_sub (hp_add ▸ h2dvd) h
    simp at this
  have hcop : Nat.Coprime (2 ^ k) p :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hnot2).pow_left k
  have hpos : 0 < 2 ^ k * p := Nat.mul_pos (Nat.pos_of_ne_zero (by positivity)) hp.pos
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos]
  have hsum : ∑ i ∈ (2 ^ k * p).divisors, i = ArithmeticFunction.sigma 1 (2 ^ k * p) := by
    simp [ArithmeticFunction.sigma_apply]
  rw [hsum, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    sigma_one_two_pow k]
  have hsigp : ArithmeticFunction.sigma 1 p = p + 1 := by
    have h := ArithmeticFunction.sigma_one_apply_prime_pow hp (i := 1)
    simp [Finset.sum_range_succ] at h
    omega
  rw [hsigp, hp_add, show 2 ^ (k + 1) - 1 = p from rfl, pow_succ']
  ring
