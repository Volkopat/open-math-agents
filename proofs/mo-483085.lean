import OMAStatements.S_mo_483085

/-!
Both Euler-quotient conjectures in joro's MathOverflow question 483085.
Qiping Zhou proved the exact quotient identity in https://mathoverflow.net/a/513641.
This development obtains the exponent divisibility using the order of 4 modulo `W n`.
-/

open OMA.S_mo_483085

private lemma pow_one_sub_of_sq_zero {R : Type*} [CommRing R] (z : R)
    (hz : z ^ 2 = 0) (k : ℕ) : (1 - z) ^ k = 1 - (k : R) * z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    linear_combination (k : R) * hz

private lemma quotient_odd (n : ℕ) (hn : Odd n) (hn1 : 1 < n) :
    a (W n) % 2 = 1 := by
  by_cases hn3 : n = 3
  · subst n
    norm_num [a, W, Nat.totient_prime (by decide : Nat.Prime 3)]
  have hn5 : 5 ≤ n := by have := Nat.odd_iff.mp hn; omega
  have hthree : 3 ∣ 2 ^ n + 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    rw [show (2 : ZMod 3) = -1 by decide, hn.neg_one_pow, neg_add_cancel]
  let m := W n
  have hm : 3 * m = 2 ^ n + 1 := Nat.mul_div_cancel' hthree
  have hpow : 2 ^ 5 ≤ (2 : ℕ) ^ n := Nat.pow_le_pow_right (by decide) hn5
  have hm2 : 2 < m := by norm_num at hpow; omega
  have hmodd : Odd m := by
    have hp : 2 ∣ (2 : ℕ) ^ n := dvd_pow_self 2 (by omega)
    rw [Nat.odd_iff]
    omega
  have hfour_pow (j : ℕ) : (4 : ℕ) ^ j = 2 ^ (j * 2) := by
    rw [pow_mul']
    rfl
  have hfour : (4 : ZMod m) ^ n = 1 := by
    have hz := congrArg (fun x : ℕ => (x : ZMod m)) hm
    push_cast at hz
    rw [ZMod.natCast_self, mul_zero] at hz
    have htwo : (2 : ZMod m) ^ n = -1 := by
      apply eq_neg_of_add_eq_zero_left
      exact hz.symm
    calc
      (4 : ZMod m) ^ n = ((2 : ZMod m) ^ n) ^ 2 := by
        rw [← pow_right_comm]
        norm_num
      _ = 1 := by rw [htwo]; ring
  -- A proper divisor of the odd exponent would give a power too small to be 1 modulo m.
  have horder : orderOf (4 : ZMod m) = n := by
    let d := orderOf (4 : ZMod m)
    have hdpos : 0 < d :=
      orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, by omega, hfour⟩)
    have hdvd : d ∣ n := orderOf_dvd_of_pow_eq_one hfour
    have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdvd
    change d = n
    by_contra hne
    obtain ⟨k, hk⟩ := hdvd
    have hkodd : Odd k := by
      have hh := hn
      rw [hk] at hh
      exact (Nat.odd_mul.mp hh).2
    have hk3 : 3 ≤ k := by
      have := Nat.odd_iff.mp hkodd
      by_contra! h
      have hk1 : k = 1 := by omega
      exact hne (by simpa [hk1] using hk.symm)
    have hdk : d * 3 ≤ d * k := Nat.mul_le_mul_left d hk3
    have hbound : 2 * d + 2 ≤ n := by omega
    have hpowbound := Nat.pow_le_pow_right (n := 2) (by decide) hbound
    rw [pow_add] at hpowbound
    have hsmall : 4 ^ d < m := by
      rw [hfour_pow]
      rw [Nat.mul_comm 2 d] at hpowbound
      norm_num at hpowbound
      omega
    have hpos : 1 < 4 ^ d := one_lt_pow₀ (by decide) (by omega)
    have hzero : (((4 ^ d - 1 : ℕ)) : ZMod m) = 0 := by
      rw [Nat.cast_sub hpos.le, Nat.cast_pow]
      push_cast
      exact sub_eq_zero.mpr (pow_orderOf_eq_one (4 : ZMod m))
    have hdiv := (ZMod.natCast_eq_zero_iff _ _).mp hzero
    have hge := Nat.le_of_dvd (show 0 < 4 ^ d - 1 by omega) hdiv
    omega
  -- The totient is even, and its half is a multiple of the order of 4.
  obtain ⟨p, hp⟩ := Nat.totient_even hm2
  have heuler := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    (Nat.ModEq.pow_totient hmodd.coprime_two_left)
  have hp4 : (4 : ZMod m) ^ p = 1 := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at heuler
    rw [hp, ← two_mul, pow_mul] at heuler
    convert heuler using 1
    norm_num
  obtain ⟨q, hq⟩ : n ∣ p := by
    rw [← horder]
    exact orderOf_dvd_of_pow_eq_one hp4
  have hphi : m.totient = n * (2 * q) := by rw [hp, hq]; ring
  have hqpos : 0 < q := by
    have ht := Nat.totient_pos.mpr (show 0 < m by omega)
    by_contra h
    have : q = 0 := by omega
    simp [hphi, this] at ht
  have h6 : 6 * q < m :=
    calc
      6 * q = 3 * (2 * q) := by ring
      _ ≤ n * (2 * q) := Nat.mul_le_mul_right _ (by omega)
      _ = m.totient := hphi.symm
      _ < m := Nat.totient_lt m (by omega)
  -- Multiples of m square to zero modulo m², leaving only the linear binomial term.
  have hm_sq : (m : ZMod (m ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hbase : (2 : ZMod (m ^ 2)) ^ n = 3 * (m : ZMod (m ^ 2)) - 1 := by
    have hz := congrArg (fun x : ℕ => (x : ZMod (m ^ 2))) hm
    push_cast at hz
    linear_combination -hz
  have hbase_sq : ((2 : ZMod (m ^ 2)) ^ n) ^ 2 = 1 - 6 * (m : ZMod (m ^ 2)) := by
    rw [hbase]
    linear_combination 9 * hm_sq
  have hexp : (2 : ZMod (m ^ 2)) ^ m.totient =
      1 - (6 * (q : ZMod (m ^ 2))) * (m : ZMod (m ^ 2)) := by
    rw [hphi, pow_mul, pow_mul, hbase_sq, pow_one_sub_of_sq_zero]
    · ring
    · linear_combination 36 * hm_sq
  have hmod : (2 ^ m.totient - 1) % m ^ 2 = (m - 6 * q) * m := by
    have hh : (((2 ^ m.totient - 1 : ℕ)) : ZMod (m ^ 2)) =
        (((m - 6 * q) * m : ℕ) : ZMod (m ^ 2)) := by
      rw [Nat.cast_sub (one_le_pow₀ (by decide) : 1 ≤ (2 : ℕ) ^ m.totient),
        Nat.cast_mul, Nat.cast_sub h6.le]
      push_cast
      linear_combination hexp - hm_sq
    have hra : (m - 6 * q) * m < m ^ 2 := by
      rw [pow_two]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    have hh' := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hh
    rwa [Nat.mod_eq_of_lt hra] at hh'
  change ((2 ^ m.totient - 1) % m ^ 2 / m) % 2 = 1
  rw [hmod, Nat.mul_div_cancel _ (by omega)]
  have := Nat.odd_iff.mp hmodd
  omega

theorem OMA.solution : type_of% @OMA.S_mo_483085.main := by
  exact ⟨quotient_odd, fun n hn hpos hzero => by
    have h := quotient_odd n hn hpos
    simp [hzero] at h⟩
