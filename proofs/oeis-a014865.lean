import OMAStatements.S_oeis_a014865

/-! Following @AttaQ (#24874), retain the recurrence and order arguments.
The least-factor coprimality step uses Mathlib’s direct gcd bound. -/

namespace OMA.S_oeis_a014865

theorem closed_s (k : ℕ) : 196 * s k + 15 + 14*k = 15^(k+1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    cases k with
    | zero => decide
    | succ k =>
      rw [s, pow_succ, ← ih]
      ring

/-- No prime smaller than the least factor of k can divide k. -/
private theorem least_coprime (k : ℕ) (hgt : 1 < k) :
    k.gcd (k.minFac - 1) = 1 := by
  have hp := (Nat.minFac_prime (by omega : k ≠ 1)).two_le
  exact Nat.gcd_eq_one_of_lt_minFac (by omega) (by omega)

theorem small_factor (k : ℕ) (hk : IsTerm k) (ho : Odd k) (hgt : 1 < k) :
    3 ∣ k ∨ 5 ∣ k ∨ 7 ∣ k := by
  let p := k.minFac
  have hp : Nat.Prime p := Nat.minFac_prime (by omega)
  have hpk : p ∣ k := Nat.minFac_dvd k
  have solve (q : ℕ) (hq : Nat.Prime q) (hd : p ∣ q) : q ∣ k :=
    (Nat.prime_dvd_prime_iff_eq hp hq).mp hd ▸ hpk
  by_cases h15 : p ∣ 15
  · rcases hp.dvd_mul.mp (show p ∣ 3 * 5 from h15) with h | h
    · exact Or.inl (solve 3 (by decide) h)
    · exact Or.inr (Or.inl (solve 5 (by decide) h))
  let _ : Fact p.Prime := ⟨hp⟩
  have hnz : (15 : ZMod p) ≠ 0 := fun h => h15 ((ZMod.natCast_eq_zero_iff 15 p).mp h)
  have hkz := (ZMod.natCast_eq_zero_iff k p).mpr hpk
  have hsz := (ZMod.natCast_eq_zero_iff (s k) p).mpr (hpk.trans hk.2)
  have eqn := congrArg (fun t : ℕ => (t : ZMod p)) (closed_s k)
  push_cast at eqn
  rw [hsz, hkz] at eqn
  have hpow : (15 : ZMod p)^k = 1 := by
    apply mul_right_cancel₀ hnz
    simpa [pow_succ] using eqn.symm
  have hdiv := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow)
    (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hnz))
  rw [show k.gcd (p-1) = 1 from least_coprime k hgt] at hdiv
  have hone : (15 : ZMod p) = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hdiv)
  have hz : (14 : ZMod p) = 0 := by linear_combination hone
  have h14 : p ∣ 2 * 7 := (ZMod.natCast_eq_zero_iff 14 p).mp hz
  rcases hp.dvd_mul.mp h14 with h | h
  · exact (ho.not_two_dvd_nat (solve 2 (by decide) h)).elim
  · exact Or.inr (Or.inr (solve 7 (by decide) h))

/-- Doubling the exponent gives an additional factor of two in the difference from one. -/
private theorem even_power (j m : ℕ) : ∃ u : ℕ,
    15 ^ (2 ^ (j + 1) * m) = 1 + 2 ^ (j + 3) * u := by
  induction j with
  | zero =>
    induction m with
    | zero => exact ⟨0, by norm_num⟩
    | succ m ih =>
      obtain ⟨u, hu⟩ := ih
      refine ⟨225 * u + 28, ?_⟩
      rw [Nat.mul_succ, pow_add, hu]
      ring
  | succ j ih =>
    obtain ⟨u, hu⟩ := ih
    refine ⟨u + 2^(j+2)*u^2, ?_⟩
    rw [show 2^(j+1+1)*m = 2^(j+1)*m + 2^(j+1)*m by ring, pow_add, hu]
    ring

theorem odd_term (k : ℕ) (hk : IsTerm k) : Odd k := by
  obtain ⟨j, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk.1.ne'
  cases j with
  | zero => simpa using hm
  | succ j =>
    obtain ⟨u, hu⟩ := even_power j m
    obtain ⟨t, ht⟩ := hk.2
    have hs := closed_s (2^(j+1)*m)
    rw [ht, pow_succ 15, hu, show 2^(j+3) = 2^(j+1)*4 by ring] at hs
    have he : 196*(m*t) + 14*m = 60*u := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 2^(j+1) by positivity)
      linear_combination hs
    obtain ⟨v, hv⟩ := hm
    omega

end OMA.S_oeis_a014865

open OMA.S_oeis_a014865 in
theorem OMA.solution : type_of% @OMA.S_oeis_a014865.main := by
  refine ⟨odd_term, ?_, fun k hk h => small_factor k hk (odd_term k hk) h⟩
  intro k hk hlarge hprime
  rcases small_factor k hk (odd_term k hk) (by omega) with h | h | h <;>
    have := (Nat.dvd_prime hprime).mp h <;> omega
