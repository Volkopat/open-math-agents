import OMAStatements.S_oeis_a110073

-- Credit: @Pixelstorm44
namespace OMA.R_oeis_a110073_R1

/-- For an odd part m greater than one, m - φ(m) is odd. If it divides 8 it is 1. -/
private theorem odd_defect {m t : ℕ} (hm : Odd m)
    (h : t * (m - m.totient) = 8) : m.totient = m - 1 ∧ t = 8 := by
  have hm1 : m ≠ 1 := by
    rintro rfl
    simp at h
  obtain ⟨b, hb⟩ := hm
  obtain ⟨c, hc⟩ := Nat.totient_even (show 2 < m by omega)
  have hdvd : m - m.totient ∣ 8 := ⟨t, by rw [← h, Nat.mul_comm]⟩
  have hle := Nat.le_of_dvd (by decide : 0 < 8) hdvd
  have hφ := Nat.totient_le m
  generalize he : m - m.totient = d at hdvd hle h
  have hd : d = 1 := by
    interval_cases d <;> omega
  simp [hd] at h
  omega

/-- On the prime-cofactor branch the original equation forces q = 8p+1
with p prime, by extracting the power of two from q-1. -/
private theorem prime_cofactor {q : ℕ} (hq : q.Prime) (hn : 76 < 10 * q)
    (hs : (ArithmeticFunction.sigma 1 (10*q) : ℤ) =
      2 * ((10*q : ℕ) : ℤ) - ((10*q).totient.totient : ℤ)) :
    ∃ p : ℕ, p.Prime ∧ (8*p+1).Prime ∧ 10*q = 80*p+10 := by
  have hcop : Nat.Coprime 10 q := by
    apply (hq.coprime_iff_not_dvd.mpr _).symm
    rw [show 10 = 2 * 5 by decide, hq.dvd_mul]
    intro h
    rcases h with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 2) h
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 5) h
      omega
  have hs10 : ArithmeticFunction.sigma 1 10 = 18 := by decide
  have hsq : ArithmeticFunction.sigma 1 q = q+1 := by
    simp [ArithmeticFunction.sigma_one_apply, hq.divisors, Ne.symm hq.ne_one, Nat.add_comm]
  have hφ10 : Nat.totient 10 = 4 := by decide
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hs10, hsq,
    Nat.totient_mul hcop, hφ10, Nat.totient_prime hq] at hs
  obtain ⟨k,m,hm,hkm⟩ := Nat.exists_eq_two_pow_mul_odd (show q-1 ≠ 0 by omega)
  have hpow : 4 * (q-1) = 2^(k+1+1) * m := by rw [hkm]; ring
  have hcm : Nat.Coprime (2^(k+1+1)) m := hm.coprime_two_left.pow_left _
  rw [hpow, Nat.totient_mul hcm, Nat.totient_prime_pow_succ Nat.prime_two] at hs
  simp only [Nat.reduceSub, Nat.mul_one, pow_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat] at hs
  have hq' : q = 2^k*m+1 := by omega
  have hs' : 2^k * m = 2^k * m.totient + 8 := by
    zify at hq' ⊢
    push_cast at *
    linarith
  have hdef : 2^k * (m-m.totient) = 8 := by rw [Nat.mul_sub]; omega
  obtain ⟨hprime, ht⟩ := odd_defect hm hdef
  rw [ht] at hq'
  refine ⟨m, (Nat.totient_eq_iff_prime (by omega)).mp hprime, hq' ▸ hq, by omega⟩

def H1 : Prop := ∀ n : ℕ, 76 < n →
    (ArithmeticFunction.sigma 1 n : ℤ) = 2 * (n : ℤ) - (n.totient.totient : ℤ) →
    10 ∣ n

/-- Rule out solutions divisible by 25 on the branch already divisible by 10. -/
def H2 : Prop := ∀ q : ℕ, 76 < 10 * q →
    (ArithmeticFunction.sigma 1 (10 * q) : ℤ) =
      2 * ((10 * q : ℕ) : ℤ) - ((10 * q).totient.totient : ℤ) → ¬ 5 ∣ q

/-- The cofactor obeys a divisor-sum equation independent of the original index. -/
def H3 : Prop := ∀ q : ℕ, 7 < q → Nat.Coprime 10 q →
    9 * ArithmeticFunction.sigma 1 q + 2 * q.totient.totient = 10 * q → q.Prime

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a110073.main := by
  intro h₁ h₂ h₃ n hn hs
  obtain ⟨q, rfl⟩ := h₁ n hn hs
  have h5 := h₂ q hn hs
  have h2 : ¬ 2 ∣ q := by
    rintro ⟨k, hk⟩
    have hab : Nat.Abundant (10*q) := (show Nat.Abundant 20 by decide).of_dvd
      ⟨k, by rw [hk]; ring⟩ (by omega)
    rw [Nat.abundant_iff_sum_divisors, ← ArithmeticFunction.sigma_one_apply] at hab
    omega
  have hcop : Nat.Coprime 10 q := by
    rw [show 10 = 2 * 5 by decide, Nat.coprime_mul_iff_left]
    exact ⟨Nat.prime_two.coprime_iff_not_dvd.mpr h2,
      (show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr h5⟩
  have hφ := Nat.totient_even (show 2 < q by omega)
  have hφ4 : (4 * q.totient).totient = 4 * q.totient.totient := by
    rw [show 4 * q.totient = 2 * (2 * q.totient) by ring,
      Nat.totient_two_mul_of_even (even_two.mul_right _),
      Nat.totient_two_mul_of_even hφ]
    ring
  apply prime_cofactor _ hn hs
  apply h₃ q (by omega) hcop
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    show ArithmeticFunction.sigma 1 10 = 18 by decide,
    Nat.totient_mul hcop, show Nat.totient 10 = 4 by decide, hφ4] at hs
  push_cast at hs
  omega

end OMA.R_oeis_a110073_R1
