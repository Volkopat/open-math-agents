import OMAStatements.S_oeis_a055008

-- Problem: A055008, every k with gcd(phi k, sigma k) = 1 is a square or twice a square.
-- Credit: @bnb9001

namespace OMA_A055008_Proof

open ArithmeticFunction

lemma sum_pow_mod_two (p k : ℕ) (hp : Odd p) : (∑ i ∈ Finset.range k, p ^ i) % 2 = k % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih]
    have : p ^ k % 2 = 1 := Nat.odd_iff.mp hp.pow
    rw [this]
    omega

lemma sq_or_twice_sq_of_odd_sigma : ∀ n : ℕ, Odd (sigma 1 n) → ∃ m, n = m ^ 2 ∨ n = 2 * m ^ 2 := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro h
    rw [sigma_one_apply_prime_pow hp] at h
    rcases hp.eq_two_or_odd' with rfl | hodd
    · rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
      · exact ⟨2 ^ j, Or.inl (by ring)⟩
      · exact ⟨2 ^ j, Or.inr (by ring)⟩
    · have := sum_pow_mod_two p (k + 1) hodd
      rw [Nat.odd_iff] at h
      obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
      exact ⟨p ^ j, Or.inl (by ring)⟩
  | zero => intro _; exact ⟨0, Or.inl (by simp)⟩
  | one => intro _; exact ⟨1, Or.inl (by simp)⟩
  | coprime a b ha hb hab iha ihb =>
    intro h
    rw [isMultiplicative_sigma.map_mul_of_coprime hab] at h
    obtain ⟨m1, h1⟩ := iha (Nat.odd_mul.1 h).1
    obtain ⟨m2, h2⟩ := ihb (Nat.odd_mul.1 h).2
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact ⟨m1 * m2, Or.inl (by ring)⟩
    · exact ⟨m1 * m2, Or.inr (by ring)⟩
    · exact ⟨m1 * m2, Or.inr (by ring)⟩
    · exfalso
      have h2a : 2 ∣ Nat.gcd (2 * m1 ^ 2) (2 * m2 ^ 2) :=
        Nat.dvd_gcd (dvd_mul_right 2 _) (dvd_mul_right 2 _)
      rw [hab] at h2a
      omega

end OMA_A055008_Proof

open ArithmeticFunction OMA_A055008_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a055008.main := by
  intro k hk
  by_cases hk2 : k ≤ 2
  · interval_cases k
    · simp at hk
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
  · have hev : Even k.totient := Nat.totient_even (by omega)
    have hodd : Odd (sigma 1 k) := by
      rcases Nat.even_or_odd (sigma 1 k) with he | ho
      · exfalso
        have : 2 ∣ Nat.gcd k.totient (sigma 1 k) := Nat.dvd_gcd (even_iff_two_dvd.1 hev) (even_iff_two_dvd.1 he)
        rw [hk] at this
        omega
      · exact ho
    obtain ⟨m, hm | hm⟩ := sq_or_twice_sq_of_odd_sigma k hodd
    · exact Or.inl ⟨m, by rw [hm]; ring⟩
    · exact Or.inr ⟨m, hm⟩
