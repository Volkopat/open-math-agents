import OMAStatements.S_oeis_a218755

-- Problem: A218755, Bernoulli denominators ≡ 6 (mod 9) differ by multiples of 36.
-- Credit: @ShoQo
-- Proof: every Bernoulli denominator is 1, 2, or (for B(2k), k ≥ 1) ≡ 2 (mod 4). For the last,
-- von Staudt-Clausen (Mathlib's `Bernoulli.vonStaudt_clausen`) gives B(2k) = z - 1/2 - Σ 1/p
-- over odd primes p with (p-1) ∣ 2k. With Q' the (odd) product of those p, 2Q'·B(2k) is an odd
-- integer: so den ∣ 2Q' (not divisible by 4) and den ∤ Q' (so den is even). A number that is
-- 2 (mod 4) and 6 (mod 9) is 6 (mod 36).

namespace OMA_A218755_Proof

lemma den_dvd_of_mul_eq {x : ℚ} {q : ℕ} {w : ℤ} (hq : q ≠ 0) (h : (q : ℚ) * x = w) :
    x.den ∣ q := by
  have hx : x = Rat.divInt w q := by
    rw [Rat.divInt_eq_div, ← h]; push_cast; field_simp
  have := Rat.den_dvd w q
  rw [← hx] at this
  exact_mod_cast this

lemma mul_eq_of_den_dvd {x : ℚ} {q : ℕ} (h : x.den ∣ q) : ∃ t : ℤ, (q : ℚ) * x = t := by
  obtain ⟨t, rfl⟩ := h
  refine ⟨t * x.num, ?_⟩
  push_cast
  calc (x.den : ℚ) * t * x = t * (x * x.den) := by ring
    _ = t * x.num := by rw [Rat.mul_den_eq_num]

lemma den_mod_four (k : ℕ) (hk : 0 < k) : (bernoulli (2 * k)).den % 4 = 2 := by
  set B := bernoulli (2 * k)
  set P := (Finset.range (2 * k + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * k)
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  have h2P : 2 ∈ P := by
    simp only [P, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.prime_two, by simp⟩
  have hprime : ∀ p ∈ P.erase 2, p.Prime ∧ p ≠ 2 := by
    intro p hp
    rw [Finset.mem_erase] at hp
    exact ⟨(Finset.mem_filter.1 hp.2).2.1, hp.1⟩
  set Q' := ∏ p ∈ P.erase 2, p
  have hQodd : ¬ 2 ∣ Q' := by
    intro h
    obtain ⟨p, hp, h2p⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).1 h
    exact (hprime p hp).2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (hprime p hp).1).1 h2p).symm
  set T := ∑ p ∈ P.erase 2, Q' / p
  have hS : (Q' : ℚ) * ∑ p ∈ P.erase 2, (1 : ℚ) / p = (T : ℚ) := by
    rw [Finset.mul_sum]
    simp only [T, Nat.cast_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (hprime p hp).1.ne_zero
    rw [Nat.cast_div (Finset.dvd_prod_of_mem _ hp) hp0]
    ring
  have hsplit := Finset.add_sum_erase P (fun p : ℕ => (1 : ℚ) / p) h2P
  simp only [Nat.cast_ofNat] at hsplit
  rw [← hsplit] at hz
  set w : ℤ := 2 * Q' * z - Q' - 2 * T
  have hw : ((2 * Q' : ℕ) : ℚ) * B = (w : ℚ) := by
    simp only [w]; push_cast
    linear_combination (2 * (Q' : ℚ)) * hz.symm + (-2) * hS
  have hQ0 : Q' ≠ 0 := by rintro h; exact hQodd (h ▸ dvd_zero 2)
  have hden : B.den ∣ 2 * Q' := den_dvd_of_mul_eq (by omega) hw
  have heven : 2 ∣ B.den := by
    by_contra hodd
    have hcop : B.den.Coprime 2 := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    obtain ⟨t, ht⟩ := mul_eq_of_den_dvd (Nat.Coprime.dvd_of_dvd_mul_left hcop hden)
    have h1 : (w : ℚ) = 2 * t := by rw [← hw]; push_cast; rw [mul_assoc, ht]
    have h2 : w = 2 * t := by exact_mod_cast h1
    have h3 : (Q' : ℤ) = 2 * (Q' * z - T - t) := by simp only [w] at h2; linarith
    exact hQodd (by exact_mod_cast (Dvd.intro _ h3.symm : (2 : ℤ) ∣ Q'))
  have hnot4 : ¬ 4 ∣ B.den := by
    intro h4
    obtain ⟨c, hc⟩ := h4.trans hden
    exact hQodd ⟨c, by omega⟩
  omega

lemma den_mod_36 (n : ℕ) (h : (bernoulli n).den % 9 = 6) : (bernoulli n).den % 36 = 6 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hodd
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [bernoulli_zero] at h
    · have := den_mod_four k hk
      rw [show k + k = 2 * k by ring] at h ⊢
      omega
  · rcases Nat.lt_or_ge 1 n with h1 | h1
    · rw [bernoulli_eq_zero_of_odd hodd h1] at h; simp at h
    · obtain rfl : n = 1 := by obtain ⟨j, rfl⟩ := hodd; omega
      have hd : (bernoulli 1).den ∣ 2 :=
        den_dvd_of_mul_eq (w := -1) (by norm_num) (by rw [bernoulli_one]; norm_num)
      have := Nat.le_of_dvd (by norm_num) hd
      omega

end OMA_A218755_Proof

open OMA_A218755_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a218755.main := by
  intro i j hi hj
  have := den_mod_36 i hi
  have := den_mod_36 j hj
  omega
