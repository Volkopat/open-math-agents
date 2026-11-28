import OMAStatements.S_oeis_a284708

namespace OMA.S_oeis_a284708


/-- If the prime `q` does not divide `d`, one of `p, p + d, ..., p + (q-1) d` is divisible by `q`. -/
theorem exists_dvd {q p d : ℕ} (hq : q.Prime) (hd : ¬ q ∣ d) : ∃ i < q, q ∣ p + i * d := by
  have := Fact.mk hq
  have hd' : (d : ZMod q) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  refine ⟨(-(p : ZMod q) * (d : ZMod q)⁻¹).val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hd', mul_one, add_neg_cancel]

/-- Every prime `q ≤ n` divides the common difference. -/
theorem prime_dvd_diff {n p d : ℕ} (hn : 4 ≤ n) (h : IsAP n p d) {q : ℕ} (hq : q.Prime)
    (hqn : q ≤ n) : q ∣ d := by
  obtain ⟨hp, hd0, hdp, hall⟩ := h
  by_contra hqd
  obtain ⟨i, hi, hdvd⟩ := exists_dvd (p := p) hq hqd
  have hprime := hall i (by omega)
  have heq : p + i * d = q := ((Nat.prime_dvd_prime_iff_eq hq hprime).mp hdvd).symm
  have hpq : p ≤ q := heq ▸ Nat.le_add_right p (i * d)
  rcases Nat.lt_or_ge p n with hpn | hpn
  · -- the term p + p d = p (1 + d) is composite
    have hc := hall p hpn
    rw [show p + p * d = p * (1 + d) by ring] at hc
    exact Nat.not_prime_mul (by have := hp.two_le; omega) (by omega) hc
  · -- p = n: all primes below p divide d, and Bertrand gives a contradiction
    have hpn' : p = n := by omega
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    have h5 : 5 ≤ p := by omega
    have hsmall : ∀ q', q'.Prime → q' < p → q' ∣ d := by
      intro q' hq' hq'p
      by_contra hq'd
      obtain ⟨i', hi', hdvd'⟩ := exists_dvd (p := p) hq' hq'd
      have hpr := hall i' (by omega)
      have heq' : p + i' * d = q' := ((Nat.prime_dvd_prime_iff_eq hq' hpr).mp hdvd').symm
      have := Nat.le_add_right p (i' * d)
      omega
    obtain ⟨r, hr, hr1, hr2⟩ := Nat.exists_prime_lt_and_le_two_mul ((p - 1) / 2) (by omega)
    have hr2' : r < p := by omega
    have hr3 : 2 < r := by omega
    have h2d := hsmall 2 Nat.prime_two (by omega)
    have hrd := hsmall r hr hr2'
    have hcop : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hr).mpr (by omega)
    have h2rd : 2 * r ∣ d := hcop.mul_dvd_of_dvd_of_dvd h2d hrd
    have := Nat.le_of_dvd hd0 h2rd
    omega

theorem solution : ∀ n : ℕ, 4 ≤ n → ∀ p d : ℕ, IsAP n p d → primorial n < p := by
  intro n hn p d h
  have hdiv : primorial n ∣ d := by
    unfold primorial
    apply Finset.prod_primes_dvd
    · intro q hq
      exact (Finset.mem_filter.mp hq).2.prime
    · intro q hq
      obtain ⟨hqn, hqp⟩ := Finset.mem_filter.mp hq
      exact prime_dvd_diff hn h hqp (by have := Finset.mem_range.mp hqn; omega)
  have := Nat.le_of_dvd h.2.1 hdiv
  exact lt_of_le_of_lt this h.2.2.1

/-! Control: a(4) = 11 with the progression 11, 17, 23, 29 (difference 6 < 11), and 4# = 6. -/

theorem control : IsAP 4 11 6 ∧ primorial 4 = 6 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, ?_⟩, by decide⟩
  intro i hi
  interval_cases i <;> norm_num

end OMA.S_oeis_a284708

theorem OMA.solution : type_of% @OMA.S_oeis_a284708.main :=
  OMA.S_oeis_a284708.solution
