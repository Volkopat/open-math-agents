import OMAStatements.S_oeis_a219543

/- Charles R. Greathouse IV gave the congruence argument on OEIS A219543
   on November 22, 2012. https://oeis.org/A219543
   The denominator calculation uses Mathlib's `Bernoulli.vonStaudt_clausen`,
   the integer correction sum from the von Staudt–Clausen theorem. -/

open Finset

private theorem half_den : (1 / 2 : ℚ).den = 2 := by
  simpa only [one_div] using Rat.inv_ofNat_den 2

private theorem bernoulli_even_den_mod_four (k : ℕ) (hk : 0 < k) :
    (bernoulli (2 * k)).den % 4 = 2 := by
  let primes := (range (2 * k + 2)).filter fun p => p.Prime ∧ (p - 1) ∣ 2 * k
  have htwo : 2 ∈ primes := by
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), Nat.prime_two, ?_⟩
    simp
  let rest : ℚ := ∑ p ∈ primes.erase 2, (1 : ℚ) / p
  have hsplit : (∑ p ∈ primes, (1 : ℚ) / p) = 1 / 2 + rest :=
    (add_sum_erase primes (fun p => (1 : ℚ) / p) htwo).symm
  have hrest : ¬ 2 ∣ rest.den := by
    intro h
    have hprod := h.trans (Rat.den_sum_dvd_prod_den (primes.erase 2)
      (fun p => (1 : ℚ) / p))
    obtain ⟨p, hp, hpd⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff
      (fun p : ℕ => ((1 : ℚ) / p).den)).mp hprod
    have hprime : p.Prime := (mem_filter.mp (mem_of_mem_erase hp)).2.1
    have hpne : p ≠ 2 := ne_of_mem_erase hp
    rw [show ((1 : ℚ) / p).den = p by simp [hprime.ne_zero]] at hpd
    exact hpne ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).mp hpd).symm
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  change (z : ℚ) = bernoulli (2 * k) + ∑ p ∈ primes, (1 : ℚ) / p at hz
  rw [hsplit] at hz
  have hden : (bernoulli (2 * k)).den = ((1 / 2 : ℚ) + rest).den := by
    rw [show bernoulli (2 * k) = (z : ℚ) - ((1 / 2 : ℚ) + rest) by linarith,
      Rat.intCast_sub_den]
  have hupper : ((1 / 2 : ℚ) + rest).den ∣ 2 * rest.den := by
    simpa only [half_den] using Rat.add_den_dvd (1 / 2) rest
  have hreverse : 2 ∣ ((1 / 2 : ℚ) + rest).den * rest.den := by
    have h := Rat.sub_den_dvd ((1 / 2 : ℚ) + rest) rest
    rwa [add_sub_cancel_right, half_den] at h
  have heven := (Nat.prime_two.dvd_mul.mp hreverse).resolve_right hrest
  have hnotfour : ¬ 4 ∣ ((1 / 2 : ℚ) + rest).den := by
    intro h
    obtain ⟨m, hm⟩ := h.trans hupper
    exact hrest ⟨m, by omega⟩
  rw [hden]
  rw [Nat.dvd_iff_mod_eq_zero] at heven hnotfour
  omega

private theorem bernoulli_den_mod_four_of_mod_nine {n : ℕ}
    (hn : (bernoulli n).den % 9 = 3) : (bernoulli n).den % 4 = 2 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
  · have heq : n = 2 * k := by omega
    rw [heq] at hn ⊢
    apply bernoulli_even_den_mod_four
    by_contra h
    have hz : k = 0 := by omega
    subst k
    change (bernoulli 0).den % 9 = 3 at hn
    rw [bernoulli_zero] at hn
    exact (by decide : (1 : ℚ).den % 9 ≠ 3) hn
  · by_cases h : n = 1
    · subst n
      rw [bernoulli_one, neg_div, Rat.neg_den, half_den] <;> decide
    · have hn₁ : 1 < n := by
        obtain ⟨k, hk⟩ := hodd
        omega
      rw [bernoulli_eq_zero_of_odd hodd hn₁] at hn
      exact ((by decide : (0 : ℚ).den % 9 ≠ 3) hn).elim

theorem OMA.solution : type_of% @OMA.S_oeis_a219543.main := by
  intro i j hi hj
  have h4 : (bernoulli i).den ≡ (bernoulli j).den [MOD 4] :=
    (bernoulli_den_mod_four_of_mod_nine hi).trans (bernoulli_den_mod_four_of_mod_nine hj).symm
  have h9 : (bernoulli i).den ≡ (bernoulli j).den [MOD 9] := hi.trans hj.symm
  exact Nat.modEq_iff_dvd.mp (Nat.mod_lcm h4 h9)
