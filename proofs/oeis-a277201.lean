import OMAStatements.S_oeis_a277201

lemma card_div_pp {p : ℕ} (hp : p.Prime) (e : ℕ) : (p ^ e).divisors.card = e + 1 := by
  simp [Nat.divisors_prime_pow hp]

lemma card_five {n : ℕ} (h : n.divisors.card = 5) : ∃ p, p.Prime ∧ n = p ^ 4 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at h
  have hn1 : n ≠ 1 := by rintro rfl; simp at h
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  set p := n.minFac
  have hcop := Nat.coprime_ordCompl hp hn0
  have hsplit := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop' : (p ^ n.factorization p).Coprime (n / p ^ n.factorization p) :=
    Nat.Coprime.pow_left _ hcop
  have hcard := hcop'.card_divisors_mul
  rw [hsplit, h, card_div_pp hp] at hcard
  have he : 1 ≤ n.factorization p :=
    (hp.dvd_iff_one_le_factorization hn0).1 (Nat.minFac_dvd n)
  have hd : n.factorization p + 1 ∣ 5 := Dvd.intro _ hcard.symm
  rcases (Nat.prime_five.eq_one_or_self_of_dvd _ hd) with h1 | h5
  · omega
  · rw [h5] at hcard
    have hm : (n / p ^ n.factorization p).divisors.card = 1 := by omega
    rw [Nat.divisors_card_eq_one_iff] at hm
    refine ⟨p, hp, ?_⟩
    have h4 : n.factorization p = 4 := by omega
    rw [← hsplit, hm, h4, mul_one]

lemma prime_of_card_two {n : ℕ} (h : n.divisors.card = 2) : n.Prime := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at h
  have hn1 : n ≠ 1 := by rintro rfl; simp at h
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hn0]
  have hc : n.divisors.card ≤ ({1, n} : Finset ℕ).card := by
    rw [Finset.card_pair (Ne.symm hn1), h]
  have heq := Finset.eq_of_subset_of_card_le hsub hc
  rw [Nat.prime_def]
  refine ⟨by omega, fun m hm => ?_⟩
  have : m ∈ n.divisors := by simp [hm, hn0]
  rw [← heq] at this
  simpa using this

lemma odd_pow4 {p : ℕ} (hp : Odd p) : (p ^ 4 + 1) / 2 % 2 = 1 := by
  obtain ⟨t, rfl⟩ := hp
  have : (2 * t + 1) ^ 4 + 1 = 2 * (8 * t ^ 4 + 16 * t ^ 3 + 12 * t ^ 2 + 4 * t + 1) := by ring
  rw [this]
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a277201.main := by
  ext k
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h4, h5⟩
    obtain ⟨p, hp, hpk⟩ := card_five h5
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at h5
      · exact h
    have hpo : Odd p := by
      rcases hp.eq_two_or_odd' with rfl | ho
      · have : 2 * k - 1 = 16 := by rw [hpk]; norm_num
        omega
      · exact ho
    have hkeq : k = (p ^ 4 + 1) / 2 := by omega
    have hko : k % 2 = 1 := by rw [hkeq]; exact odd_pow4 hpo
    have hcop : Nat.Coprime 2 k := by
      rw [Nat.coprime_two_left]; exact Nat.odd_iff.2 hko
    rw [hcop.card_divisors_mul, Nat.prime_two.divisors] at h4
    simp at h4
    exact ⟨prime_of_card_two (by omega), p, hp, hkeq⟩
  · rintro ⟨hq, p, hp, rfl⟩
    have hpo : Odd p := by
      rcases hp.eq_two_or_odd' with rfl | ho
      · norm_num at hq
      · exact ho
    have hko := odd_pow4 hpo
    have hcop : Nat.Coprime 2 ((p ^ 4 + 1) / 2) := by
      rw [Nat.coprime_two_left]; exact Nat.odd_iff.2 hko
    have hev : (p ^ 4 + 1) % 2 = 0 := by
      have := Nat.odd_iff.1 (hpo.pow (n := 4)); omega
    refine ⟨?_, ?_⟩
    · rw [hcop.card_divisors_mul, Nat.prime_two.divisors, hq.divisors,
        Finset.card_pair (by norm_num), Finset.card_pair hq.one_lt.ne]
    · have : 2 * ((p ^ 4 + 1) / 2) - 1 = p ^ 4 := by omega
      rw [this, card_div_pp hp]
