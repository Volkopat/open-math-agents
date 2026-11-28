import OMAStatements.S_oeis_a008474

namespace OMA.OeisA008474

open OMA.S_oeis_a008474

lemma a_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) : a (p ^ k) = p + k := by
  unfold a
  rw [Nat.primeFactors_pow p (Nat.ne_of_gt hk), hp.primeFactors]
  simp [hp.factorization_pow]

lemma a_mul_coprime {u v : ℕ} (hu : u ≠ 0) (hv : v ≠ 0) (hcop : Nat.Coprime u v) :
    a (u * v) = a u + a v := by
  unfold a
  rw [Nat.primeFactors_mul hu hv]
  have hdisj : Disjoint u.primeFactors v.primeFactors := hcop.disjoint_primeFactors
  rw [Finset.sum_union hdisj]
  congr 1
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Nat.factorization_mul hu hv, Finsupp.add_apply]
    have hnot : p ∉ v.primeFactors := Finset.disjoint_left.mp hdisj hp
    have hv0 : v.factorization p = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      by_contra h
      push Not at h
      exact hnot (Nat.mem_primeFactors.mpr ⟨h.1, h.2.1, hv⟩)
    rw [hv0, add_zero]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Nat.factorization_mul hu hv, Finsupp.add_apply]
    have hnot : p ∉ u.primeFactors := Finset.disjoint_right.mp hdisj hp
    have hu0 : u.factorization p = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      by_contra h
      push Not at h
      exact hnot (Nat.mem_primeFactors.mpr ⟨h.1, h.2.1, hu⟩)
    rw [hu0, zero_add]

lemma pow_ge_add_one {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) : p + k ≤ p ^ k + 1 := by
  induction k with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp
    | succ m' =>
      have h1 : p + (m' + 1) ≤ p ^ (m' + 1) + 1 := ih (by omega)
      have h2 : p ^ (m' + 2) = p ^ (m' + 1) * p := by ring
      have h3 : 2 ≤ p ^ (m' + 1) := by
        calc 2 ≤ p := hp
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ (m' + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith

lemma two_pow_ge_add_two {k : ℕ} (hk : 2 ≤ k) : k + 2 ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 1
    · subst hm; norm_num
    · have h1 := ih (by omega)
      have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega

lemma two_pow_ge_add_four {k : ℕ} (hk : 4 ≤ k) : k + 4 ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 3
    · subst hm; norm_num
    · have h1 := ih (by omega)
      have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega

lemma prime_pow_lt {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (h8 : 8 ≤ p ^ k) :
    p + k < p ^ k := by
  by_cases hp2 : p = 2
  · subst hp2
    have hk3 : 3 ≤ k := by
      by_contra hlt
      have hk2 : k = 2 := by omega
      subst hk2; norm_num at h8
    by_cases hk3' : k = 3
    · subst hk3'; norm_num
    · have := two_pow_ge_add_four (by omega : 4 ≤ k); omega
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    induction k with
    | zero => omega
    | succ m ih =>
      by_cases hm : m = 1
      · subst hm
        have : p ^ (1 + 1) = p * p := by ring
        nlinarith
      · have hpm : 9 ≤ p ^ m := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
            _ ≤ p ^ m := Nat.pow_le_pow_right (by omega) (by omega)
        have h1 := ih (by omega) (by omega)
        have h2 : p ^ (m + 1) = p ^ m * p := by ring
        nlinarith

lemma split_prime_pow {n : ℕ} (hn : 2 ≤ n) :
    ∃ p k u : ℕ, p.Prime ∧ 1 ≤ k ∧ 1 ≤ u ∧ n = p ^ k * u ∧ Nat.Coprime (p ^ k) u := by
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ n := Nat.minFac_dvd n
  set k := n.factorization p
  have hk : 1 ≤ k := by
    have : k ≠ 0 := (hp.dvd_iff_one_le_factorization (by omega)).mp hpdvd |> Nat.pos_iff_ne_zero.mp
    omega
  have hpk_dvd : p ^ k ∣ n := Nat.ordProj_dvd n p
  set u := n / p ^ k
  have hmul : p ^ k * u = n := Nat.mul_div_cancel' hpk_dvd
  have hu_pos : 1 ≤ u :=
    Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hmul; omega
  have hcop : Nat.Coprime (p ^ k) u := by
    refine Nat.Coprime.pow_left k ?_
    rw [hp.coprime_iff_not_dvd]
    intro hpu
    have hpk1 : p ^ (k + 1) ∣ n := by
      rcases hpu with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      rw [← hmul, hr]; ring
    have hle := (hp.pow_dvd_iff_le_factorization (by omega)).mp hpk1
    omega
  exact ⟨p, k, u, hp, hk, hu_pos, hmul.symm, hcop⟩

lemma a_le_succ : ∀ n : ℕ, 1 ≤ n → a n ≤ n + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst h1; simp [a]
    · obtain ⟨p, k, u, hp, hk, hu, hmul, hcop⟩ := split_prime_pow (n := n) (by omega)
      have hpk_ge2 : 2 ≤ p ^ k := by
        calc 2 ≤ p := hp.two_le
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
      by_cases hu1 : u = 1
      · rw [hmul, hu1, mul_one, a_prime_pow hp hk]
        exact pow_ge_add_one hp.two_le hk
      · have hu_lt : u < n := by nlinarith
        have hau : a u ≤ u + 1 := ih u hu_lt hu
        rw [hmul, a_mul_coprime (by positivity) (by omega) hcop, a_prime_pow hp hk]
        have hpk_bound : p + k ≤ p ^ k + 1 := pow_ge_add_one hp.two_le hk
        by_cases hsmall : p ^ k = 2 ∧ u = 3
        · rcases hsmall with ⟨hA, hB⟩
          have hp2 : p = 2 := by
            have := hp.two_le
            have : p ≤ p ^ k := Nat.le_self_pow (by omega) p
            omega
          have hk1 : k = 1 := by
            subst hp2
            by_contra hk1
            have : 4 ≤ 2 ^ k := by
              calc 4 = 2 ^ 2 := by norm_num
                _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
            omega
          subst hp2; subst hk1; rw [hB] at hau ⊢; omega
        · by_cases hsmall2 : p ^ k = 3 ∧ u = 2
          · rcases hsmall2 with ⟨hA, hB⟩
            have hp3 : p = 3 := by
              have := hp.two_le
              have : p ≤ p ^ k := Nat.le_self_pow (by omega) p
              by_cases hp2' : p = 2
              · subst hp2'
                cases k with
                | zero => omega
                | succ m =>
                  cases m with
                  | zero => norm_num at hA
                  | succ m' =>
                    have : 4 ≤ 2 ^ (m' + 2) := by
                      calc 4 = 2 ^ 2 := by norm_num
                        _ ≤ 2 ^ (m' + 2) := Nat.pow_le_pow_right (by omega) (by omega)
                    omega
              · omega
            have hk1 : k = 1 := by
              subst hp3
              by_contra hk1
              have : 9 ≤ 3 ^ k := by
                calc 9 = 3 ^ 2 := by norm_num
                  _ ≤ 3 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
              omega
            subst hp3; subst hk1; rw [hB] at hau ⊢; omega
          · have hnot22 : ¬ (p ^ k = 2 ∧ u = 2) := by
              rintro ⟨hA, hB⟩
              rw [hA, hB] at hcop
              norm_num at hcop
            by_cases hA2 : p ^ k = 2
            · have hu4 : 4 ≤ u := by omega
              rw [hA2] at hpk_bound ⊢; omega
            · by_cases hB2 : u = 2
              · have hA4 : 4 ≤ p ^ k := by omega
                rw [hB2] at hau ⊢; omega
              · have hA3 : 3 ≤ p ^ k := by omega
                have hB3 : 3 ≤ u := by omega
                nlinarith

lemma a_ge_five {n : ℕ} (hn : 5 ≤ n) : 5 ≤ a n := by
  obtain ⟨p, k, u, hp, hk, hu, hmul, hcop⟩ := split_prime_pow (n := n) (by omega)
  by_cases hu1 : u = 1
  · rw [hmul, hu1, mul_one, a_prime_pow hp hk]
    by_cases hp5 : 5 ≤ p
    · omega
    · have hp_cases : p = 2 ∨ p = 3 := by
        have h2 := hp.two_le
        have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by decide)
        omega
      rcases hp_cases with rfl | rfl
      · by_contra hlt
        have : k ≤ 2 := by omega
        have : 2 ^ k ≤ 4 := by
          calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) this
            _ = 4 := by norm_num
        rw [hu1, mul_one] at hmul; omega
      · by_contra hlt
        have hk1 : k = 1 := by omega
        rw [hk1, pow_one, hu1, mul_one] at hmul; omega
  · rw [hmul, a_mul_coprime (pow_ne_zero k hp.ne_zero) (by omega) hcop, a_prime_pow hp hk]
    obtain ⟨q, m, v, hq, hm, hv, hmul_u, hcop_u⟩ := split_prime_pow (n := u) (by omega : 2 ≤ u)
    have hq_ge : 3 ≤ a u := by
      by_cases hv1 : v = 1
      · rw [hmul_u, hv1, mul_one, a_prime_pow hq hm]
        have := hq.two_le; omega
      · rw [hmul_u, a_mul_coprime (pow_ne_zero m hq.ne_zero) (by omega) hcop_u, a_prime_pow hq hm]
        have := hq.two_le; omega
    have := hp.two_le
    omega

lemma a_lt_of_composite {n : ℕ} (hn : 8 ≤ n) (hnp : ¬ n.Prime) : a n < n := by
  obtain ⟨p, k, u, hp, hk, hu, hmul, hcop⟩ := split_prime_pow (n := n) (by omega)
  by_cases hu1 : u = 1
  · rw [hmul, hu1, mul_one] at hn hnp ⊢
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk1 : k = 1 := by omega
      rw [hk1, pow_one] at hnp
      exact hnp hp
    rw [a_prime_pow hp hk]
    exact prime_pow_lt hp hk2 hn
  · have hau : a u ≤ u + 1 := a_le_succ u hu
    have hpk_bound : p + k ≤ p ^ k + 1 := pow_ge_add_one hp.two_le hk
    rw [hmul, a_mul_coprime (pow_ne_zero k hp.ne_zero) (by omega) hcop, a_prime_pow hp hk]
    have hpk_ge2 : 2 ≤ p ^ k := by
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
    have hnot22 : ¬ (p ^ k = 2 ∧ u = 2) := by
      rintro ⟨hA, hB⟩; rw [hA, hB] at hcop; norm_num at hcop
    have hnot24 : ¬ (p ^ k = 2 ∧ u = 4) := by
      rintro ⟨hA, hB⟩; rw [hA, hB] at hcop; norm_num at hcop
    have hnot42 : ¬ (p ^ k = 4 ∧ u = 2) := by
      rintro ⟨hA, hB⟩; rw [hA, hB] at hcop; norm_num at hcop
    by_cases hA2 : p ^ k = 2
    · have hu5 : 5 ≤ u := by rw [hA2] at hmul; omega
      rw [hA2] at hpk_bound ⊢; omega
    · by_cases hB2 : u = 2
      · have hA5 : 5 ≤ p ^ k := by rw [hB2] at hmul; omega
        rw [hB2] at hau ⊢; omega
      · have hA3 : 3 ≤ p ^ k := by omega
        have hB3 : 3 ≤ u := by omega
        nlinarith

lemma a_le_sub_two_of_even {n : ℕ} (hn : 12 ≤ n) (heven : 2 ∣ n) : a n + 2 ≤ n := by
  set k := n.factorization 2
  have hk : 1 ≤ k := (Nat.prime_two.dvd_iff_one_le_factorization (by omega)).mp heven
  have h2k_dvd : 2 ^ k ∣ n := Nat.ordProj_dvd n 2
  set u := n / 2 ^ k
  have hmul : 2 ^ k * u = n := Nat.mul_div_cancel' h2k_dvd
  have hu_pos : 1 ≤ u :=
    Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hmul; omega
  have hnot2u : ¬ 2 ∣ u := by
    intro h2u
    rcases h2u with ⟨r, hr⟩
    have hdvd : 2 ^ (k + 1) ∣ n := ⟨r, by rw [← hmul, hr]; ring⟩
    have hle := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp hdvd
    omega
  have hcop : Nat.Coprime (2 ^ k) u :=
    Nat.Coprime.pow_left k (Nat.prime_two.coprime_iff_not_dvd.mpr hnot2u)
  by_cases hu1 : u = 1
  · rw [← hmul, hu1, mul_one] at hn ⊢
    have hk4 : 4 ≤ k := by
      by_contra hlt
      have : 2 ^ k ≤ 8 := by
        calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
          _ = 8 := by norm_num
      omega
    rw [a_prime_pow Nat.prime_two hk]
    have := two_pow_ge_add_four hk4
    omega
  · have hu3 : 3 ≤ u := by
      by_contra hlt
      have hu2 : u = 2 := by omega
      exact hnot2u (by rw [hu2])
    have hau : a u ≤ u + 1 := a_le_succ u hu_pos
    rw [← hmul, a_mul_coprime (by positivity) (by omega) hcop, a_prime_pow Nat.prime_two hk]
    by_cases hk1 : k = 1
    · rw [hk1, pow_one] at hmul ⊢
      have hu6 : 6 ≤ u := by omega
      omega
    · have hk2 : 2 ≤ k := by omega
      have h2k := two_pow_ge_add_two hk2
      nlinarith

lemma a_five : a 5 = 6 := by
  simpa using a_prime_pow (by decide : Nat.Prime 5) (by norm_num : 0 < 1)

lemma a_six : a 6 = 7 := by
  have h := a_mul_coprime (u := 2) (v := 3) (by norm_num) (by norm_num) (by decide)
  have h2 : a 2 = 3 := by simpa using a_prime_pow Nat.prime_two (by norm_num : 0 < 1)
  have h3 : a 3 = 4 := by simpa using a_prime_pow (by decide : Nat.Prime 3) (by norm_num : 0 < 1)
  simpa [h2, h3] using h

lemma a_seven : a 7 = 8 := by
  simpa using a_prime_pow (by decide : Nat.Prime 7) (by norm_num : 0 < 1)

lemma a_eight : a 8 = 5 := by
  have h := a_prime_pow Nat.prime_two (k := 3) (by norm_num)
  simpa using h

lemma reaches_five : ∀ m : ℕ, 4 < m → ∃ k : ℕ, a^[k] m = 5 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases h5 : m = 5
    · exact ⟨0, by simp [h5]⟩
    by_cases h6 : m = 6
    · exact ⟨3, by subst h6; simp [Function.iterate_succ_apply, a_six, a_seven, a_eight]⟩
    by_cases h7 : m = 7
    · exact ⟨2, by subst h7; simp [Function.iterate_succ_apply, a_seven, a_eight]⟩
    by_cases h8 : m = 8
    · exact ⟨1, by subst h8; simp [a_eight]⟩
    have hm9 : 9 ≤ m := by omega
    by_cases hp : m.Prime
    · have hm11 : 11 ≤ m := by
        have h9 : m ≠ 9 := fun h => by rw [h] at hp; exact absurd hp (by decide)
        have h10 : m ≠ 10 := fun h => by rw [h] at hp; exact absurd hp (by decide)
        omega
      have ham : a m = m + 1 := by
        simpa using a_prime_pow hp (k := 1) (by norm_num)
      have heven : 2 ∣ m + 1 := by
        have hodd := hp.odd_of_ne_two (by omega)
        obtain ⟨r, hr⟩ := hodd
        exact ⟨r + 1, by omega⟩
      have hstep : a (a m) + 2 ≤ m + 1 := by
        rw [ham]
        exact a_le_sub_two_of_even (by omega) heven
      have hge5 : 5 ≤ a (a m) := a_ge_five (by rw [ham]; omega)
      obtain ⟨k, hk⟩ := ih (a (a m)) (by omega) (by omega)
      refine ⟨k + 2, ?_⟩
      rw [Function.iterate_add_apply]
      simpa [Function.iterate_succ_apply] using hk
    · have hlt : a m < m := a_lt_of_composite (by omega) hp
      have hge5 : 5 ≤ a m := a_ge_five (by omega)
      obtain ⟨k, hk⟩ := ih (a m) hlt (by omega)
      refine ⟨k + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      exact hk

end OMA.OeisA008474

theorem OMA.solution : type_of% @OMA.S_oeis_a008474.main := by
  intro m hm
  exact OMA.OeisA008474.reaches_five m hm
