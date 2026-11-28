import OMAStatements.S_mo_434166

-- Problem: MathOverflow 434166, (sum j^k)(sum 1/j^k) is an integer only for n = 1 (k = 2, 3).
-- For n >= 2 Bertrand gives a prime p with n/2 < p <= n. In sum 1/j^k only j = p is divisible by p, so
-- multiplying by p^k * prod_(j != p) j^k shows p^k | A = sum j^k (the other product is prime to p).
-- But 6 A = n(n+1)(2n+1) and 4 A = (n(n+1))^2: from p <= n < 2p each factor divisible by p is p, 2p
-- or 3p, at most one factor is, so p^2 (resp. p^3) cannot divide when p >= 5 (resp. p >= 3), i.e.
-- n >= 8; the cases n <= 7 are checked directly.

namespace OMA.MO434166

open OMA.S_mo_434166 Finset

lemma key (k n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) (h2p : n < 2 * p) (hp1 : 1 ≤ p)
    (hm : ∃ m : ℤ, F k n = m) : p ^ k ∣ ∑ j ∈ Icc 1 n, j ^ k := by
  obtain ⟨m, hm⟩ := hm
  set A : ℕ := ∑ j ∈ Icc 1 n, j ^ k with hAdef
  have hpmem : p ∈ Icc 1 n := Finset.mem_Icc.mpr ⟨hp1, hpn⟩
  set s' := (Icc 1 n).erase p
  set D : ℕ := ∏ j ∈ s', j ^ k
  have hdvd : ∀ j ∈ s', j ^ k ∣ D := fun j hj => Finset.dvd_prod_of_mem _ hj
  have hpos : ∀ j ∈ s', 0 < j := fun j hj =>
    (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hj)).1
  set I : ℕ := ∑ j ∈ s', D / j ^ k
  have hI : (∑ j ∈ s', 1 / (j : ℚ) ^ k) * D = I := by
    rw [Finset.sum_mul, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Nat.cast_div (hdvd j hj) (by have := hpos j hj; positivity)]
    push_cast; ring
  have hsplit : ∑ j ∈ Icc 1 n, 1 / (j : ℚ) ^ k = 1 / (p : ℚ) ^ k + ∑ j ∈ s', 1 / (j : ℚ) ^ k :=
    (Finset.add_sum_erase _ _ hpmem).symm
  have hAq : ∑ j ∈ Icc 1 n, (j : ℚ) ^ k = (A : ℚ) := by rw [hAdef]; push_cast; rfl
  have hpq : (p : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have heq : (m : ℚ) * D * p ^ k = A * D + A * I * p ^ k := by
    unfold F at hm
    rw [hAq, hsplit] at hm
    rw [← hm, ← hI]
    field_simp
  have heqZ : (m : ℤ) * D * p ^ k = A * D + A * I * p ^ k := by exact_mod_cast heq
  have hdz : ((p : ℤ) ^ k) ∣ (A * D : ℤ) := by
    refine ⟨m * D - A * I, ?_⟩
    linear_combination -heqZ
  have hdn : p ^ k ∣ A * D := by exact_mod_cast hdz
  have hcop : Nat.Coprime (p ^ k) D := by
    apply Nat.Coprime.pow_left
    apply Nat.Coprime.prod_right
    intro j hj
    apply Nat.Coprime.pow_right
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    rintro ⟨t, rfl⟩
    have hj' := Finset.mem_erase.mp hj
    have hjr := Finset.mem_Icc.mp hj'.2
    rcases t with _ | _ | t
    · simp at hjr
    · exact hj'.1 (by ring)
    · nlinarith
  exact hcop.dvd_of_dvd_mul_right hdn

lemma sum_sq (n : ℕ) : 6 * ∑ j ∈ Icc 1 n, j ^ 2 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]; ring

lemma sum_cube (n : ℕ) : 4 * ∑ j ∈ Icc 1 n, j ^ 3 = (n * (n + 1)) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]; ring

lemma bertrand_half (n : ℕ) (hn : 2 ≤ n) : ∃ p, p.Prime ∧ p ≤ n ∧ n < 2 * p := by
  obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
  exact ⟨p, hp, by omega, by omega⟩

lemma mult_eq {p a c : ℕ} (_hp : 0 < p) (hpa : p ∣ a) (lo : (c - 1) * p < a) (hi : a < (c + 1) * p)
    (hc : 1 ≤ c) : a = c * p := by
  obtain ⟨t, rfl⟩ := hpa
  have h1 : c - 1 < t := by
    by_contra h; push Not at h
    have : p * t ≤ (c - 1) * p := by rw [mul_comm]; exact Nat.mul_le_mul_right p h
    omega
  have h2 : t < c + 1 := by
    by_contra h; push Not at h
    have : (c + 1) * p ≤ p * t := by rw [mul_comm p]; exact Nat.mul_le_mul_right p h
    omega
  have : t = c := by omega
  subst this; ring

lemma p_dvd_one {p : ℕ} (hp : p.Prime) (h : p ∣ 1) : False := hp.one_lt.ne' (Nat.dvd_one.mp h)

lemma no_div2 (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) (h2p : n < 2 * p) (h5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ n * (n + 1) * (2 * n + 1) := by
  have hp0 := hp.pos
  have f1 : p ∣ n → n = p := fun h => by
    have := mult_eq hp0 h (c := 1) (by omega) (by omega) le_rfl; omega
  have f2 : p ∣ n + 1 → n + 1 = 2 * p := fun h => mult_eq hp0 h (c := 2) (by omega) (by omega) (by omega)
  have f3 : p ∣ 2 * n + 1 → 2 * n + 1 = 3 * p := fun h => by
    obtain ⟨t, ht⟩ := h
    have h1 : 2 < t := by
      by_contra hc; push Not at hc
      have : p * t ≤ p * 2 := Nat.mul_le_mul_left p hc
      omega
    have h2 : t < 4 := by
      by_contra hc; push Not at hc
      have : p * 4 ≤ p * t := Nat.mul_le_mul_left p hc
      omega
    interval_cases t <;> omega
  have n2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have n3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  intro h
  have hp1 : p ∣ n * (n + 1) * (2 * n + 1) := (dvd_pow_self p two_ne_zero).trans h
  rcases hp.dvd_mul.mp hp1 with h12 | h3
  · rcases hp.dvd_mul.mp h12 with h1 | h2
    · have e := f1 h1; rw [e] at h
      rw [show p * (p + 1) * (2 * p + 1) = p * ((p + 1) * (2 * p + 1)) by ring, pow_two,
        Nat.mul_dvd_mul_iff_left hp0] at h
      rcases hp.dvd_mul.mp h with h' | h'
      · exact p_dvd_one hp ((Nat.dvd_add_right (dvd_refl p)).mp h')
      · exact p_dvd_one hp ((Nat.dvd_add_right (dvd_mul_left p 2)).mp h')
    · have e := f2 h2
      rw [show n * (n + 1) * (2 * n + 1) = p * (2 * n * (2 * n + 1)) by rw [e]; ring, pow_two,
        Nat.mul_dvd_mul_iff_left hp0] at h
      rcases hp.dvd_mul.mp h with h' | h'
      · rcases hp.dvd_mul.mp h' with h'' | h''
        · exact n2 h''
        · have := f1 h''; omega
      · have := f3 h'; omega
  · have e := f3 h3
    rw [show n * (n + 1) * (2 * n + 1) = p * (3 * n * (n + 1)) by rw [e]; ring, pow_two,
      Nat.mul_dvd_mul_iff_left hp0] at h
    rcases hp.dvd_mul.mp h with h' | h'
    · rcases hp.dvd_mul.mp h' with h'' | h''
      · exact n3 h''
      · have := f1 h''; omega
    · have := f2 h'; omega

lemma no_div3 (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) (h2p : n < 2 * p) (h3 : 3 ≤ p) :
    ¬ p ^ 3 ∣ (n * (n + 1)) ^ 2 := by
  have hp0 := hp.pos
  have f1 : p ∣ n → n = p := fun h => by
    have := mult_eq hp0 h (c := 1) (by omega) (by omega) le_rfl; omega
  have f2 : p ∣ n + 1 → n + 1 = 2 * p := fun h => mult_eq hp0 h (c := 2) (by omega) (by omega) (by omega)
  have n2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  intro h
  have hp1 : p ∣ n * (n + 1) := hp.dvd_of_dvd_pow ((dvd_pow_self p (by norm_num : 3 ≠ 0)).trans h)
  rcases hp.dvd_mul.mp hp1 with h1 | h2
  · have e := f1 h1; rw [e] at h
    rw [show (p * (p + 1)) ^ 2 = p ^ 2 * (p + 1) ^ 2 by ring, pow_succ,
      Nat.mul_dvd_mul_iff_left (by positivity)] at h
    exact p_dvd_one hp ((Nat.dvd_add_right (dvd_refl p)).mp (hp.dvd_of_dvd_pow h))
  · have e := f2 h2
    rw [show (n * (n + 1)) ^ 2 = p ^ 2 * (2 * n) ^ 2 by rw [e]; ring, pow_succ,
      Nat.mul_dvd_mul_iff_left (by positivity)] at h
    rcases hp.dvd_mul.mp (hp.dvd_of_dvd_pow h) with h' | h'
    · exact n2 h'
    · have := f1 h'; omega

end OMA.MO434166

open OMA.MO434166 in
theorem OMA.solution : type_of% @OMA.S_mo_434166.main := by
  intro n hn
  have hF1 : ∀ k, ∃ m : ℤ, OMA.S_mo_434166.F k 1 = m := fun k => ⟨1, by simp [OMA.S_mo_434166.F]⟩
  refine ⟨⟨fun hm => ?_, fun h => h ▸ hF1 2⟩, ⟨fun hm => ?_, fun h => h ▸ hF1 3⟩⟩
  · by_contra hne
    obtain ⟨p, hp, hpn, h2p⟩ := bertrand_half n (by omega)
    have hk := key 2 n p hp hpn h2p hp.one_lt.le hm
    by_cases hsmall : n ≤ 7
    · have h2n : 2 ≤ n := by omega
      interval_cases n <;> interval_cases p <;>
        first | omega | (norm_num at hp; done) | (revert hk; decide)
    · have h6 := sum_sq n
      exact no_div2 n p hp hpn h2p (by omega) (h6 ▸ dvd_mul_of_dvd_right hk 6)
  · by_contra hne
    obtain ⟨p, hp, hpn, h2p⟩ := bertrand_half n (by omega)
    have hk := key 3 n p hp hpn h2p hp.one_lt.le hm
    by_cases hsmall : n ≤ 7
    · have h2n : 2 ≤ n := by omega
      interval_cases n <;> interval_cases p <;>
        first | omega | (norm_num at hp; done) | (revert hk; decide)
    · have h4 := sum_cube n
      exact no_div3 n p hp hpn h2p (by omega) (h4 ▸ dvd_mul_of_dvd_right hk 4)
