import OMAStatements.S_oeis_a342039

namespace OMA.S_oeis_a342039

open ArithmeticFunction


lemma prime_dvd_finset_lcm {r : ℕ} (hr : r.Prime) (s : Finset ℕ) (f : ℕ → ℕ)
    (h : r ∣ s.lcm f) : ∃ a ∈ s, r ∣ f a := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.lcm_empty] at h
    exact absurd (Nat.eq_one_of_dvd_one h) hr.one_lt.ne'
  | insert a s ha ih =>
    rw [Finset.lcm_insert] at h
    have hm : r ∣ f a * s.lcm f := dvd_trans h (Nat.lcm_dvd_mul (f a) (s.lcm f))
    rcases (Nat.Prime.dvd_mul hr).mp hm with h1 | h2
    · exact ⟨a, Finset.mem_insert_self _ _, h1⟩
    · obtain ⟨b, hb, hb'⟩ := ih h2
      exact ⟨b, Finset.mem_insert_of_mem hb, hb'⟩

lemma lam_odd_prime (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) : carmichael q = q - 1 := by
  have := carmichael_pow_of_prime_ne_two 1 hq hq2
  simp only [pow_one] at this
  rw [Nat.totient_prime hq] at this
  exact this

lemma lam_one : carmichael 1 = 1 := by
  have := carmichael_two_pow_of_le_two (n := 0) (by norm_num)
  simpa using this

lemma lam_two : carmichael 2 = 1 := by
  have := carmichael_two_pow_of_le_two (n := 1) (by norm_num)
  simpa using this

lemma lam_four : carmichael 4 = 2 := by
  have := carmichael_two_pow_of_le_two (n := 2) (by norm_num)
  simpa using this

lemma lam_three : carmichael 3 = 2 := lam_odd_prime 3 (by norm_num) (by norm_num)

lemma lam_five : carmichael 5 = 4 := lam_odd_prime 5 (by norm_num) (by norm_num)

lemma lam_six : carmichael 6 = 2 := by
  have := carmichael_mul (a := 2) (b := 3) (by norm_num)
  rw [show (2 : ℕ) * 3 = 6 by norm_num, lam_two, lam_three] at this
  rw [this]; norm_num

lemma lam_seven : carmichael 7 = 6 := lam_odd_prime 7 (by norm_num) (by norm_num)

lemma lam_653 : carmichael 653 = 652 := lam_odd_prime 653 (by norm_num) (by norm_num)

lemma lam_2609 : carmichael 2609 = 2608 := lam_odd_prime 2609 (by norm_num) (by norm_num)

lemma lam_4571 : carmichael 4571 = 1956 := by
  have := carmichael_mul (a := 7) (b := 653) (by norm_num)
  rw [show (7 : ℕ) * 653 = 4571 by norm_num, lam_seven, lam_653] at this
  rw [this]; norm_num

/-- 163 | lambda(j) for 0 < j < 4571 forces 653 | j or j = 2609. -/
lemma key_163 (j : ℕ) (hj0 : 0 < j) (hj : j < 4571) (h : 163 ∣ carmichael j) :
    653 ∣ j ∨ j = 2609 := by
  have : NeZero j := ⟨by omega⟩
  rw [carmichael_factorization j] at h
  obtain ⟨q, hq, hdq⟩ := prime_dvd_finset_lcm (by norm_num) _ _ h
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqj : q ∣ j := Nat.dvd_of_mem_primeFactors hq
  have he : 0 < j.factorization q := hqp.factorization_pos_of_dvd (by omega) hqj
  have hqe : q ^ j.factorization q ∣ j := Nat.ordProj_dvd j q
  by_cases h2 : q = 2
  · subst h2
    have hpow : ∃ x, carmichael (2 ^ j.factorization 2) = 2 ^ x := by
      by_cases he2 : j.factorization 2 = 2
      · rw [he2, carmichael_two_pow_of_le_two (by norm_num)]; exact ⟨_, rfl⟩
      · rw [carmichael_two_pow_of_ne_two he2]; exact ⟨_, rfl⟩
    obtain ⟨x, hx⟩ := hpow
    rw [hx] at hdq
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 163) hdq
    norm_num at this
  · rw [carmichael_pow_of_prime_ne_two _ hqp h2, Nat.totient_prime_pow hqp he] at hdq
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 163)).mp hdq with h3 | h3
    · exfalso
      have h163 : 163 ∣ q := Nat.Prime.dvd_of_dvd_pow (by norm_num) h3
      have hq163 : q = 163 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hqp).mp h163).symm
      have he2 : 2 ≤ j.factorization q := by
        by_contra hlt
        have h0 : j.factorization q - 1 = 0 := by omega
        rw [h0, pow_zero] at h3
        norm_num at h3
      have hdiv : q ^ 2 ∣ j := dvd_trans (pow_dvd_pow q he2) hqe
      rw [hq163] at hdiv
      have := Nat.le_of_dvd hj0 hdiv
      norm_num at this
      omega
    · have hqle : q ≤ j := Nat.le_of_dvd hj0 hqj
      obtain ⟨t, ht⟩ := h3
      have hq1 := hqp.one_lt
      have hq' : q = 163 * t + 1 := by omega
      have ht29 : t < 29 := by omega
      subst hq'
      interval_cases t
      all_goals (try (exfalso; norm_num at hqp; done))
      · left
        simpa using hqj
      · right
        obtain ⟨c, hc⟩ := hqj
        have : c = 1 := by
          rcases Nat.lt_or_ge c 2 with hc2 | hc2
          · interval_cases c <;> omega
          · omega
        subst this
        omega

lemma no_smaller (j : ℕ) (hj0 : 0 < j) (hj : j < 4571) : ¬ 2 * 489 ∣ carmichael j := by
  intro h
  have h163 : 163 ∣ carmichael j := dvd_trans (by norm_num) h
  have h3 : 3 ∣ carmichael j := dvd_trans (by norm_num) h
  rcases key_163 j hj0 hj h163 with ⟨r, rfl⟩ | rfl
  · have hr0 : 0 < r := by omega
    have hr : r ≤ 6 := by omega
    have hcop : Nat.Coprime 653 r :=
      (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr
        (fun hd => by have := Nat.le_of_dvd hr0 hd; omega)
    have hlam : carmichael (653 * r) = Nat.lcm 652 (carmichael r) := by
      rw [carmichael_mul hcop, lam_653]
    rw [hlam] at h3
    interval_cases r <;>
      simp only [lam_one, lam_two, lam_three, lam_four, lam_five, lam_six] at h3 <;> norm_num at h3
  · rw [lam_2609] at h3
    norm_num at h3

theorem is_a307437 : IsA307437 489 4571 := by
  refine ⟨by norm_num, ?_, no_smaller⟩
  rw [lam_4571]
  norm_num

/-- Song's conjecture, in the form: if A307437(m) is a multiple of p greater than p, then
m >= p - 1. It fails for p = 653, m = 489. -/
theorem disproof : ¬ (∀ p m k : ℕ, p.Prime → 1 ≤ m → IsA307437 m k → p ∣ k → p < k → p - 1 ≤ m) := by
  intro h
  have := h 653 489 4571 (by norm_num) (by norm_num) is_a307437 (by norm_num) (by norm_num)
  omega

end OMA.S_oeis_a342039

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a342039.main) :=
  OMA.S_oeis_a342039.disproof
