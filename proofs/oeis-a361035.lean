import OMAStatements.S_oeis_a361035

/-
Parity of a(n) = 9979200 (4n)! / (n! (n+3)!^3).
1. Divisibility, prime by prime. For odd p, Legendre's sums and the bound
   n/q + 3((n+3)/q) ≤ 4n/q + c(q), with c(q) = 0 for q ≥ 12, while the small q
   (3, 9, 5, 7, 11) are paid for by the valuations 4, 2, 1, 1 of 9979200.
   For p = 2, (p - 1) v_p(m!) = m - s_2(m) and s_2(4n) = s_2(n).
2. Hence v_2(a n) = 3 (s_2(n + 3) - 1), and s_2(m) = 1 exactly for powers of 2.
-/

namespace OMA.BC361035

open OMA.S_oeis_a361035

theorem s_two_mul (m : ℕ) : (Nat.digits 2 (2 * m)).sum = (Nat.digits 2 m).sum := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp
  · rw [Nat.digits_eq_cons_digits_div (b := 2) (n := 2 * m) (by norm_num) (by omega), List.sum_cons,
      show 2 * m % 2 = 0 by omega, show 2 * m / 2 = m by omega, zero_add]

theorem s_four_mul (m : ℕ) : (Nat.digits 2 (4 * m)).sum = (Nat.digits 2 m).sum := by
  rw [show 4 * m = 2 * (2 * m) by ring, s_two_mul, s_two_mul]

theorem s_eq_zero (t : ℕ) (h : (Nat.digits 2 t).sum = 0) : t = 0 := by
  induction' t using Nat.strong_induction_on with t ih
  by_contra ht
  rw [Nat.digits_eq_cons_digits_div (b := 2) (n := t) (by norm_num) ht, List.sum_cons] at h
  have h2 : t / 2 = 0 := ih (t / 2) (by omega) (by omega)
  omega

theorem s_eq_one_iff (m : ℕ) : (Nat.digits 2 m).sum = 1 ↔ ∃ k, m = 2 ^ k := by
  induction' m using Nat.strong_induction_on with m ih
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    constructor
    · intro h
      simp at h
    · rintro ⟨k, hk⟩
      exact absurd hk.symm (by positivity)
  · rw [Nat.digits_eq_cons_digits_div (b := 2) (n := m) (by norm_num) (by omega), List.sum_cons]
    rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
    · rw [show m % 2 = 0 by omega, show m / 2 = t by omega, zero_add, ih t (by omega)]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k + 1, by rw [pow_succ]; omega⟩
      · rintro ⟨k, hk⟩
        rcases k with _ | k
        · rw [pow_zero] at hk
          omega
        · refine ⟨k, ?_⟩
          rw [pow_succ] at hk
          omega
    · rw [show m % 2 = 1 by omega, show m / 2 = t by omega]
      constructor
      · intro h
        have ht0 : t = 0 := s_eq_zero t (by omega)
        refine ⟨0, ?_⟩
        rw [pow_zero]
        omega
      · rintro ⟨k, hk⟩
        rcases k with _ | k
        · rw [pow_zero] at hk
          have ht0 : t = 0 := by omega
          rw [ht0]
          simp
        · rw [pow_succ] at hk
          omega

theorem floor_bound (n q c : ℕ) (hq : 3 ≤ q) (h : ∀ r < q, 3 * ((r + 3) / q) ≤ 4 * r / q + c) :
    n / q + 3 * ((n + 3) / q) ≤ 4 * n / q + c := by
  have hq0 : 0 < q := by omega
  obtain ⟨A, r, hr, rfl⟩ : ∃ A r, r < q ∧ n = q * A + r :=
    ⟨n / q, n % q, Nat.mod_lt n hq0, (Nat.div_add_mod n q).symm⟩
  have e1 : (q * A + r) / q = A := by
    rw [Nat.mul_add_div hq0, Nat.div_eq_of_lt hr, add_zero]
  have e2 : (q * A + r + 3) / q = A + (r + 3) / q := by
    rw [add_assoc, Nat.mul_add_div hq0]
  have e3 : 4 * (q * A + r) / q = 4 * A + 4 * r / q := by
    rw [show 4 * (q * A + r) = q * (4 * A) + 4 * r by ring, Nat.mul_add_div hq0]
  rw [e1, e2, e3]
  have := h r hr
  omega

theorem big_q (q : ℕ) (hq : 12 ≤ q) : ∀ r < q, 3 * ((r + 3) / q) ≤ 4 * r / q + 0 := by
  intro r hr
  have hq0 : 0 < q := by omega
  rcases Nat.lt_or_ge (r + 3) q with h | h
  · rw [Nat.div_eq_of_lt h]
    simp
  · have h1 : (r + 3) / q < 2 := (Nat.div_lt_iff_lt_mul hq0).2 (by omega)
    have h2 : 3 ≤ 4 * r / q := (Nat.le_div_iff_mul_le hq0).2 (by omega)
    omega

theorem sum_peel (f g : ℕ → ℕ) (B c : ℕ) (hB : 3 ≤ B)
    (h12 : f 1 + f (1 + 1) ≤ g 1 + g (1 + 1) + c) (hrest : ∀ i, 3 ≤ i → f i ≤ g i) :
    ∑ i ∈ Finset.Ico 1 B, f i ≤ c + ∑ i ∈ Finset.Ico 1 B, g i := by
  rw [Finset.sum_eq_sum_Ico_succ_bot (show 1 < B by omega) f,
    Finset.sum_eq_sum_Ico_succ_bot (show 1 + 1 < B by omega) f,
    Finset.sum_eq_sum_Ico_succ_bot (show 1 < B by omega) g,
    Finset.sum_eq_sum_Ico_succ_bot (show 1 + 1 < B by omega) g]
  have h3 : ∑ i ∈ Finset.Ico (1 + 1 + 1) B, f i ≤ ∑ i ∈ Finset.Ico (1 + 1 + 1) B, g i :=
    Finset.sum_le_sum (fun i hi => hrest i (by have := (Finset.mem_Ico.mp hi).1; omega))
  omega

theorem prime_cases (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ 13 ≤ p := by
  have h2 := hp.two_le
  by_contra hc
  push_neg at hc
  obtain ⟨h3, h5, h7, h11, h13⟩ := hc
  interval_cases p <;> first | omega | (norm_num at hp)

theorem odd_val (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    padicValNat p n.factorial + 3 * padicValNat p (n + 3).factorial ≤
      padicValNat p 9979200 + padicValNat p (4 * n).factorial := by
  haveI := Fact.mk hp
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  set B := Nat.log p (4 * n + 3) + 3 with hB
  have hlog : ∀ x, x ≤ 4 * n + 3 → Nat.log p x < B := by
    intro x hx
    have := Nat.log_mono_right (b := p) hx
    omega
  rw [padicValNat_factorial (hlog n (by omega)), padicValNat_factorial (hlog (n + 3) (by omega)),
    padicValNat_factorial (hlog (4 * n) (by omega)), Finset.mul_sum, ← Finset.sum_add_distrib]
  have hrest : ∀ i, 3 ≤ i → n / p ^ i + 3 * ((n + 3) / p ^ i) ≤ 4 * n / p ^ i := by
    intro i hi
    have hq : 12 ≤ p ^ i := by
      calc 12 ≤ 3 ^ 3 := by norm_num
        _ ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hi
        _ ≤ p ^ i := Nat.pow_le_pow_left hp3 i
    have := floor_bound n (p ^ i) 0 (by omega) (big_q (p ^ i) hq)
    omega
  have key : ∀ c, c ≤ padicValNat p 9979200 →
      n / p ^ 1 + 3 * ((n + 3) / p ^ 1) + (n / p ^ (1 + 1) + 3 * ((n + 3) / p ^ (1 + 1))) ≤
        4 * n / p ^ 1 + 4 * n / p ^ (1 + 1) + c →
      ∑ i ∈ Finset.Ico 1 B, (n / p ^ i + 3 * ((n + 3) / p ^ i)) ≤
        padicValNat p 9979200 + ∑ i ∈ Finset.Ico 1 B, 4 * n / p ^ i := by
    intro c hc h12
    exact le_trans
      (sum_peel (fun i => n / p ^ i + 3 * ((n + 3) / p ^ i)) (fun i => 4 * n / p ^ i) B c
        (by omega) h12 hrest)
      (Nat.add_le_add_right hc _)
  rcases prime_cases p hp hp2 with h3 | h5 | h7 | h11 | h13
  · subst h3
    have hc : 4 ≤ padicValNat 3 9979200 :=
      (padicValNat_dvd_iff_le (p := 3) (a := 9979200) (by norm_num)).mp (by norm_num)
    apply key 4 hc
    have b1 := floor_bound n (3 ^ 1) 3 (by norm_num) (by decide)
    have b2 := floor_bound n (3 ^ (1 + 1)) 1 (by norm_num) (by decide)
    omega
  · subst h5
    have hc : 2 ≤ padicValNat 5 9979200 :=
      (padicValNat_dvd_iff_le (p := 5) (a := 9979200) (by norm_num)).mp (by norm_num)
    apply key 2 hc
    have b1 := floor_bound n (5 ^ 1) 2 (by norm_num) (by decide)
    have b2 := floor_bound n (5 ^ (1 + 1)) 0 (by norm_num) (big_q _ (by norm_num))
    omega
  · subst h7
    have hc : 1 ≤ padicValNat 7 9979200 :=
      (padicValNat_dvd_iff_le (p := 7) (a := 9979200) (by norm_num)).mp (by norm_num)
    apply key 1 hc
    have b1 := floor_bound n (7 ^ 1) 1 (by norm_num) (by decide)
    have b2 := floor_bound n (7 ^ (1 + 1)) 0 (by norm_num) (big_q _ (by norm_num))
    omega
  · subst h11
    have hc : 1 ≤ padicValNat 11 9979200 :=
      (padicValNat_dvd_iff_le (p := 11) (a := 9979200) (by norm_num)).mp (by norm_num)
    apply key 1 hc
    have b1 := floor_bound n (11 ^ 1) 1 (by norm_num) (by decide)
    have b2 := floor_bound n (11 ^ (1 + 1)) 0 (by norm_num) (big_q _ (by norm_num))
    omega
  · apply key 0 (Nat.zero_le _)
    have q1 : 12 ≤ p ^ 1 := by
      rw [pow_one]
      omega
    have q2 : 12 ≤ p ^ (1 + 1) := by
      calc 12 ≤ 13 ^ (1 + 1) := by norm_num
        _ ≤ p ^ (1 + 1) := Nat.pow_le_pow_left h13 _
    have b1 := floor_bound n (p ^ 1) 0 (by omega) (big_q _ q1)
    have b2 := floor_bound n (p ^ (1 + 1)) 0 (by omega) (big_q _ q2)
    omega

theorem two_val_eq (n : ℕ) :
    padicValNat 2 9979200 + padicValNat 2 (4 * n).factorial + 3 =
      padicValNat 2 n.factorial + 3 * padicValNat 2 (n + 3).factorial +
        3 * (Nat.digits 2 (n + 3)).sum := by
  have hC : padicValNat 2 9979200 = 6 := by
    have e : (9979200 : ℕ) = 2 ^ 6 * 155925 := by norm_num
    have h0 : padicValNat 2 155925 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    have hm := padicValNat.mul (p := 2) (a := 2 ^ 6) (b := 155925) (by norm_num) (by norm_num)
    rw [padicValNat.prime_pow, h0, add_zero] at hm
    rw [e, hm]
  have h1 := sub_one_mul_padicValNat_factorial (p := 2) (4 * n)
  have h2 := sub_one_mul_padicValNat_factorial (p := 2) n
  have h3 := sub_one_mul_padicValNat_factorial (p := 2) (n + 3)
  rw [s_four_mul] at h1
  rw [show (2 : ℕ) - 1 = 1 by norm_num, one_mul] at h1 h2 h3
  have l1 := Nat.digit_sum_le 2 n
  have l3 := Nat.digit_sum_le 2 (n + 3)
  omega

theorem dvd_main (n : ℕ) : n.factorial * (n + 3).factorial ^ 3 ∣ 9979200 * (4 * n).factorial := by
  have hD : n.factorial * (n + 3).factorial ^ 3 ≠ 0 := by positivity
  have hN : 9979200 * (4 * n).factorial ≠ 0 := by positivity
  rw [← Nat.factorization_prime_le_iff_dvd hD hN]
  intro p hp
  haveI := Fact.mk hp
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
    padicValNat.mul (p := p) (a := n.factorial) (b := (n + 3).factorial ^ 3) (by positivity)
      (by positivity),
    padicValNat.pow (p := p) (n + 3).factorial 3,
    padicValNat.mul (p := p) (a := 9979200) (b := (4 * n).factorial) (by norm_num) (by positivity)]
  by_cases h2 : p = 2
  · subst h2
    have heq := two_val_eq n
    have hs1 : 1 ≤ (Nat.digits 2 (n + 3)).sum := by
      by_contra h
      have := s_eq_zero (n + 3) (by omega)
      omega
    omega
  · exact odd_val p n hp h2

end OMA.BC361035

theorem OMA.solution : type_of% @OMA.S_oeis_a361035.main := by
  intro n
  have hN : 9979200 * (4 * n).factorial ≠ 0 := by positivity
  have hdvd := OMA.BC361035.dvd_main n
  have ha : OMA.S_oeis_a361035.a n =
      9979200 * (4 * n).factorial / (n.factorial * (n + 3).factorial ^ 3) := rfl
  have ha0 : OMA.S_oeis_a361035.a n ≠ 0 := by
    rw [ha]
    intro h
    have := Nat.div_mul_cancel hdvd
    rw [h, zero_mul] at this
    exact hN this.symm
  have hval : padicValNat 2 (OMA.S_oeis_a361035.a n) =
      padicValNat 2 (9979200 * (4 * n).factorial) -
        padicValNat 2 (n.factorial * (n + 3).factorial ^ 3) := by
    rw [ha, padicValNat.div_of_dvd hdvd]
  rw [padicValNat.mul (p := 2) (a := 9979200) (b := (4 * n).factorial) (by norm_num)
      (by positivity),
    padicValNat.mul (p := 2) (a := n.factorial) (b := (n + 3).factorial ^ 3) (by positivity)
      (by positivity),
    padicValNat.pow (p := 2) (n + 3).factorial 3] at hval
  have heq := OMA.BC361035.two_val_eq n
  have hs1 : 1 ≤ (Nat.digits 2 (n + 3)).sum := by
    by_contra h
    have := OMA.BC361035.s_eq_zero (n + 3) (by omega)
    omega
  have hodd : Odd (OMA.S_oeis_a361035.a n) ↔ padicValNat 2 (OMA.S_oeis_a361035.a n) = 0 := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero, padicValNat.eq_zero_iff]
    constructor
    · intro h
      exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · norm_num at h
      · exact absurd h ha0
      · exact h
  rw [hodd, hval]
  constructor
  · intro h
    have hs : (Nat.digits 2 (n + 3)).sum = 1 := by omega
    obtain ⟨k, hk⟩ := (OMA.BC361035.s_eq_one_iff (n + 3)).mp hs
    refine ⟨k, ?_, by omega⟩
    by_contra hk2
    have hk2' : k < 2 := by omega
    interval_cases k <;> simp at hk <;> omega
  · rintro ⟨k, hk2, rfl⟩
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    have hs : (Nat.digits 2 (2 ^ k - 3 + 3)).sum = 1 := by
      rw [show 2 ^ k - 3 + 3 = 2 ^ k by omega]
      exact (OMA.BC361035.s_eq_one_iff _).mpr ⟨k, rfl⟩
    omega
