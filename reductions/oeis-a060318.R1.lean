import OMAStatements.S_oeis_a060318

-- Reduction oeis-a060318.R1 of A060318: smallest prime factor of the odd Catalan numbers Catalan(2^n - 1).
-- Credit: @notswizz
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Proved here: Catalan(2^n - 1) is always odd. Kummer gives v_2(C(2m, m)) = n for m = 2^n - 1, and
-- (m + 1) Catalan(m) = C(2m, m) with m + 1 = 2^n. If some base-3 digit of 2^n - 1 is 2, there is a carry in
-- m + m in base 3, so 3 | C(2m, m), and since 3 does not divide 2^n, 3 | Catalan(m) and minFac = 3.
-- The three exceptions n = 2, 5, 8 are computed directly (minFac 5, 7, 7).
-- Remaining: the pure ternary-digit statement that 2 is a base-3 digit of 2^n - 1 for every n >= 2 other than
-- 2, 5, 8 (an Erdős-type ternary digit question; checked for n < 5000). It is split by parity:
-- H1 for odd n, H2 for even n.

namespace OMA.R_oeis_a060318_R1

theorem digit_carry : ∀ x : ℕ, 2 ∈ Nat.digits 3 x → ∃ i, 3 ^ i ≤ 2 * (x % 3 ^ i) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    rcases Nat.eq_zero_or_pos x with h0 | hpos
    · subst h0; simp at hx
    · rw [Nat.digits_def' (by norm_num) hpos] at hx
      rcases List.mem_cons.mp hx with h | h
      · exact ⟨1, by omega⟩
      · obtain ⟨i, hi⟩ := ih (x / 3) (Nat.div_lt_self hpos (by norm_num)) h
        refine ⟨i + 1, ?_⟩
        rw [pow_succ', Nat.mod_mul]
        have := Nat.zero_le (x % 3)
        linarith

theorem mod_two_pow (n i : ℕ) (hi : i ≤ n) : (2 ^ n - 1) % 2 ^ i = 2 ^ i - 1 := by
  have h1 : 2 ^ n = 2 ^ i * 2 ^ (n - i) := by rw [← pow_add]; congr 1; omega
  have h2 : 1 ≤ 2 ^ (n - i) := Nat.one_le_two_pow
  have h3 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  have : 2 ^ n - 1 = (2 ^ i - 1) + 2 ^ i * (2 ^ (n - i) - 1) := by
    rw [h1, Nat.mul_sub_one]
    have : 2 ^ i ≤ 2 ^ i * 2 ^ (n - i) := Nat.le_mul_of_pos_right _ h2
    omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem cat_ne_zero (m : ℕ) : catalan m ≠ 0 := by
  intro h
  have := succ_mul_catalan_eq_centralBinom m
  rw [h, mul_zero] at this
  exact Nat.centralBinom_ne_zero m this.symm

theorem cat_odd (n : ℕ) : ¬ 2 ∣ catalan (2 ^ n - 1) := by
  set m := 2 ^ n - 1 with hm
  have hm1 : m + 1 = 2 ^ n := by have := @Nat.one_le_two_pow n; omega
  have hprod := succ_mul_catalan_eq_centralBinom m
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul] at hprod
  have hlog : Nat.log 2 (m + m) < n + 1 := by
    rcases Nat.eq_zero_or_pos (m + m) with h | h
    · rw [h]; simp
    · apply Nat.log_lt_of_lt_pow h.ne'
      rw [pow_succ]; omega
  have hv : padicValNat 2 ((m + m).choose m) = n := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [padicValNat_choose' hlog]
    have : (Finset.Ico 1 (n + 1)).filter (fun i => 2 ^ i ≤ m % 2 ^ i + m % 2 ^ i) = Finset.Ico 1 (n + 1) := by
      apply Finset.filter_true_of_mem
      intro i hi
      rw [Finset.mem_Ico] at hi
      rw [hm, mod_two_pow n i (by omega)]
      have : 2 ≤ 2 ^ i := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi.1
      omega
    rw [this]; simp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := cat_ne_zero m
  rw [← hprod, padicValNat.mul (by omega) hc, hm1, padicValNat.prime_pow] at hv
  have h0 : padicValNat 2 (catalan m) = 0 := by omega
  intro hd
  exact (dvd_iff_padicValNat_ne_zero hc).mp hd h0

theorem cat_three (n : ℕ) (h : ∃ i, 3 ^ i ≤ 2 * ((2 ^ n - 1) % 3 ^ i)) : 3 ∣ catalan (2 ^ n - 1) := by
  obtain ⟨i, hi⟩ := h
  set m := 2 ^ n - 1 with hm
  have hm1 : m + 1 = 2 ^ n := by have := @Nat.one_le_two_pow n; omega
  have hprod := succ_mul_catalan_eq_centralBinom m
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul] at hprod
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; rw [pow_zero, Nat.mod_one] at hi; omega
    · exact h0
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : padicValNat 3 ((m + m).choose m) ≠ 0 := by
    rw [padicValNat_choose' (b := i + Nat.log 3 (m + m) + 1) (by omega)]
    apply Finset.card_ne_zero.mpr
    refine ⟨i, ?_⟩
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hi1, by omega⟩, by omega⟩
  have hd : 3 ∣ (m + m).choose m :=
    (dvd_iff_padicValNat_ne_zero (Nat.choose_pos (by omega)).ne').mpr hv
  rw [← hprod, hm1] at hd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with h | h
  · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  · exact h

theorem minfac_three (n : ℕ) (h : ∃ i, 3 ^ i ≤ 2 * ((2 ^ n - 1) % 3 ^ i)) :
    (catalan (2 ^ n - 1)).minFac = 3 := by
  have h3 := cat_three n h
  have h2 := cat_odd n
  have hne1 : catalan (2 ^ n - 1) ≠ 1 := by intro h1; rw [h1] at h3; omega
  have hp := Nat.minFac_prime hne1
  have hle := Nat.minFac_le_of_dvd (by norm_num) h3
  have hge := hp.two_le
  have hd := Nat.minFac_dvd (catalan (2 ^ n - 1))
  interval_cases hm : (catalan (2 ^ n - 1)).minFac
  · exact absurd hd h2
  · rfl

def H1 : Prop := ∀ n : ℕ, Odd n → 2 ≤ n → n ≠ 5 → 2 ∈ Nat.digits 3 (2 ^ n - 1)

def H2 : Prop := ∀ n : ℕ, Even n → 2 ≤ n → n ≠ 2 → n ≠ 8 → 2 ∈ Nat.digits 3 (2 ^ n - 1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a060318.main := by
  intro h1 h2 n hn
  by_cases e2 : n = 2
  · subst e2
    rw [if_pos rfl]
    norm_num [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose,
      Nat.choose_eq_factorial_div_factorial, Nat.factorial]
  by_cases e5 : n = 5
  · subst e5
    rw [if_neg (by norm_num), if_pos (by norm_num)]
    norm_num [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose,
      Nat.choose_eq_factorial_div_factorial, Nat.factorial]
  by_cases e8 : n = 8
  · subst e8
    rw [if_neg (by norm_num), if_pos (by norm_num)]
    norm_num [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose,
      Nat.choose_eq_factorial_div_factorial, Nat.factorial]
  rw [if_neg e2, if_neg (by omega)]
  apply minfac_three
  apply digit_carry
  rcases Nat.even_or_odd n with he | ho
  · exact h2 n he hn e2 e8
  · exact h1 n ho hn e5

end OMA.R_oeis_a060318_R1
