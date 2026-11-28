import OMAStatements.S_oeis_a211419

namespace OeisA211419

open Finset

private def numNat (n : ℕ) : ℕ :=
  (6 * n).factorial * (2 * n).factorial

private def denNat (n : ℕ) : ℕ :=
  (4 * n).factorial * (3 * n).factorial * n.factorial

private lemma numNat_pos (n : ℕ) : 0 < numNat n :=
  Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)

private lemma denNat_pos (n : ℕ) : 0 < denNat n :=
  Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) (Nat.factorial_pos _)

private lemma numNat_cast (n : ℕ) :
    (numNat n : ℤ) = OMA.S_oeis_a211419.numerator n := by
  simp [numNat, OMA.S_oeis_a211419.numerator]

private lemma denNat_cast (n : ℕ) :
    (denNat n : ℤ) = OMA.S_oeis_a211419.denominator n := by
  simp [denNat, OMA.S_oeis_a211419.denominator]

private lemma nat_div_eq_of_bounds {a q k : ℕ} (hq : 0 < q) (h1 : k * q ≤ a)
    (h2 : a < (k + 1) * q) : a / q = k :=
  le_antisymm (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hq).mpr h2))
    ((Nat.le_div_iff_mul_le hq).mpr h1)

private def fStep (r q : ℕ) : ℕ :=
  6 * r / q + 2 * r / q - (4 * r / q + 3 * r / q)

private lemma fStep_le_aux {r q : ℕ} (hrq : r < q) :
    4 * r / q + 3 * r / q ≤ 6 * r / q + 2 * r / q := by
  have hq : 0 < q := by omega
  by_cases h1 : 6 * r < q
  · rw [nat_div_eq_of_bounds hq (k := 0) (by omega) (by omega),
        nat_div_eq_of_bounds hq (k := 0) (by omega) (by omega),
        nat_div_eq_of_bounds hq (k := 0) (by omega) (by omega),
        nat_div_eq_of_bounds hq (k := 0) (by omega) (by omega)]
  · by_cases h2 : 4 * r < q
    · rw [nat_div_eq_of_bounds hq (k := 0) (by omega) (by omega),
          nat_div_eq_of_bounds hq (k := 0) (by omega) (by omega),
          nat_div_eq_of_bounds hq (k := 1) (by omega) (by omega),
          nat_div_eq_of_bounds hq (k := 0) (by omega) (by omega)]
      omega
    · by_cases h3 : 3 * r < q
      · rw [nat_div_eq_of_bounds hq (k := 1) (by omega) (by omega),
            nat_div_eq_of_bounds hq (k := 0) (by omega) (by omega),
            nat_div_eq_of_bounds hq (k := 1) (by omega) (by omega),
            nat_div_eq_of_bounds hq (k := 0) (by omega) (by omega)]
      · by_cases h4 : 2 * r < q
        · rw [nat_div_eq_of_bounds hq (k := 1) (by omega) (by omega),
              nat_div_eq_of_bounds hq (k := 1) (by omega) (by omega),
              nat_div_eq_of_bounds hq (k := 2) (by omega) (by omega),
              nat_div_eq_of_bounds hq (k := 0) (by omega) (by omega)]
        · by_cases h5 : 3 * r < 2 * q
          · rw [nat_div_eq_of_bounds hq (k := 2) (by omega) (by omega),
                nat_div_eq_of_bounds hq (k := 1) (by omega) (by omega),
                nat_div_eq_of_bounds hq (k := 3) (by omega) (by omega),
                nat_div_eq_of_bounds hq (k := 1) (by omega) (by omega)]
            omega
          · by_cases h6 : 4 * r < 3 * q
            · rw [nat_div_eq_of_bounds hq (k := 2) (by omega) (by omega),
                  nat_div_eq_of_bounds hq (k := 2) (by omega) (by omega),
                  nat_div_eq_of_bounds hq (k := 4) (by omega) (by omega),
                  nat_div_eq_of_bounds hq (k := 1) (by omega) (by omega)]
              omega
            · by_cases h7 : 6 * r < 5 * q
              · rw [nat_div_eq_of_bounds hq (k := 3) (by omega) (by omega),
                    nat_div_eq_of_bounds hq (k := 2) (by omega) (by omega),
                    nat_div_eq_of_bounds hq (k := 4) (by omega) (by omega),
                    nat_div_eq_of_bounds hq (k := 1) (by omega) (by omega)]
              · rw [nat_div_eq_of_bounds hq (k := 3) (by omega) (by omega),
                    nat_div_eq_of_bounds hq (k := 2) (by omega) (by omega),
                    nat_div_eq_of_bounds hq (k := 5) (by omega) (by omega),
                    nat_div_eq_of_bounds hq (k := 1) (by omega) (by omega)]
                omega

private lemma fStep_eq_one_I1 {r q : ℕ} (h1 : q ≤ 6 * r) (h2 : 4 * r < q) :
    fStep r q = 1 := by
  have hq : 0 < q := by omega
  dsimp only [fStep]
  rw [nat_div_eq_of_bounds hq (k := 1) (by omega) (by omega),
      nat_div_eq_of_bounds hq (k := 0) (by omega) (by omega),
      nat_div_eq_of_bounds hq (k := 0) (by omega) (by omega),
      nat_div_eq_of_bounds hq (k := 0) (by omega) (by omega)]

private lemma fStep_eq_one_I2 {r q : ℕ} (h1 : q ≤ 2 * r) (h2 : 4 * r < 3 * q) :
    fStep r q = 1 := by
  have hq : 0 < q := by omega
  dsimp only [fStep]
  by_cases h3 : 3 * r < 2 * q
  · rw [nat_div_eq_of_bounds hq (k := 3) (by omega) (by omega),
        nat_div_eq_of_bounds hq (k := 1) (by omega) (by omega),
        nat_div_eq_of_bounds hq (k := 2) (by omega) (by omega),
        nat_div_eq_of_bounds hq (k := 1) (by omega) (by omega)]
  · rw [nat_div_eq_of_bounds hq (k := 4) (by omega) (by omega),
        nat_div_eq_of_bounds hq (k := 1) (by omega) (by omega),
        nat_div_eq_of_bounds hq (k := 2) (by omega) (by omega),
        nat_div_eq_of_bounds hq (k := 2) (by omega) (by omega)]

private lemma fStep_eq_one_I3 {r q : ℕ} (h1 : 5 * q ≤ 6 * r) (h2 : r < q) :
    fStep r q = 1 := by
  have hq : 0 < q := by omega
  dsimp only [fStep]
  rw [nat_div_eq_of_bounds hq (k := 5) (by omega) (by omega),
      nat_div_eq_of_bounds hq (k := 1) (by omega) (by omega),
      nat_div_eq_of_bounds hq (k := 3) (by omega) (by omega),
      nat_div_eq_of_bounds hq (k := 2) (by omega) (by omega)]

private lemma mul_div_decomp (c n q : ℕ) (hq : 0 < q) :
    c * n / q = c * (n / q) + c * (n % q) / q := by
  conv_lhs => rw [← Nat.div_add_mod n q]
  rw [Nat.mul_add, ← mul_assoc, mul_comm c q, mul_assoc, Nat.mul_add_div hq]

private lemma div_step_identity (n q : ℕ) (hq : 0 < q) :
    6 * n / q + 2 * n / q = 4 * n / q + 3 * n / q + n / q + fStep (n % q) q := by
  have hle := fStep_le_aux (Nat.mod_lt n hq)
  rw [mul_div_decomp 6 n q hq, mul_div_decomp 2 n q hq,
      mul_div_decomp 4 n q hq, mul_div_decomp 3 n q hq]
  dsimp only [fStep]
  omega

private lemma legendre_excess {p : ℕ} [hp : Fact p.Prime] (n : ℕ) {b : ℕ}
    (hb : Nat.log p (6 * n) < b) :
    padicValNat p (numNat n) =
      padicValNat p (denNat n) + ∑ e ∈ Finset.Ico 1 b, fStep (n % p ^ e) (p ^ e) := by
  have hb4 : Nat.log p (4 * n) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb
  have hb3 : Nat.log p (3 * n) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb
  have hb2 : Nat.log p (2 * n) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb
  have hb1 : Nat.log p n < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb
  have hnum : padicValNat p (numNat n) =
      ∑ e ∈ Finset.Ico 1 b, (6 * n / p ^ e + 2 * n / p ^ e) := by
    rw [numNat, padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
        padicValNat_factorial hb, padicValNat_factorial hb2, ← Finset.sum_add_distrib]
  have hden : padicValNat p (denNat n) =
      ∑ e ∈ Finset.Ico 1 b, (4 * n / p ^ e + 3 * n / p ^ e + n / p ^ e) := by
    rw [denNat,
        padicValNat.mul (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
          (Nat.factorial_ne_zero _),
        padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
        padicValNat_factorial hb4, padicValNat_factorial hb3, padicValNat_factorial hb1,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [hnum, hden, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  exact div_step_identity n (p ^ e) (pow_pos hp.out.pos e)

private lemma int_dvd_of_padicValNat_le (n : ℕ) (A : ℤ) (M : ℕ) (hA : A ≠ 0) (hM : 0 < M)
    (h : ∀ (p : ℕ), p.Prime →
      ∃ b : ℕ, Nat.log p (6 * n) < b ∧
        padicValNat p A.natAbs ≤
          padicValNat p M + ∑ e ∈ Finset.Ico 1 b, fStep (n % p ^ e) (p ^ e)) :
    OMA.S_oeis_a211419.denominator n * A ∣ (M : ℤ) * OMA.S_oeis_a211419.numerator n := by
  rw [← denNat_cast, ← numNat_cast, ← Int.natAbs_dvd_natAbs]
  rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
  have hlhs : denNat n * A.natAbs ≠ 0 :=
    Nat.mul_ne_zero (denNat_pos n).ne' (Int.natAbs_ne_zero.mpr hA)
  have hrhs : M * numNat n ≠ 0 :=
    Nat.mul_ne_zero hM.ne' (numNat_pos n).ne'
  refine (Nat.factorization_le_iff_dvd hlhs hrhs).mp ?_
  intro p
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    rw [padicValNat.mul (denNat_pos n).ne' (Int.natAbs_ne_zero.mpr hA),
        padicValNat.mul hM.ne' (numNat_pos n).ne']
    rcases h p hp with ⟨b, hb, hle⟩
    rw [legendre_excess n hb]
    omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

private lemma sum_fStep_ge_of_subset {p n b : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.Ico 1 b)
    (hone : ∀ e ∈ S, fStep (n % p ^ e) (p ^ e) = 1) :
    S.card ≤ ∑ e ∈ Finset.Ico 1 b, fStep (n % p ^ e) (p ^ e) := by
  calc
    S.card = ∑ _e ∈ S, 1 := by simp
    _ = ∑ e ∈ S, fStep (n % p ^ e) (p ^ e) :=
      Finset.sum_congr rfl fun e he => (hone e he).symm
    _ ≤ ∑ e ∈ Finset.Ico 1 b, fStep (n % p ^ e) (p ^ e) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _

private lemma pow_dvd_int_of_le_padicValNat {p e : ℕ} [Fact p.Prime] {a : ℤ}
    (ha : a ≠ 0) (hle : e ≤ padicValNat p a.natAbs) :
    ((p ^ e : ℕ) : ℤ) ∣ a := by
  have hd : p ^ e ∣ a.natAbs := (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr ha)).mpr hle
  exact Int.natCast_dvd.mpr hd

private lemma dvd_sub_mod_int (n q : ℕ) : (q : ℤ) ∣ (n : ℤ) - ((n % q : ℕ) : ℤ) := by
  refine ⟨(n / q : ℕ), ?_⟩
  have h := Nat.div_add_mod n q
  omega

private lemma extra_bit_p2 {n k : ℕ} (hk2 : 2 ≤ k) (hdvd : 2 ^ k ∣ n + 1) :
    ∃ e : ℕ, k < e ∧ e ≤ Nat.log 2 n + 3 ∧ fStep (n % 2 ^ e) (2 ^ e) = 1 := by
  have hn3 : 3 ≤ n := by
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    have hle : 2 ^ k ≤ n + 1 := Nat.le_of_dvd (Nat.succ_pos n) hdvd
    omega
  set L := Nat.log 2 n
  have hL_le : 2 ^ L ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hL_lt : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hpow_le : 2 ^ k ≤ 2 ^ (L + 1) :=
    le_trans (Nat.le_of_dvd (Nat.succ_pos n) hdvd) (by omega)
  have hk_le : k ≤ L + 1 :=
    (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp hpow_le
  by_cases hcase : k < L + 1 ∧ (4 * n < 3 * 2 ^ (L + 1) ∨ 5 * 2 ^ (L + 1) ≤ 6 * n)
  · refine ⟨L + 1, hcase.1, by omega, ?_⟩
    rw [Nat.mod_eq_of_lt hL_lt]
    have h2 : 2 ^ (L + 1) ≤ 2 * n := by
      rw [pow_succ]; omega
    rcases hcase.2 with hlt | hge
    · exact fStep_eq_one_I2 h2 hlt
    · exact fStep_eq_one_I3 hge hL_lt
  · refine ⟨L + 3, by omega, by omega, ?_⟩
    have hq_eq : 2 ^ (L + 3) = 4 * 2 ^ (L + 1) := by
      have : L + 3 = (L + 1) + 2 := by omega
      rw [this, pow_add]; ring
    have hn_lt : n < 2 ^ (L + 3) := by omega
    rw [Nat.mod_eq_of_lt hn_lt]
    by_cases heq : k = L + 1
    · have hd2 : 2 ^ (L + 1) ∣ n + 1 := heq ▸ hdvd
      have hge2 : 2 ^ (L + 1) ≤ n + 1 := Nat.le_of_dvd (Nat.succ_pos n) hd2
      have h4 : 4 ≤ 2 ^ (L + 1) := by
        rw [← heq]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      exact fStep_eq_one_I1 (by omega) (by omega)
    · have hlt_k : k < L + 1 := by omega
      have hnot : ¬ (4 * n < 3 * 2 ^ (L + 1) ∨ 5 * 2 ^ (L + 1) ≤ 6 * n) :=
        fun h => hcase ⟨hlt_k, h⟩
      exact fStep_eq_one_I1 (by omega) (by omega)

private lemma fStep_pred_self {q : ℕ} (hq : q = 2 ∨ q = 3 ∨ 6 ≤ q) :
    fStep (q - 1) q = 1 := by
  rcases hq with rfl | rfl | h6
  · exact fStep_eq_one_I2 (by omega) (by omega)
  · exact fStep_eq_one_I2 (by omega) (by omega)
  · exact fStep_eq_one_I3 (by omega) (by omega)

private lemma conj1 :
    ∀ n : ℕ, OMA.S_oeis_a211419.denominator n * ((n : ℤ) + 1) ∣
      5 * OMA.S_oeis_a211419.numerator n := by
  intro n
  have hA : ((n : ℤ) + 1) ≠ 0 := by omega
  have h5 : ((5 : ℕ) : ℤ) = 5 := rfl
  rw [← h5]
  refine int_dvd_of_padicValNat_le n ((n : ℤ) + 1) 5 hA (by norm_num) ?_
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  have hnat : ((n : ℤ) + 1).natAbs = n + 1 := by omega
  rw [hnat]
  set k := padicValNat p (n + 1)
  have hmod_pred : ∀ e : ℕ, 1 ≤ e → e ≤ k → n % p ^ e = p ^ e - 1 := by
    intro e he1 hek
    have hd : p ^ e ∣ n + 1 :=
      (padicValNat_dvd_iff_le (Nat.succ_ne_zero n)).mpr hek
    have hq_pos : 0 < p ^ e := pow_pos hp.pos e
    have hq_ge2 : 2 ≤ p ^ e := by
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he1
    have hmod0 : (n + 1) % p ^ e = 0 := Nat.mod_eq_zero_of_dvd hd
    have hlt : n % p ^ e < p ^ e := Nat.mod_lt n hq_pos
    have hstep : (n % p ^ e + 1) % p ^ e = 0 := by
      rw [← hmod0, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    by_cases hlt1 : n % p ^ e + 1 < p ^ e
    · rw [Nat.mod_eq_of_lt hlt1] at hstep
      exact absurd hstep (Nat.succ_ne_zero _)
    · omega
  by_cases hp5 : p = 5
  · subst hp5
    refine ⟨max (Nat.log 5 (6 * n) + 1) (k + 1), by omega, ?_⟩
    have hv5 : padicValNat 5 5 = 1 := padicValNat.self (by norm_num)
    rw [hv5]
    by_cases hk0 : k = 0
    · omega
    · have hsub : Finset.Ico 2 (k + 1) ⊆ Finset.Ico 1 (max (Nat.log 5 (6 * n) + 1) (k + 1)) := by
        intro e he
        simp only [Finset.mem_Ico] at he ⊢
        omega
      have hone : ∀ e ∈ Finset.Ico 2 (k + 1), fStep (n % 5 ^ e) (5 ^ e) = 1 := by
        intro e he
        simp only [Finset.mem_Ico] at he
        rw [hmod_pred e (by omega) (by omega)]
        have h25 : 6 ≤ 5 ^ e := by
          calc 6 ≤ 5 ^ 2 := by norm_num
            _ ≤ 5 ^ e := Nat.pow_le_pow_right (by norm_num) he.1
        exact fStep_pred_self (Or.inr (Or.inr h25))
      have hcard := sum_fStep_ge_of_subset hsub hone
      rw [Nat.card_Ico] at hcard
      omega
  · by_cases hp2 : p = 2
    · subst hp2
      by_cases hk2 : 2 ≤ k
      · have hdvd : 2 ^ k ∣ n + 1 :=
          (padicValNat_dvd_iff_le (Nat.succ_ne_zero n)).mpr le_rfl
        rcases extra_bit_p2 hk2 hdvd with ⟨e_star, he_gt, he_le, hf_star⟩
        set b := max (Nat.log 2 (6 * n) + 1) (Nat.log 2 n + 4)
        refine ⟨b, by omega, ?_⟩
        set S := insert e_star ((Finset.Ico 1 (k + 1)).erase 2)
        have hL_ge : k ≤ Nat.log 2 n + 1 := by
          have hn0 : n ≠ 0 := by
            have h4 : 4 ≤ 2 ^ k := by
              calc 4 = 2 ^ 2 := by norm_num
                _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
            have := Nat.le_of_dvd (Nat.succ_pos n) hdvd
            omega
          have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
          have hle : 2 ^ k ≤ 2 ^ (Nat.log 2 n + 1) :=
            le_trans (Nat.le_of_dvd (Nat.succ_pos n) hdvd) (by omega)
          exact (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp hle
        have hsub : S ⊆ Finset.Ico 1 b := by
          intro e he
          simp only [S, Finset.mem_insert, Finset.mem_erase, Finset.mem_Ico] at he ⊢
          rcases he with rfl | ⟨_, he1, he2⟩
          · omega
          · omega
        have hone : ∀ e ∈ S, fStep (n % 2 ^ e) (2 ^ e) = 1 := by
          intro e he
          simp only [S, Finset.mem_insert, Finset.mem_erase, Finset.mem_Ico] at he
          rcases he with rfl | ⟨hne2, he1, he2⟩
          · exact hf_star
          · rw [hmod_pred e he1 (by omega)]
            by_cases heq1 : e = 1
            · subst heq1
              exact fStep_pred_self (Or.inl (by norm_num))
            · have h8 : 6 ≤ 2 ^ e := by
                calc 6 ≤ 2 ^ 3 := by norm_num
                  _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
              exact fStep_pred_self (Or.inr (Or.inr h8))
        have hnotmem : e_star ∉ (Finset.Ico 1 (k + 1)).erase 2 := by
          simp only [Finset.mem_erase, Finset.mem_Ico]
          omega
        have h2mem : 2 ∈ Finset.Ico 1 (k + 1) := by
          simp only [Finset.mem_Ico]; omega
        have hcard_S : S.card = k := by
          rw [Finset.card_insert_of_notMem hnotmem, Finset.card_erase_of_mem h2mem, Nat.card_Ico]
          omega
        have hsum := sum_fStep_ge_of_subset hsub hone
        omega
      · refine ⟨max (Nat.log 2 (6 * n) + 1) (k + 1), by omega, ?_⟩
        by_cases hk0 : k = 0
        · omega
        · have hk1 : k = 1 := by omega
          have hsub : ({1} : Finset ℕ) ⊆ Finset.Ico 1 (max (Nat.log 2 (6 * n) + 1) (k + 1)) := by
            intro e he
            simp only [Finset.mem_singleton, Finset.mem_Ico] at he ⊢
            omega
          have hone : ∀ e ∈ ({1} : Finset ℕ), fStep (n % 2 ^ e) (2 ^ e) = 1 := by
            intro e he
            simp only [Finset.mem_singleton] at he
            subst he
            rw [hmod_pred 1 le_rfl (by omega)]
            exact fStep_pred_self (Or.inl (by norm_num))
          have hsum := sum_fStep_ge_of_subset hsub hone
          simp only [Finset.card_singleton] at hsum
          omega
    · refine ⟨max (Nat.log p (6 * n) + 1) (k + 1), by omega, ?_⟩
      have hsub : Finset.Ico 1 (k + 1) ⊆ Finset.Ico 1 (max (Nat.log p (6 * n) + 1) (k + 1)) := by
        intro e he
        simp only [Finset.mem_Ico] at he ⊢
        omega
      have hone : ∀ e ∈ Finset.Ico 1 (k + 1), fStep (n % p ^ e) (p ^ e) = 1 := by
        intro e he
        simp only [Finset.mem_Ico] at he
        rw [hmod_pred e he.1 (by omega)]
        by_cases hp3 : p = 3
        · subst hp3
          by_cases he1 : e = 1
          · subst he1
            exact fStep_pred_self (Or.inr (Or.inl (by norm_num)))
          · have h9 : 6 ≤ 3 ^ e := by
              calc 6 ≤ 3 ^ 2 := by norm_num
                _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
            exact fStep_pred_self (Or.inr (Or.inr h9))
        · have hp7 : 7 ≤ p := by
            have h2 := hp.two_le
            have hne4 : p ≠ 4 := by intro h; rw [h] at hp; norm_num at hp
            have hne6 : p ≠ 6 := by intro h; rw [h] at hp; norm_num at hp
            omega
          have h6 : 6 ≤ p ^ e := by
            calc 6 ≤ p := by omega
              _ = p ^ 1 := (pow_one p).symm
              _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he.1
          exact fStep_pred_self (Or.inr (Or.inr h6))
      have hsum := sum_fStep_ge_of_subset hsub hone
      rw [Nat.card_Ico] at hsum
      omega

private lemma conj2 :
    ∀ n : ℕ, OMA.S_oeis_a211419.denominator n * (4 * (n : ℤ) + 1) ∣
      OMA.S_oeis_a211419.numerator n := by
  intro n
  have h1 : ((1 : ℕ) : ℤ) * OMA.S_oeis_a211419.numerator n = OMA.S_oeis_a211419.numerator n := by
    simp
  rw [← h1]
  refine int_dvd_of_padicValNat_le n (4 * (n : ℤ) + 1) 1 (by omega) (by norm_num) ?_
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  have hnat : (4 * (n : ℤ) + 1).natAbs = 4 * n + 1 := by omega
  rw [hnat]
  set k := padicValNat p (4 * n + 1)
  refine ⟨max (Nat.log p (6 * n) + 1) (k + 1), by omega, ?_⟩
  by_cases hk0 : k = 0
  · omega
  · have hp_dvd : p ∣ 4 * n + 1 := by
      have hd1 : p ^ 1 ∣ 4 * n + 1 :=
        (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
      simpa using hd1
    have hp_odd : p % 2 = 1 := by
      by_contra hne
      have h2p : 2 ∣ p := by omega
      have h2n : 2 ∣ 4 * n + 1 := dvd_trans h2p hp_dvd
      omega
    have hsub : Finset.Ico 1 (k + 1) ⊆ Finset.Ico 1 (max (Nat.log p (6 * n) + 1) (k + 1)) := by
      intro e he
      simp only [Finset.mem_Ico] at he ⊢
      omega
    have hone : ∀ e ∈ Finset.Ico 1 (k + 1), fStep (n % p ^ e) (p ^ e) = 1 := by
      intro e he
      simp only [Finset.mem_Ico] at he
      set q := p ^ e
      have hq_ge3 : 3 ≤ q := by
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        calc 3 ≤ p := hp3
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he.1
      have hq_odd : q % 2 = 1 := by
        have : Odd p := Nat.odd_iff.mpr hp_odd
        exact Nat.odd_iff.mp (this.pow)
      have hd : q ∣ 4 * n + 1 :=
        (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
      have hr_lt : n % q < q := Nat.mod_lt n (by omega)
      have hd_r : q ∣ 4 * (n % q) + 1 := by
        have hdecomp : 4 * n + 1 = q * (4 * (n / q)) + (4 * (n % q) + 1) := by
          have := Nat.div_add_mod n q
          linarith
        rw [hdecomp] at hd
        exact (Nat.dvd_add_right (dvd_mul_right q _)).mp hd
      rcases hd_r with ⟨m, hm⟩
      have hm_odd : m % 2 = 1 := by
        have hqm : (q * m) % 2 = 1 := by omega
        rw [Nat.mul_mod, hq_odd] at hqm
        omega
      have hm_cases : m = 1 ∨ m = 3 := by
        have hlt : q * m < q * 5 := by omega
        have hm_lt5 : m < 5 := (Nat.mul_lt_mul_left (by omega)).mp hlt
        omega
      rcases hm_cases with rfl | rfl
      · exact fStep_eq_one_I1 (by omega) (by omega)
      · exact fStep_eq_one_I2 (by omega) (by omega)
    have hsum := sum_fStep_ge_of_subset hsub hone
    rw [Nat.card_Ico] at hsum
    omega

private lemma conj3 :
    ∀ n : ℕ, OMA.S_oeis_a211419.denominator n * (6 * (n : ℤ) - 1) ∣
      OMA.S_oeis_a211419.numerator n := by
  intro n
  cases n with
  | zero =>
    simp [OMA.S_oeis_a211419.denominator, OMA.S_oeis_a211419.numerator]
  | succ m =>
    set n := m + 1
    have h1 : ((1 : ℕ) : ℤ) * OMA.S_oeis_a211419.numerator n = OMA.S_oeis_a211419.numerator n := by
      simp
    rw [← h1]
    refine int_dvd_of_padicValNat_le n (6 * (n : ℤ) - 1) 1 (by omega) (by norm_num) ?_
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    have hnat : (6 * (n : ℤ) - 1).natAbs = 6 * n - 1 := by omega
    rw [hnat]
    set k := padicValNat p (6 * n - 1)
    refine ⟨max (Nat.log p (6 * n) + 1) (k + 1), by omega, ?_⟩
    by_cases hk0 : k = 0
    · omega
    · have hp_dvd : p ∣ 6 * n - 1 := by
        have hd1 : p ^ 1 ∣ 6 * n - 1 :=
          (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
        simpa using hd1
      have hp_ge5 : 5 ≤ p := by
        have h2 := hp.two_le
        have hne2 : p ≠ 2 := by intro h; rw [h] at hp_dvd; omega
        have hne3 : p ≠ 3 := by intro h; rw [h] at hp_dvd; omega
        have hne4 : p ≠ 4 := by intro h; rw [h] at hp; norm_num at hp
        omega
      have hsub : Finset.Ico 1 (k + 1) ⊆ Finset.Ico 1 (max (Nat.log p (6 * n) + 1) (k + 1)) := by
        intro e he
        simp only [Finset.mem_Ico] at he ⊢
        omega
      have hone : ∀ e ∈ Finset.Ico 1 (k + 1), fStep (n % p ^ e) (p ^ e) = 1 := by
        intro e he
        simp only [Finset.mem_Ico] at he
        set q := p ^ e
        have hq_ge5 : 5 ≤ q := by
          calc 5 ≤ p := hp_ge5
            _ = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he.1
        have hq_cop2 : ¬ (2 ∣ q) := by
          intro h2
          have := Nat.prime_two.dvd_of_dvd_pow h2
          have : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this
          omega
        have hq_cop3 : ¬ (3 ∣ q) := by
          intro h3
          have := Nat.prime_three.dvd_of_dvd_pow h3
          have : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp this
          omega
        have hd : q ∣ 6 * n - 1 :=
          (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
        have hd_z : (q : ℤ) ∣ 6 * (n : ℤ) - 1 := by
          have : ((6 * n - 1 : ℕ) : ℤ) = 6 * (n : ℤ) - 1 := by omega
          rw [← this]
          exact Int.natCast_dvd_natCast.mpr hd
        have hd_r : (q : ℤ) ∣ 6 * ((n % q : ℕ) : ℤ) - 1 := by
          have hsub_z : (q : ℤ) ∣ 6 * ((n : ℤ) - ((n % q : ℕ) : ℤ)) :=
            dvd_mul_of_dvd_right (dvd_sub_mod_int n q) 6
          have hdiff := dvd_sub hd_z hsub_z
          have heq : (6 * (n : ℤ) - 1) - 6 * ((n : ℤ) - ((n % q : ℕ) : ℤ)) =
              6 * ((n % q : ℕ) : ℤ) - 1 := by ring
          rwa [heq] at hdiff
        rcases hd_r with ⟨t, ht⟩
        have hr_lt : n % q < q := Nat.mod_lt n (by omega)
        have hr_lt_z : ((n % q : ℕ) : ℤ) < (q : ℤ) := Int.ofNat_lt.mpr hr_lt
        have hq_ge5_z : (5 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq_ge5
        have ht_ge0 : 0 ≤ t := by nlinarith
        have ht_ne0 : t ≠ 0 := by intro h; subst h; omega
        have ht_pos : 1 ≤ t := by omega
        have ht_le5 : t ≤ 5 := by nlinarith
        have ht_ne2 : t ≠ 2 := by intro h; subst h; omega
        have ht_ne3 : t ≠ 3 := by intro h; subst h; omega
        have ht_ne4 : t ≠ 4 := by intro h; subst h; omega
        have ht_cases : t = 1 ∨ t = 5 := by omega
        rcases ht_cases with rfl | rfl
        · exact fStep_eq_one_I1 (by omega) (by omega)
        · exact fStep_eq_one_I3 (by omega) hr_lt
      have hsum := sum_fStep_ge_of_subset hsub hone
      rw [Nat.card_Ico] at hsum
      omega

private lemma padicValNat_prod_natAbs {p : ℕ} [Fact p.Prime] (S : Finset ℕ) (f : ℕ → ℤ)
    (hf : ∀ i ∈ S, f i ≠ 0) :
    padicValNat p (∏ i ∈ S, f i).natAbs = ∑ i ∈ S, padicValNat p (f i).natAbs := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Int.natAbs_mul, Finset.sum_insert ha]
    have hfa : (f a).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hf a (Finset.mem_insert_self a s))
    have hfs : (∏ i ∈ s, f i).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [padicValNat.mul hfa hfs, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

private lemma uniform_prod_dvd (r B T0 : ℕ) (hr : 0 < r) (hBT : B ≤ T0)
    (s : ℕ → ℕ) (hs_le : ∀ p, s p ≤ 1) (hs_gt : ∀ p, T0 < p → s p = 0)
    (g : ℕ → ℕ → ℤ)
    (h_ne : ∀ n, ∀ i < r, g i n ≠ 0)
    (h_diff : ∀ n, ∀ i < r, ∀ j < r, i ≠ j →
      0 < (g i n - g j n).natAbs ∧ (g i n - g j n).natAbs ≤ B)
    (h_step : ∀ n p i e, p.Prime → i < r → s p < e → T0 < p ^ (e - s p) →
      ((p ^ e : ℕ) : ℤ) ∣ g i n → fStep (n % p ^ (e - s p)) (p ^ (e - s p)) = 1) :
    ∃ M : ℤ, 0 < M ∧
      ∀ n : ℕ, OMA.S_oeis_a211419.denominator n * (∏ i ∈ Finset.range r, g i n) ∣
        M * OMA.S_oeis_a211419.numerator n := by
  classical
  set E := r * B + T0 + 2
  set Pset := (Finset.range (T0 + 1)).filter Nat.Prime
  set Mnat : ℕ := ∏ q ∈ Pset, q ^ E
  have hMpos : 0 < Mnat :=
    Finset.prod_pos fun q hq => pow_pos (Finset.mem_filter.mp hq).2.pos E
  refine ⟨(Mnat : ℤ), Int.natCast_pos.mpr hMpos, ?_⟩
  intro n
  have hPne : (∏ i ∈ Finset.range r, g i n) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => h_ne n i (Finset.mem_range.mp hi)
  refine int_dvd_of_padicValNat_le n (∏ i ∈ Finset.range r, g i n) Mnat hPne hMpos ?_
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValNat_prod_natAbs (Finset.range r) (fun i => g i n)
      fun i hi => h_ne n i (Finset.mem_range.mp hi)]
  have hne_range : (Finset.range r).Nonempty := ⟨0, Finset.mem_range.mpr hr⟩
  obtain ⟨i0, hi0_mem, hi0_max⟩ :=
    Finset.exists_max_image (Finset.range r) (fun i => padicValNat p (g i n).natAbs) hne_range
  have hi0_lt : i0 < r := Finset.mem_range.mp hi0_mem
  set kmax := padicValNat p (g i0 n).natAbs
  set b := max (Nat.log p (6 * n) + 1) (kmax + 2)
  refine ⟨b, by omega, ?_⟩
  have h_other_dvd : ∀ i ∈ Finset.range r, i ≠ i0 →
      p ^ padicValNat p (g i n).natAbs ∣ (g i n - g i0 n).natAbs := by
    intro i hi hne
    have hle : padicValNat p (g i n).natAbs ≤ kmax := hi0_max i hi
    have h1 : ((p ^ padicValNat p (g i n).natAbs : ℕ) : ℤ) ∣ g i n :=
      pow_dvd_int_of_le_padicValNat (h_ne n i (Finset.mem_range.mp hi)) le_rfl
    have h2 : ((p ^ padicValNat p (g i n).natAbs : ℕ) : ℤ) ∣ g i0 n :=
      pow_dvd_int_of_le_padicValNat (h_ne n i0 hi0_lt) hle
    exact Int.natCast_dvd.mp (dvd_sub h1 h2)
  by_cases hp_gt : T0 < p
  · have hsp0 : s p = 0 := hs_gt p hp_gt
    have h_zero : ∀ i ∈ (Finset.range r).erase i0, padicValNat p (g i n).natAbs = 0 := by
      intro i hi
      have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
      have hi_mem : i ∈ Finset.range r := (Finset.mem_erase.mp hi).2
      have hi_lt : i < r := Finset.mem_range.mp hi_mem
      have hd := h_other_dvd i hi_mem hne
      have hdiff := h_diff n i hi_lt i0 hi0_lt hne
      have hle_B : p ^ padicValNat p (g i n).natAbs ≤ B :=
        le_trans (Nat.le_of_dvd hdiff.1 hd) hdiff.2
      by_contra hpos
      have hge1 : 1 ≤ padicValNat p (g i n).natAbs := by omega
      have hp_le : p ≤ p ^ padicValNat p (g i n).natAbs := by
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ padicValNat p (g i n).natAbs := Nat.pow_le_pow_right hp.pos hge1
      omega
    have hsum_val : ∑ i ∈ Finset.range r, padicValNat p (g i n).natAbs = kmax := by
      rw [← Finset.add_sum_erase _ _ hi0_mem]
      rw [Finset.sum_eq_zero h_zero, add_zero]
    rw [hsum_val]
    have hsub : Finset.Ico 1 (kmax + 1) ⊆ Finset.Ico 1 b := by
      intro d hd
      simp only [Finset.mem_Ico] at hd ⊢
      omega
    have hone : ∀ d ∈ Finset.Ico 1 (kmax + 1), fStep (n % p ^ d) (p ^ d) = 1 := by
      intro d hd
      simp only [Finset.mem_Ico] at hd
      have hpow_gt : T0 < p ^ (d - s p) := by
        rw [hsp0, Nat.sub_zero]
        have : p ≤ p ^ d := by
          calc p = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ d := Nat.pow_le_pow_right hp.pos hd.1
        omega
      have hstep := h_step n p i0 d hp hi0_lt (by omega) hpow_gt
        (pow_dvd_int_of_le_padicValNat (h_ne n i0 hi0_lt) (by omega))
      rwa [hsp0, Nat.sub_zero] at hstep
    have hsum := sum_fStep_ge_of_subset hsub hone
    rw [Nat.card_Ico] at hsum
    omega
  · have hp_le : p ≤ T0 := by omega
    have hp_mem : p ∈ Pset :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
    have hdvd_M : p ^ E ∣ Mnat := Finset.dvd_prod_of_mem (fun q => q ^ E) hp_mem
    have hE_le : E ≤ padicValNat p Mnat :=
      (padicValNat_dvd_iff_le hMpos.ne').mp hdvd_M
    have h_other_le : ∀ i ∈ (Finset.range r).erase i0, padicValNat p (g i n).natAbs ≤ B := by
      intro i hi
      have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
      have hi_mem : i ∈ Finset.range r := (Finset.mem_erase.mp hi).2
      have hi_lt : i < r := Finset.mem_range.mp hi_mem
      have hd := h_other_dvd i hi_mem hne
      have hdiff := h_diff n i hi_lt i0 hi0_lt hne
      have hle_B : p ^ padicValNat p (g i n).natAbs ≤ B :=
        le_trans (Nat.le_of_dvd hdiff.1 hd) hdiff.2
      have hv_lt : padicValNat p (g i n).natAbs < 2 ^ padicValNat p (g i n).natAbs :=
        Nat.lt_two_pow_self
      have h2p : 2 ^ padicValNat p (g i n).natAbs ≤ p ^ padicValNat p (g i n).natAbs :=
        Nat.pow_le_pow_left hp.two_le _
      omega
    have hsum_val : ∑ i ∈ Finset.range r, padicValNat p (g i n).natAbs ≤ kmax + r * B := by
      rw [← Finset.add_sum_erase _ _ hi0_mem]
      have hle1 : ∑ i ∈ (Finset.range r).erase i0, padicValNat p (g i n).natAbs ≤
          ∑ _i ∈ (Finset.range r).erase i0, B := Finset.sum_le_sum h_other_le
      have hcard_er : ((Finset.range r).erase i0).card ≤ r := by
        rw [Finset.card_erase_of_mem hi0_mem, Finset.card_range]; omega
      simp only [Finset.sum_const, smul_eq_mul] at hle1
      have hmul : ((Finset.range r).erase i0).card * B ≤ r * B :=
        Nat.mul_le_mul_right B hcard_er
      omega
    have hsub : Finset.Ico (T0 + 1) (kmax + 1 - s p) ⊆ Finset.Ico 1 b := by
      intro d hd
      simp only [Finset.mem_Ico] at hd ⊢
      omega
    have hone : ∀ d ∈ Finset.Ico (T0 + 1) (kmax + 1 - s p),
        fStep (n % p ^ d) (p ^ d) = 1 := by
      intro d hd
      simp only [Finset.mem_Ico] at hd
      set e := d + s p
      have he_sub : e - s p = d := Nat.add_sub_cancel d (s p)
      have hpow_gt : T0 < p ^ (e - s p) := by
        rw [he_sub]
        have hd_lt : d < 2 ^ d := Nat.lt_two_pow_self
        have h2p : 2 ^ d ≤ p ^ d := Nat.pow_le_pow_left hp.two_le d
        omega
      have he_le_kmax : e ≤ kmax := by omega
      have hstep := h_step n p i0 e hp (by omega) (by omega) hpow_gt
        (pow_dvd_int_of_le_padicValNat (h_ne n i0 hi0_lt) he_le_kmax)
      rwa [he_sub] at hstep
    have hsum := sum_fStep_ge_of_subset hsub hone
    rw [Nat.card_Ico] at hsum
    have hsp1 := hs_le p
    omega

private lemma conj4 :
    ∀ r : ℕ, 0 < r → ∃ C : ℤ, 0 < C ∧
      ∀ n : ℕ, OMA.S_oeis_a211419.denominator n * OMA.S_oeis_a211419.factorsC r n ∣
        C * OMA.S_oeis_a211419.numerator n := by
  intro r hr
  simpa [OMA.S_oeis_a211419.factorsC] using
    uniform_prod_dvd r (2 * r) (12 * r) hr (by omega)
      (fun _ => 0) (fun _ => by omega) (fun _ _ => rfl)
      (fun i n => (n : ℤ) + (i : ℤ) + 1)
      (fun n i _ => by omega)
      (fun n i hi j hj hne => by omega)
      (by
        intro n p i e hp hi _ hq_gt hdvd
        simp only [Nat.sub_zero] at hq_gt ⊢
        set q := p ^ e
        have hd_nat : q ∣ n + i + 1 := by
          have : ((n + i + 1 : ℕ) : ℤ) = (n : ℤ) + (i : ℤ) + 1 := by omega
          rw [← this] at hdvd
          exact Int.natCast_dvd_natCast.mp hdvd
        have hr_lt : n % q < q := Nat.mod_lt n (by omega)
        have hd_r : q ∣ n % q + i + 1 := by
          have hdecomp : n + i + 1 = q * (n / q) + (n % q + i + 1) := by
            have := Nat.div_add_mod n q; omega
          rw [hdecomp] at hd_nat
          exact (Nat.dvd_add_right (dvd_mul_right q _)).mp hd_nat
        rcases hd_r with ⟨m, hm⟩
        have hm_pos : 1 ≤ m := by
          rcases m with _ | m
          · omega
          · omega
        have hm_lt2 : m < 2 := by nlinarith
        have hm1 : m = 1 := by omega
        subst hm1
        exact fStep_eq_one_I3 (by omega) hr_lt)

private lemma conj5 :
    ∀ r : ℕ, 0 < r → ∃ D : ℤ, 0 < D ∧
      ∀ n : ℕ, OMA.S_oeis_a211419.denominator n * OMA.S_oeis_a211419.factorsD r n ∣
        D * OMA.S_oeis_a211419.numerator n := by
  intro r hr
  simpa [OMA.S_oeis_a211419.factorsD] using
    uniform_prod_dvd r (2 * r) (12 * r) hr (by omega)
      (fun _ => 0) (fun _ => by omega) (fun _ _ => rfl)
      (fun i n => 4 * (n : ℤ) + 2 * (i : ℤ) + 1)
      (fun n i _ => by omega)
      (fun n i hi j hj hne => by omega)
      (by
        intro n p i e hp hi he_pos hq_gt hdvd
        simp only [Nat.sub_zero] at hq_gt ⊢
        set q := p ^ e
        have hd_nat : q ∣ 4 * n + 2 * i + 1 := by
          have : ((4 * n + 2 * i + 1 : ℕ) : ℤ) = 4 * (n : ℤ) + 2 * (i : ℤ) + 1 := by omega
          rw [← this] at hdvd
          exact Int.natCast_dvd_natCast.mp hdvd
        have hq_odd : q % 2 = 1 := by
          by_contra hne
          have h2q : 2 ∣ q := by omega
          have := dvd_trans h2q hd_nat
          omega
        have hr_lt : n % q < q := Nat.mod_lt n (by omega)
        have hd_r : q ∣ 4 * (n % q) + 2 * i + 1 := by
          have hdecomp : 4 * n + 2 * i + 1 = q * (4 * (n / q)) + (4 * (n % q) + 2 * i + 1) := by
            have := Nat.div_add_mod n q; linarith
          rw [hdecomp] at hd_nat
          exact (Nat.dvd_add_right (dvd_mul_right q _)).mp hd_nat
        rcases hd_r with ⟨m, hm⟩
        have hm_odd : m % 2 = 1 := by
          have hqm : (q * m) % 2 = 1 := by omega
          rw [Nat.mul_mod, hq_odd] at hqm
          omega
        have hm_lt5 : m < 5 := by nlinarith
        have hm_cases : m = 1 ∨ m = 3 := by omega
        rcases hm_cases with rfl | rfl
        · exact fStep_eq_one_I1 (by omega) (by omega)
        · exact fStep_eq_one_I2 (by omega) (by omega))

private lemma conj6 :
    ∀ r : ℕ, 0 < r → ∃ K : ℤ, 0 < K ∧
      ∀ n : ℕ, OMA.S_oeis_a211419.denominator n * OMA.S_oeis_a211419.factorsK r n ∣
        K * OMA.S_oeis_a211419.numerator n := by
  intro r hr
  simpa [OMA.S_oeis_a211419.factorsK] using
    uniform_prod_dvd r (2 * r) (12 * r) hr (by omega)
      (fun p => if p = 3 then 1 else 0)
      (fun p => by split_ifs <;> omega)
      (fun p hp => by split_ifs <;> omega)
      (fun i n => 6 * (n : ℤ) - (2 * (i : ℤ) + 1))
      (fun n i _ => by omega)
      (fun n i hi j hj hne => by omega)
      (by
        intro n p i e hp hi he_gt hq_gt hdvd
        have hp_odd : p % 2 = 1 := by
          by_contra hne
          have h2p : 2 ∣ p := by omega
          have h2pe : (2 : ℤ) ∣ ((p ^ e : ℕ) : ℤ) := by
            have : 2 ∣ p ^ e := dvd_trans h2p (dvd_pow_self p (by omega))
            exact Int.natCast_dvd_natCast.mpr this
          have h2g : (2 : ℤ) ∣ 6 * (n : ℤ) - (2 * (i : ℤ) + 1) := dvd_trans h2pe hdvd
          omega
        by_cases hp3 : p = 3
        · subst hp3
          simp only [↓reduceIte] at he_gt hq_gt ⊢
          set q := 3 ^ (e - 1)
          have h3q : 3 ^ e = 3 * q := by
            have he1 : e = (e - 1) + 1 := by omega
            conv_lhs => rw [he1, pow_succ, mul_comm]
          have h3_dvd : (3 : ℤ) ∣ 6 * (n : ℤ) - (2 * (i : ℤ) + 1) := by
            have : (3 : ℤ) ∣ ((3 ^ e : ℕ) : ℤ) := by
              rw [h3q, Nat.cast_mul]; exact dvd_mul_right 3 _
            exact dvd_trans this hdvd
          have h3_2i1 : 3 ∣ 2 * i + 1 := by
            have : (3 : ℤ) ∣ (2 * (i : ℤ) + 1) := by omega
            have : (3 : ℤ) ∣ ((2 * i + 1 : ℕ) : ℤ) := by push_cast; exact this
            exact Int.natCast_dvd_natCast.mp this
          rcases h3_2i1 with ⟨j, hj⟩
          have hd_q : (q : ℤ) ∣ 2 * (n : ℤ) - (j : ℤ) := by
            rw [h3q, Nat.cast_mul] at hdvd
            have hfact : 6 * (n : ℤ) - (2 * (i : ℤ) + 1) = 3 * (2 * (n : ℤ) - (j : ℤ)) := by
              omega
            rw [hfact] at hdvd
            exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).mp hdvd
          have hd_r : (q : ℤ) ∣ 2 * ((n % q : ℕ) : ℤ) - (j : ℤ) := by
            have hsub_z : (q : ℤ) ∣ 2 * ((n : ℤ) - ((n % q : ℕ) : ℤ)) :=
              dvd_mul_of_dvd_right (dvd_sub_mod_int n q) 2
            have hdiff := dvd_sub hd_q hsub_z
            have heq : (2 * (n : ℤ) - (j : ℤ)) - 2 * ((n : ℤ) - ((n % q : ℕ) : ℤ)) =
                2 * ((n % q : ℕ) : ℤ) - (j : ℤ) := by ring
            rwa [heq] at hdiff
          rcases hd_r with ⟨t, ht⟩
          have hr_lt : n % q < q := Nat.mod_lt n (by omega)
          have hr_lt_z : ((n % q : ℕ) : ℤ) < (q : ℤ) := Int.ofNat_lt.mpr hr_lt
          have hq_gt_z : 12 * (r : ℤ) < (q : ℤ) := by exact_mod_cast hq_gt
          have hj_z : (j : ℤ) < (r : ℤ) := by omega
          have hr_z : (0 : ℤ) < (r : ℤ) := by omega
          have hq_odd : q % 2 = 1 :=
            Nat.odd_iff.mp ((by decide : Odd 3).pow)
          have ht_ge0 : 0 ≤ t := by nlinarith
          have ht_le1 : t ≤ 1 := by nlinarith
          have ht_ne0 : t ≠ 0 := by intro h; subst h; omega
          have ht1 : t = 1 := by omega
          subst ht1
          exact fStep_eq_one_I2 (by omega) (by omega)
        · simp only [hp3, ↓reduceIte, Nat.sub_zero] at he_gt hq_gt ⊢
          set q := p ^ e
          have hq_odd : q % 2 = 1 :=
            Nat.odd_iff.mp ((Nat.odd_iff.mpr hp_odd).pow)
          have hd_r : (q : ℤ) ∣ 6 * ((n % q : ℕ) : ℤ) - (2 * (i : ℤ) + 1) := by
            have hsub_z : (q : ℤ) ∣ 6 * ((n : ℤ) - ((n % q : ℕ) : ℤ)) :=
              dvd_mul_of_dvd_right (dvd_sub_mod_int n q) 6
            have hdiff := dvd_sub hdvd hsub_z
            have heq : (6 * (n : ℤ) - (2 * (i : ℤ) + 1)) - 6 * ((n : ℤ) - ((n % q : ℕ) : ℤ)) =
                6 * ((n % q : ℕ) : ℤ) - (2 * (i : ℤ) + 1) := by ring
            rwa [heq] at hdiff
          rcases hd_r with ⟨t, ht⟩
          have hr_lt : n % q < q := Nat.mod_lt n (by omega)
          have hr_lt_z : ((n % q : ℕ) : ℤ) < (q : ℤ) := Int.ofNat_lt.mpr hr_lt
          have hq_gt_z : 12 * (r : ℤ) < (q : ℤ) := by exact_mod_cast hq_gt
          have hi_z : (i : ℤ) < (r : ℤ) := by omega
          have hr_z : (0 : ℤ) < (r : ℤ) := by omega
          have ht_ge0 : 0 ≤ t := by nlinarith
          have ht_le5 : t ≤ 5 := by nlinarith
          have ht_odd : t % 2 = 1 := by
            have hq_mod : ((q : ℤ)) % 2 = 1 := by omega
            have hprod : ((q : ℤ) * t) % 2 = 1 := by omega
            rw [Int.mul_emod, hq_mod] at hprod
            omega
          have ht_cases : t = 1 ∨ t = 3 ∨ t = 5 := by omega
          rcases ht_cases with rfl | rfl | rfl
          · exact fStep_eq_one_I1 (by omega) (by omega)
          · exact fStep_eq_one_I2 (by omega) (by omega)
          · exact fStep_eq_one_I3 (by omega) hr_lt)

end OeisA211419

theorem OMA.solution : type_of% @OMA.S_oeis_a211419.main :=
  ⟨OeisA211419.conj1, OeisA211419.conj2, OeisA211419.conj3,
   OeisA211419.conj4, OeisA211419.conj5, OeisA211419.conj6⟩
