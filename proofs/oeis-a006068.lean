import OMAStatements.S_oeis_a006068

namespace OMA.P_oeis_a006068

open OMA.S_oeis_a006068

private def prefXor (M n : ℕ) : ℕ :=
  (List.range M).foldl (fun acc k => acc ^^^ (n >>> k)) 0

private lemma prefXor_zero (n : ℕ) : prefXor 0 n = 0 := rfl

private lemma prefXor_succ (M n : ℕ) :
    prefXor (M + 1) n = prefXor M n ^^^ (n >>> M) := by
  simp [prefXor, List.range_succ]

private lemma prefXor_zero_right (M : ℕ) : prefXor M 0 = 0 := by
  induction M with
  | zero => rfl
  | succ M ih => simp [prefXor_succ, ih]

private lemma prefXor_succ_shift (M n : ℕ) :
    prefXor (M + 1) n = n ^^^ prefXor M (n >>> 1) := by
  induction M with
  | zero =>
    simp [prefXor]
  | succ M ih =>
    rw [prefXor_succ, ih, prefXor_succ, Nat.xor_assoc]
    congr 1
    congr 1
    rw [Nat.add_comm M 1, Nat.shiftRight_add]

private lemma prefXor_eq_of_lt {M M' n : ℕ} (hM : M ≤ M') (hn : n < 2 ^ M) :
    prefXor M' n = prefXor M n := by
  induction hM with
  | refl => rfl
  | @step m hm ih =>
    rw [prefXor_succ, ih]
    have hlt : n < 2 ^ m := lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) hm)
    have hshr : n >>> m = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt hlt
    simp [hshr]

private lemma a_eq_prefXor {M n : ℕ} (hn : n < 2 ^ M) : a n = prefXor M n := by
  change prefXor (Nat.log 2 n + 1) n = prefXor M n
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [prefXor_zero_right]
  · have hle : Nat.log 2 n + 1 ≤ M := by
      have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (Nat.ne_of_gt hpos)
      have h2 : 2 ^ Nat.log 2 n < 2 ^ M := lt_of_le_of_lt h1 hn
      have h3 : Nat.log 2 n < M := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
      omega
    have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    exact (prefXor_eq_of_lt hle hlt).symm

private lemma shiftRight_xor_distrib (x y k : ℕ) :
    (x ^^^ y) >>> k = (x >>> k) ^^^ (y >>> k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_shiftRight, Nat.testBit_xor]

private lemma prefXor_xor (M x y : ℕ) :
    prefXor M (x ^^^ y) = prefXor M x ^^^ prefXor M y := by
  induction M with
  | zero => simp [prefXor_zero]
  | succ M ih =>
    rw [prefXor_succ, prefXor_succ, prefXor_succ, ih, shiftRight_xor_distrib]
    simp only [Nat.xor_assoc]
    congr 1
    rw [← Nat.xor_assoc (prefXor M y), Nat.xor_comm (prefXor M y) (x >>> M), Nat.xor_assoc]

private lemma prefXor_lt_two_pow (M : ℕ) {x k : ℕ} (hx : x < 2 ^ k) :
    prefXor M x < 2 ^ k := by
  induction M with
  | zero =>
    rw [prefXor_zero]
    exact Nat.two_pow_pos k
  | succ M ih =>
    rw [prefXor_succ]
    apply Nat.xor_lt_two_pow ih
    rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self x (2 ^ M)) hx

private lemma prefXor_gray_two_pow (k : ℕ) :
    prefXor (k + 2) (2 ^ (k + 1) ^^^ 2 ^ k) = 2 ^ (k + 1) := by
  rw [prefXor_xor, prefXor_succ_shift]
  have hshr : 2 ^ (k + 1) >>> 1 = 2 ^ k := by
    rw [Nat.shiftRight_eq_div_pow, pow_one, pow_succ]
    exact Nat.mul_div_cancel _ (by norm_num)
  rw [hshr]
  have heq : prefXor (k + 2) (2 ^ k) = prefXor (k + 1) (2 ^ k) :=
    prefXor_eq_of_lt (Nat.le_succ _) (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k))
  rw [heq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

private lemma add_two_pow_eq_xor {x k : ℕ} (hx : x < 2 ^ k) :
    x + 2 ^ k = x ^^^ 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_eq_decide_div_mod_eq,
      Nat.testBit_eq_decide_div_mod_eq]
  by_cases hi : i < k
  · have hne : k ≠ i := Nat.ne_of_gt hi
    have hpow : 2 ^ k = 2 ^ i * 2 ^ (k - i) := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hi)]
    have hdiv : (x + 2 ^ k) / 2 ^ i = x / 2 ^ i + 2 ^ (k - i) := by
      rw [hpow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i)]
    have heven : 2 ^ (k - i) % 2 = 0 := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt hi)
      rw [hd, pow_succ]
      omega
    simp [hne, hdiv, Nat.add_mod, heven]
  · by_cases heq : i = k
    · subst heq
      have hdiv0 : x / 2 ^ i = 0 := Nat.div_eq_of_lt hx
      have hdiv1 : (x + 2 ^ i) / 2 ^ i = 1 := by
        rw [Nat.add_div_right _ (Nat.two_pow_pos i), hdiv0]
      simp [hdiv0, hdiv1]
    · have hgt : k < i := by omega
      have hne : k ≠ i := Nat.ne_of_lt hgt
      have h1 : x < 2 ^ i := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h2 : x + 2 ^ k < 2 ^ i := by
        have h3 : 2 ^ (k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h4 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
        omega
      simp [hne, Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h2]

private lemma main_proof : ∀ n : ℕ, 0 < n → a n = a (A053645 (A063946 n)) + A053644 n := by
  intro n hn
  by_cases hlt2 : n < 2
  · have hn1 : n = 1 := by omega
    subst hn1
    decide
  · have hge2 : 2 ≤ n := by omega
    have hlog_pos : 0 < Nat.log 2 n := by
      have : 1 ≤ Nat.log 2 n := by
        rw [← Nat.log_pow (by norm_num : 1 < 2) 1]
        exact Nat.log_mono_right (by simpa using hge2)
      omega
    set k := Nat.log 2 n - 1
    have hk : Nat.log 2 n = k + 1 := by omega
    have hn_lo : 2 ^ (k + 1) ≤ n := by
      rw [← hk]
      exact Nat.pow_log_le_self 2 (by omega)
    have hn_hi : n < 2 ^ (k + 2) := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
      rw [hk] at this
      exact this
    have hA6 : A063946 n = n ^^^ 2 ^ k := by
      unfold A063946
      rw [if_neg hlt2, hk]
      simp
    set y := n ^^^ 2 ^ k
    have hy_hi : y < 2 ^ (k + 2) :=
      Nat.xor_lt_two_pow hn_hi (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hn_bit : n.testBit (k + 1) = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : n / 2 ^ (k + 1) = 1 := by
        have h1 : 1 ≤ n / 2 ^ (k + 1) := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by simpa using hn_lo)
        have h2 : n / 2 ^ (k + 1) < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by
          have : 2 * 2 ^ (k + 1) = 2 ^ (k + 2) := by ring
          omega)
        omega
      simp [hdiv]
    have hy_bit : y.testBit (k + 1) = true := by
      simp [y, Nat.testBit_xor, hn_bit]
    have hy_lo : 2 ^ (k + 1) ≤ y := by
      by_contra hlt
      have hlt' : y < 2 ^ (k + 1) := by omega
      have : y.testBit (k + 1) = false := Nat.testBit_eq_false_of_lt hlt'
      rw [this] at hy_bit
      exact Bool.false_ne_true hy_bit
    have hy_ne : y ≠ 0 := by
      have := Nat.two_pow_pos (k + 1)
      omega
    have hy_log : Nat.log 2 y = k + 1 :=
      (Nat.log_eq_iff (Or.inr ⟨by norm_num, hy_ne⟩)).mpr ⟨hy_lo, hy_hi⟩
    have hA4_y : A053644 y = 2 ^ (k + 1) := by
      unfold A053644
      rw [if_neg hy_ne, hy_log]
    have hA4_n : A053644 n = 2 ^ (k + 1) := by
      unfold A053644
      rw [if_neg (by omega), hk]
    set m := y - 2 ^ (k + 1)
    have hA5 : A053645 (A063946 n) = m := by
      rw [hA6]
      unfold A053645
      rw [hA4_y]
    have hm_lt : m < 2 ^ (k + 1) := by
      have : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      omega
    have hm_add : m + 2 ^ (k + 1) = y := Nat.sub_add_cancel hy_lo
    have hm_xor : m ^^^ 2 ^ (k + 1) = y := by
      rw [← add_two_pow_eq_xor hm_lt, hm_add]
    have hn_eq : n = m ^^^ (2 ^ (k + 1) ^^^ 2 ^ k) := by
      calc n = (n ^^^ 2 ^ k) ^^^ 2 ^ k := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        _ = y ^^^ 2 ^ k := rfl
        _ = (m ^^^ 2 ^ (k + 1)) ^^^ 2 ^ k := by rw [hm_xor]
        _ = m ^^^ (2 ^ (k + 1) ^^^ 2 ^ k) := Nat.xor_assoc _ _ _
    have hm_lt2 : m < 2 ^ (k + 2) :=
      lt_trans hm_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _))
    have ham_lt : a m < 2 ^ (k + 1) := by
      rw [a_eq_prefXor hm_lt2]
      exact prefXor_lt_two_pow (k + 2) hm_lt
    rw [hA5, hA4_n]
    calc a n = prefXor (k + 2) n := a_eq_prefXor hn_hi
      _ = prefXor (k + 2) (m ^^^ (2 ^ (k + 1) ^^^ 2 ^ k)) := by rw [hn_eq]
      _ = prefXor (k + 2) m ^^^ prefXor (k + 2) (2 ^ (k + 1) ^^^ 2 ^ k) := prefXor_xor _ _ _
      _ = a m ^^^ 2 ^ (k + 1) := by rw [← a_eq_prefXor hm_lt2, prefXor_gray_two_pow]
      _ = a m + 2 ^ (k + 1) := (add_two_pow_eq_xor ham_lt).symm

end OMA.P_oeis_a006068

theorem OMA.solution : type_of% @OMA.S_oeis_a006068.main :=
  OMA.P_oeis_a006068.main_proof
