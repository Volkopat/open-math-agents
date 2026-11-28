import OMAStatements.S_oeis_a046699

namespace OMA.OeisA046699

open OMA.S_oeis_a046699

/-- Explicit description of the Conolly sequence. -/
def f (n : ℕ) : ℕ :=
  if h : n < 3 then (if n = 0 then 0 else 1)
  else if n = 2 ^ Nat.log 2 n then 2 ^ (Nat.log 2 n - 1)
  else 2 ^ (Nat.log 2 n - 1) + f (n - 2 ^ Nat.log 2 n + 1)
decreasing_by
  have h1 : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) (by omega)
  have h2 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h3 : 2 ^ 1 ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by norm_num) h1
  rw [pow_one] at h3
  omega

lemma f0 : f 0 = 0 := by rw [f]; simp
lemma f1 : f 1 = 1 := by rw [f]; simp
lemma f2 : f 2 = 1 := by rw [f]; simp

lemma two_pow_pred (K : ℕ) (h : 1 ≤ K) : 2 ^ K = 2 * 2 ^ (K - 1) := by
  rw [← pow_succ']; congr 1; omega

lemma f_pow (K : ℕ) (hK : 1 ≤ K) : f (2 ^ K) = 2 ^ (K - 1) := by
  rcases (show K = 1 ∨ 2 ≤ K by omega) with h | h
  · subst h; simpa using f2
  · have h4 : 2 ^ 2 ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) h
    rw [f, dif_neg (by norm_num at h4; omega)]
    simp only [Nat.log_pow (by norm_num : 1 < 2)]
    simp

lemma f_mid (K j : ℕ) (hK : 1 ≤ K) (hj1 : 1 ≤ j) (hj : j < 2 ^ K) :
    f (2 ^ K + j) = 2 ^ (K - 1) + f (j + 1) := by
  have h2 : 2 ^ 1 ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
  rw [pow_one] at h2
  have hl : Nat.log 2 (2 ^ K + j) = K :=
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by rw [pow_succ]; omega)
  rw [f, dif_neg (by omega)]
  simp only [hl]
  rw [if_neg (by omega)]
  rw [show 2 ^ K + j - 2 ^ K + 1 = j + 1 by omega]

lemma decomp (n : ℕ) (hn : 2 ≤ n) : ∃ K j, 1 ≤ K ∧ j < 2 ^ K ∧ n = 2 ^ K + j := by
  refine ⟨Nat.log 2 n, n - 2 ^ Nat.log 2 n, Nat.log_pos (by norm_num) hn, ?_, ?_⟩
  · have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    rw [Nat.succ_eq_add_one, pow_succ] at h1
    have := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    omega
  · have := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    omega

lemma f3 : f 3 = 2 := by
  have h := f_mid 1 1 le_rfl le_rfl (by norm_num)
  norm_num [f2] at h
  exact h

lemma f4 : f 4 = 2 := by
  have h := f_pow 2 (by norm_num)
  norm_num at h
  exact h

lemma f5 : f 5 = 3 := by
  have h := f_mid 2 1 (by norm_num) le_rfl (by norm_num)
  norm_num [f2] at h
  exact h

lemma f6 : f 6 = 4 := by
  have h := f_mid 2 2 (by norm_num) (by norm_num) (by norm_num)
  norm_num [f3] at h
  exact h

lemma f_bounds : ∀ n, 1 ≤ n → n ≤ 2 * f n ∧ (2 ≤ n → f n < n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases (show n = 1 ∨ 2 ≤ n by omega) with h | h
  · subst h; rw [f1]; omega
  obtain ⟨K, j, hK, hj, rfl⟩ := decomp n h
  have hP := Nat.one_le_two_pow (n := K - 1)
  have h1 := two_pow_pred K hK
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    rw [Nat.add_zero, f_pow K hK]
    omega
  · rw [f_mid K j hK h0 hj]
    obtain ⟨a1, a2⟩ := ih (j + 1) (by omega) (by omega)
    have a3 := a2 (by omega)
    omega

lemma f_le_pow : ∀ n, 1 ≤ n → ∀ K, 1 ≤ K → n ≤ 2 ^ K → f n ≤ 2 ^ (K - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn K hK hnK
  rcases (show n = 1 ∨ 2 ≤ n by omega) with h | h
  · subst h; rw [f1]; exact Nat.one_le_two_pow
  obtain ⟨L, i, hL, hi, rfl⟩ := decomp n h
  have hP := Nat.one_le_two_pow (n := L - 1)
  have h1 := two_pow_pred L hL
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    rw [Nat.add_zero, f_pow L hL]
    have hLK : L ≤ K := by
      by_contra hc
      have := Nat.pow_le_pow_right (show 2 > 0 by norm_num) (show K + 1 ≤ L by omega)
      rw [pow_succ] at this
      have := Nat.one_le_two_pow (n := K)
      omega
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [f_mid L i hL h0 hi]
    have hLK : L + 1 ≤ K := by
      by_contra hc
      have := Nat.pow_le_pow_right (show 2 > 0 by norm_num) (show K ≤ L by omega)
      omega
    have := ih (i + 1) (by omega) (by omega) L hL (by omega)
    have := Nat.pow_le_pow_right (show 2 > 0 by norm_num) (show L ≤ K - 1 by omega)
    omega

lemma f_top (K : ℕ) (hK : 1 ≤ K) : f (2 ^ K - 1) = 2 ^ (K - 1) := by
  rcases (show K = 1 ∨ 2 ≤ K by omega) with h | h
  · subst h; simpa using f1
  have h1 := two_pow_pred K (by omega)
  have h2 := two_pow_pred (K - 1) (by omega)
  have hP := Nat.one_le_two_pow (n := K - 1 - 1)
  rw [show 2 ^ K - 1 = 2 ^ (K - 1) + (2 ^ (K - 1) - 1) by omega,
    f_mid (K - 1) _ (by omega) (by omega) (by omega),
    show 2 ^ (K - 1) - 1 + 1 = 2 ^ (K - 1) by omega, f_pow (K - 1) (by omega)]
  omega

lemma f_top2 (K : ℕ) (hK : 3 ≤ K) : f (2 ^ K - 2) = 2 ^ (K - 1) := by
  have h1 := two_pow_pred K (by omega)
  have h2 := two_pow_pred (K - 1) (by omega)
  have h3 := two_pow_pred (K - 1 - 1) (by omega)
  have hP := Nat.one_le_two_pow (n := K - 1 - 1 - 1)
  rw [show 2 ^ K - 2 = 2 ^ (K - 1) + (2 ^ (K - 1) - 2) by omega,
    f_mid (K - 1) _ (by omega) (by omega) (by omega),
    show 2 ^ (K - 1) - 2 + 1 = 2 ^ (K - 1) - 1 by omega, f_top (K - 1) (by omega)]
  omega

lemma f_rec : ∀ n, 3 ≤ n → f n = f (n - f (n - 1)) + f (n - 1 - f (n - 2)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  obtain ⟨K, j, hK, hj, rfl⟩ := decomp n (by omega)
  have hP := Nat.one_le_two_pow (n := K - 1)
  have h1 := two_pow_pred K hK
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with h0 | h0 | h0 | h0
  · subst h0
    rw [Nat.add_zero] at hn ⊢
    rcases (show K = 1 ∨ K = 2 ∨ 3 ≤ K by omega) with hk | hk | hk
    · subst hk; norm_num at hn
    · subst hk; norm_num [f2, f3, f4]
    have h2 := two_pow_pred (K - 1) (by omega)
    rw [f_top K hK, f_top2 K hk, f_pow K hK,
      show 2 ^ K - 2 ^ (K - 1) = 2 ^ (K - 1) by omega,
      show 2 ^ K - 1 - 2 ^ (K - 1) = 2 ^ (K - 1) - 1 by omega,
      f_pow (K - 1) (by omega), f_top (K - 1) (by omega)]
    omega
  · subst h0
    rcases (show K = 1 ∨ 2 ≤ K by omega) with hk | hk
    · subst hk; norm_num [f1, f2, f3]
    have h2 := two_pow_pred (K - 1) (by omega)
    have hP2 := Nat.one_le_two_pow (n := K - 1 - 1)
    rw [Nat.add_sub_cancel, show 2 ^ K + 1 - 2 = 2 ^ K - 1 by omega,
      f_mid K 1 hK le_rfl (by omega), f_pow K hK, f_top K hK,
      show 2 ^ K + 1 - 2 ^ (K - 1) = 2 ^ (K - 1) + 1 by omega,
      show 2 ^ K - 2 ^ (K - 1) = 2 ^ (K - 1) by omega,
      f_mid (K - 1) 1 (by omega) le_rfl (by omega), f_pow (K - 1) (by omega)]
    omega
  · subst h0
    rcases (show K = 1 ∨ K = 2 ∨ 3 ≤ K by omega) with hk | hk | hk
    · subst hk; norm_num at hj
    · subst hk; norm_num [f3, f4, f5, f6]
    have h2 := two_pow_pred (K - 1) (by omega)
    have h3 := two_pow_pred (K - 1 - 1) (by omega)
    have hP2 := Nat.one_le_two_pow (n := K - 1 - 1 - 1)
    rw [show 2 ^ K + 2 - 1 = 2 ^ K + 1 by omega, Nat.add_sub_cancel,
      f_mid K 2 hK (by omega) (by omega), f_mid K 1 hK le_rfl (by omega), f_pow K hK,
      show (1 : ℕ) + 1 = 2 from rfl, show (2 : ℕ) + 1 = 3 from rfl, f2, f3,
      show 2 ^ K + 2 - (2 ^ (K - 1) + 1) = 2 ^ (K - 1) + 1 by omega,
      show 2 ^ K + 1 - 2 ^ (K - 1) = 2 ^ (K - 1) + 1 by omega,
      f_mid (K - 1) 1 (by omega) le_rfl (by omega), show (1 : ℕ) + 1 = 2 from rfl, f2]
    omega
  · have hk : 2 ≤ K := by
      rcases (show K = 1 ∨ 2 ≤ K by omega) with hk | hk
      · subst hk
        have : (2 : ℕ) ^ 1 = 2 := by norm_num
        omega
      · exact hk
    have h2 := two_pow_pred (K - 1) (by omega)
    have hb1 := f_bounds j (by omega)
    have hb2 := f_bounds (j - 1) (by omega)
    have hb1' := hb1.2 (by omega)
    have hb2' := hb2.2 (by omega)
    have hb1l := hb1.1
    have hb2l := hb2.1
    clear hb1 hb2
    rw [show 2 ^ K + j - 1 = 2 ^ K + (j - 1) by omega,
      show 2 ^ K + j - 2 = 2 ^ K + (j - 2) by omega,
      f_mid K j hK (by omega) hj, f_mid K (j - 1) hK (by omega) (by omega),
      f_mid K (j - 2) hK (by omega) (by omega),
      show j - 1 + 1 = j by omega, show j - 2 + 1 = j - 1 by omega,
      show 2 ^ K + j - (2 ^ (K - 1) + f j) = 2 ^ (K - 1) + (j - f j) by omega,
      show 2 ^ K + (j - 1) - (2 ^ (K - 1) + f (j - 1))
        = 2 ^ (K - 1) + (j - 1 - f (j - 1)) by omega,
      f_mid (K - 1) (j - f j) (by omega) (by omega) (by omega),
      f_mid (K - 1) (j - 1 - f (j - 1)) (by omega) (by omega) (by omega)]
    have hr := ih (j + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel, show j + 1 - 2 = j - 1 by omega,
      show j + 1 - f j = j - f j + 1 by omega,
      show j - f (j - 1) = j - 1 - f (j - 1) + 1 by omega] at hr
    omega

/-! ### The word `b` -/

lemma len_str (k : ℕ) : (str k).length + 1 = 3 * 2 ^ k := by
  induction k with
  | zero => simp [str]
  | succ k ih =>
    simp only [str, List.length_append, List.length_singleton]
    rw [pow_succ]
    omega

lemma getD_succ (k i : ℕ) (h : i < (str k).length) :
    (str (k + 1)).getD i 0 = (str k).getD i 0 := by
  rw [str, List.append_assoc, List.getD_append _ _ _ _ h]

lemma getD_mono (k i : ℕ) (h : i < (str k).length) :
    ∀ k', k ≤ k' → (str k').getD i 0 = (str k).getD i 0 := by
  intro k' hk
  induction k', hk using Nat.le_induction with
  | base => rfl
  | succ m hm ihm =>
    have : (str k).length ≤ (str m).length := by
      have := len_str k
      have := len_str m
      have := Nat.pow_le_pow_right (show 2 > 0 by norm_num) hm
      omega
    rw [getD_succ m i (by omega), ihm]

lemma lt_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

lemma b_eq (k i : ℕ) (h : i < (str k).length) : b i = (str k).getD i 0 := by
  unfold b
  rcases Nat.le_total i k with hik | hik
  · have hi : i < (str i).length := by
      have := len_str i
      have := lt_pow i
      omega
    rw [getD_mono i i hi k hik]
  · exact getD_mono k i h i hik

lemma b_shift (k t : ℕ) (ht : t < (str k).length) : b ((str k).length + t) = b t := by
  have hl : ((str (k + 1)).length) = (str k).length + (str k).length + 1 := by
    simp [str]; omega
  rw [b_eq (k + 1) _ (by omega), b_eq k t ht, str, List.append_assoc,
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ ht]

lemma b_two (k : ℕ) : b (2 * (str k).length) = 0 := by
  have hl : ((str (k + 1)).length) = (str k).length + (str k).length + 1 := by
    simp [str]; omega
  rw [b_eq (k + 1) _ (by omega), str, List.append_assoc,
    List.getD_append_right _ _ _ _ (by omega),
    List.getD_append_right _ _ _ _ (by omega)]
  rw [show 2 * (str k).length - (str k).length - (str k).length = 0 by omega]
  rfl

lemma b0 : b 0 = 0 := by decide
lemma b1 : b 1 = 1 := by decide
lemma b2 : b 2 = 0 := by decide
lemma b3 : b 3 = 1 := by decide

lemma f_b : ∀ n, 1 ≤ n → f (n + 1) = f n + b (f n + n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases (show n = 1 ∨ 2 ≤ n by omega) with h | h
  · subst h; rw [f2, f1, b2]
  obtain ⟨K, j, hK, hj, rfl⟩ := decomp n h
  have hP := Nat.one_le_two_pow (n := K - 1)
  have h1 := two_pow_pred K hK
  have hLk := len_str (K - 1)
  rcases (show j = 0 ∨ (1 ≤ j ∧ j + 2 < 2 ^ K) ∨ (1 ≤ j ∧ j + 2 = 2 ^ K) ∨ j + 1 = 2 ^ K
    by omega) with h0 | ⟨h0, h0'⟩ | ⟨h0, h0'⟩ | h0
  · subst h0
    simp only [Nat.add_zero]
    rw [f_mid K 1 hK le_rfl (by omega), f_pow K hK, show (1 : ℕ) + 1 = 2 from rfl, f2,
      show 2 ^ (K - 1) + 2 ^ K = (str (K - 1)).length + 1 by omega,
      b_shift (K - 1) 1 (by omega), b1]
  · rw [show 2 ^ K + j + 1 = 2 ^ K + (j + 1) by omega,
      f_mid K (j + 1) hK (by omega) (by omega), f_mid K j hK h0 hj]
    have hle := f_le_pow (j + 1) (by omega) K hK (by omega)
    rw [show 2 ^ (K - 1) + f (j + 1) + (2 ^ K + j)
        = (str (K - 1)).length + (f (j + 1) + (j + 1)) by omega,
      b_shift (K - 1) _ (by omega), ih (j + 1) (by omega) (by omega)]
    omega
  · have hj1 : j + 1 = 2 ^ K - 1 := by omega
    rw [show 2 ^ K + j + 1 = 2 ^ K + (j + 1) by omega,
      f_mid K (j + 1) hK (by omega) (by omega), f_mid K j hK h0 hj,
      show j + 1 + 1 = 2 ^ K by omega, hj1, f_pow K hK, f_top K hK,
      show 2 ^ (K - 1) + 2 ^ (K - 1) + (2 ^ K + j) = 2 * (str (K - 1)).length by omega,
      b_two]
    omega
  · have hj1 : 1 ≤ j := by omega
    have hLK := len_str K
    have e : 2 ^ K + j + 1 = 2 ^ (K + 1) := by rw [pow_succ]; omega
    rw [e, f_pow (K + 1) (by omega), f_mid K j hK hj1 hj, h0, f_pow K hK,
      Nat.add_sub_cancel,
      show 2 ^ (K - 1) + 2 ^ (K - 1) + (2 ^ K + j) = (str K).length + 0 by omega,
      b_shift K 0 (by omega), b0]
    omega

lemma prefix_eq : ∀ k, (prefixA k).length = k + 3 ∧
    ∀ i, i < k + 3 → (prefixA k).getD i 0 = f i := by
  intro k
  induction k with
  | zero =>
    refine ⟨rfl, ?_⟩
    intro i hi
    interval_cases i
    · rw [f0]; rfl
    · rw [f1]; rfl
    · rw [f2]; rfl
  | succ k ih =>
    obtain ⟨hlen, hget⟩ := ih
    have hb1 := (f_bounds (k + 2) (by omega)).1
    refine ⟨?_, ?_⟩
    · simp [prefixA, hlen]
    intro i hi
    simp only [prefixA]
    rcases (show i < k + 3 ∨ i = k + 3 by omega) with h | h
    · rw [List.getD_append _ _ _ _ (by omega), hget i h]
    · subst h
      rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
      rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
        hget (k + 2) (by omega), hget (k + 1) (by omega),
        hget _ (by omega), hget _ (by omega)]
      have hr := f_rec (k + 3) (by omega)
      rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega] at hr
      rw [hr, List.getD_cons_zero]

end OMA.OeisA046699

theorem OMA.solution : type_of% @OMA.S_oeis_a046699.main := by
  intro n hn
  have ha : ∀ m, OMA.S_oeis_a046699.a m = OMA.OeisA046699.f m :=
    fun m => (OMA.OeisA046699.prefix_eq m).2 m (by omega)
  rw [ha, ha]
  exact OMA.OeisA046699.f_b n hn
