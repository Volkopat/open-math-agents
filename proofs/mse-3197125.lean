import OMAStatements.S_mse_3197125
import Mathlib

private lemma ofDigits_eq_sum_range (b : ℕ) (l : List ℕ) :
    Nat.ofDigits b l = ∑ i ∈ Finset.range l.length, l[i]! * b ^ i := by
  induction l with
  | nil => simp [Nat.ofDigits]
  | cons d tl ih =>
    rw [Nat.ofDigits_cons, ih, Finset.mul_sum, List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem!_cons_zero, pow_zero, mul_one, List.getElem!_cons_succ, pow_succ']
    ring_nf

private lemma sum_digits_lt_pow (m : ℕ) (f : ℕ → ℕ) (hf : ∀ i < m, f i < 10) :
    ∑ i ∈ Finset.range m, f i * 10 ^ i < 10 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ']
    have h1 : ∑ i ∈ Finset.range m, f i * 10 ^ i < 10 ^ m :=
      ih fun i hi => hf i (Nat.lt_succ_of_lt hi)
    have h2 : f m < 10 := hf m (Nat.lt_succ_self m)
    nlinarith [pow_pos (by norm_num : 0 < 10) m]

private lemma digits_getElem!_lt {n i : ℕ} : (Nat.digits 10 n)[i]! < 10 := by
  by_cases hi : i < (Nat.digits 10 n).length
  · rw [getElem!_pos (Nat.digits 10 n) i hi]
    exact Nat.digits_lt_base (by norm_num) (List.getElem_mem hi)
  · rw [getElem!_neg (Nat.digits 10 n) i (by omega)]
    norm_num

private lemma pal_getElem!_symm {n i : ℕ}
    (hpal : (Nat.digits 10 n).reverse = Nat.digits 10 n)
    (hi : i < (Nat.digits 10 n).length) :
    (Nat.digits 10 n)[(Nat.digits 10 n).length - 1 - i]! = (Nat.digits 10 n)[i]! := by
  have h1 : i < (Nat.digits 10 n).reverse.length := by simpa using hi
  have h2 : (Nat.digits 10 n).length - 1 - i < (Nat.digits 10 n).length := by omega
  rw [getElem!_pos (Nat.digits 10 n) _ h2, getElem!_pos (Nat.digits 10 n) i hi]
  have hr : (Nat.digits 10 n).reverse[i] = (Nat.digits 10 n)[i] := by
    simp [hpal]
  simp only [List.getElem_reverse] at hr
  exact hr

private lemma digits_zero_getElem! {n : ℕ} (hn : n ≠ 0) :
    (Nat.digits 10 n)[0]! = n % 10 := by
  rw [Nat.digits_eq_cons_digits_div (by norm_num) hn]
  simp

private lemma div_pow_length_sub_one {n : ℕ} (hn : n ≠ 0) :
    n / 10 ^ ((Nat.digits 10 n).length - 1) =
      (Nat.digits 10 n)[(Nat.digits 10 n).length - 1]! := by
  set D := Nat.digits 10 n
  have hne : D ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hpos : 0 < D.length := List.length_pos_iff.mpr hne
  have hdrop : D.drop (D.length - 1) = [D[D.length - 1]!] := by
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 hi2
      have hi0 : i = 0 := by simp at hi2; omega
      subst hi0
      rw [List.getElem_drop, getElem!_pos D (D.length - 1) (by omega)]
      simp
  rw [Nat.self_div_pow_eq_ofDigits_drop (D.length - 1) n (by norm_num), hdrop,
    Nat.ofDigits_singleton]

private lemma pal_div_pow_eq_mod {n : ℕ} (hn : n ≠ 0)
    (hpal : (Nat.digits 10 n).reverse = Nat.digits 10 n) :
    n / 10 ^ ((Nat.digits 10 n).length - 1) = n % 10 := by
  have hne : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hpos : 0 < (Nat.digits 10 n).length := List.length_pos_iff.mpr hne
  rw [div_pow_length_sub_one hn]
  have hsym := pal_getElem!_symm hpal hpos
  simp only [Nat.sub_zero] at hsym
  rw [hsym, digits_zero_getElem! hn]

private lemma mod_pow_eq_of_zero_digits {p j : ℕ} (hp : p ≠ 0)
    (hj : 1 ≤ j) (hjL : j ≤ (Nat.digits 10 p).length)
    (hp0 : p % 10 = 3)
    (hzero : ∀ k, 1 ≤ k → k < j → (Nat.digits 10 p)[k]! = 0) :
    p % 10 ^ j = 3 := by
  rw [Nat.self_mod_pow_eq_ofDigits_take j p (by norm_num), ofDigits_eq_sum_range]
  have hlen : ((Nat.digits 10 p).take j).length = j := by simp [hjL]
  rw [hlen, Finset.sum_eq_single 0]
  · have h0 : ((Nat.digits 10 p).take j)[0]! = 3 := by
      rw [getElem!_pos ((Nat.digits 10 p).take j) 0 (by rw [hlen]; omega), List.getElem_take,
        ← getElem!_pos (Nat.digits 10 p) 0 (by omega), digits_zero_getElem! hp, hp0]
    rw [h0, pow_zero, mul_one]
  · intro k hk hne
    rw [Finset.mem_range] at hk
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hne
    have htk : ((Nat.digits 10 p).take j)[k]! = (Nat.digits 10 p)[k]! := by
      rw [getElem!_pos _ _ (by rw [hlen]; exact hk), List.getElem_take,
        getElem!_pos _ _ (by omega)]
    rw [htk, hzero k hk1 hk, zero_mul]
  · intro h0
    exfalso
    apply h0
    rw [Finset.mem_range]
    omega

private lemma digits_take_eq_nine_zeros {n j : ℕ}
    (hj : 1 ≤ j) (hjL : j ≤ (Nat.digits 10 n).length)
    (hmod : n % 10 ^ j = 9) :
    (Nat.digits 10 n).take j = 9 :: List.replicate (j - 1) 0 := by
  have h1 : Nat.ofDigits 10 ((Nat.digits 10 n).take j) =
      Nat.ofDigits 10 (9 :: List.replicate (j - 1) 0) := by
    rw [← Nat.self_mod_pow_eq_ofDigits_take j n (by norm_num), hmod,
      Nat.ofDigits_cons, Nat.ofDigits_replicate_zero, mul_zero, add_zero]
  apply Nat.ofDigits_inj_of_len_eq (b := 10) (by norm_num)
  · simp [hjL]; omega
  · intro d hd
    exact Nat.digits_lt_base (by norm_num) (List.mem_of_mem_take hd)
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · norm_num
    · rw [List.mem_replicate.mp hd |>.2]
      norm_num
  · exact h1

theorem OMA.solution : type_of% @OMA.S_mse_3197125.main := by
  intro p hp h1 hpal hpal2
  dsimp [OMA.S_mse_3197125.IsPal] at hpal hpal2
  by_cases hp10 : p < 10
  · interval_cases p <;> simp_all [Nat.Prime]
  exfalso
  push Not at hp10
  have hp0 : p ≠ 0 := by omega
  have hp2_0 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp0
  set D := Nat.digits 10 p
  have hD_len_gt : 1 < D.length := (Nat.lt_digits_length_iff (by norm_num) p).mpr (by omega)
  set L := D.length - 1
  have hL1 : 1 ≤ L := by omega
  have hD_len : D.length = L + 1 := by omega
  have h2_not_dvd : ¬ 2 ∣ p := by
    intro hd
    rcases hp.eq_one_or_self_of_dvd 2 hd with h | h <;> omega
  have h5_not_dvd : ¬ 5 ∣ p := by
    intro hd
    rcases hp.eq_one_or_self_of_dvd 5 hd with h | h <;> omega
  have hpmod_ne2 : p % 10 ≠ 0 ∧ p % 10 ≠ 2 ∧ p % 10 ≠ 4 ∧ p % 10 ≠ 5 ∧ p % 10 ≠ 6 ∧ p % 10 ≠ 8 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h
    · exact h2_not_dvd (Nat.dvd_of_mod_eq_zero (by omega))
    · exact h2_not_dvd (Nat.dvd_of_mod_eq_zero (by omega))
    · exact h2_not_dvd (Nat.dvd_of_mod_eq_zero (by omega))
    · exact h5_not_dvd (Nat.dvd_of_mod_eq_zero (by omega))
    · exact h2_not_dvd (Nat.dvd_of_mod_eq_zero (by omega))
    · exact h2_not_dvd (Nat.dvd_of_mod_eq_zero (by omega))
  have hpmod_ne1 : p % 10 ≠ 1 := by
    intro h
    apply h1
    dsimp only [D]
    rw [Nat.digits_eq_cons_digits_div (by norm_num : 1 < 10) hp0, h]
    exact List.mem_cons_self
  have hpmod_lt : p % 10 < 10 := Nat.mod_lt p (by norm_num)
  have hp_div : p / 10 ^ L = p % 10 := pal_div_pow_eq_mod hp0 hpal
  have hp_lb : (p % 10) * 10 ^ L ≤ p := by
    rw [← hp_div]
    exact Nat.div_mul_le_self p (10 ^ L)
  have hp_ub : p < (p % 10 + 1) * 10 ^ L := by
    have hlt := Nat.lt_mul_div_succ p (pow_pos (by norm_num : 0 < 10) L)
    rw [hp_div, mul_comm] at hlt
    exact hlt
  have hpow2L : (10 ^ L) ^ 2 = 10 ^ (2 * L) := by ring
  have hpmod_cases : p % 10 = 3 ∨ p % 10 = 7 ∨ p % 10 = 9 := by omega
  rcases hpmod_cases with hmod3 | hmod7 | hmod9
  · -- Case p % 10 = 3
    have hlo : 9 * 10 ^ (2 * L) ≤ p ^ 2 := by
      have : 3 * 10 ^ L ≤ p := by rwa [hmod3] at hp_lb
      nlinarith [hpow2L]
    have hhi : p ^ 2 < 16 * 10 ^ (2 * L) := by
      have : p < 4 * 10 ^ L := by rwa [hmod3] at hp_ub
      nlinarith [hpow2L]
    have hp2_mod : p ^ 2 % 10 = 9 := by
      rw [pow_two, Nat.mul_mod, hmod3]
    set D2 := Nat.digits 10 (p ^ 2)
    have hD2_gt : 2 * L < D2.length := by
      apply (Nat.lt_digits_length_iff (by norm_num) (p ^ 2)).mpr
      calc 10 ^ (2 * L) ≤ 9 * 10 ^ (2 * L) := by omega
        _ ≤ p ^ 2 := hlo
    have hD2_le : D2.length ≤ 2 * L + 2 := by
      apply (Nat.digits_length_le_iff (by norm_num) (p ^ 2)).mpr
      calc p ^ 2 < 16 * 10 ^ (2 * L) := hhi
        _ < 100 * 10 ^ (2 * L) := by nlinarith [pow_pos (by norm_num : 0 < 10) (2 * L)]
        _ = 10 ^ (2 * L + 2) := by ring
    have hD2_len : D2.length = 2 * L + 1 := by
      by_contra hne
      have hlen2 : D2.length = 2 * L + 2 := by omega
      have hdiv2 : p ^ 2 / 10 ^ (2 * L + 1) = 9 := by
        have h := pal_div_pow_eq_mod hp2_0 hpal2
        have hsub : D2.length - 1 = 2 * L + 1 := by omega
        rwa [hsub, hp2_mod] at h
      have h90 : 9 * 10 ^ (2 * L + 1) ≤ p ^ 2 := by
        rw [← hdiv2]
        exact Nat.div_mul_le_self (p ^ 2) (10 ^ (2 * L + 1))
      have h90' : 90 * 10 ^ (2 * L) ≤ p ^ 2 := by
        calc 90 * 10 ^ (2 * L) = 9 * 10 ^ (2 * L + 1) := by ring
          _ ≤ p ^ 2 := h90
      omega
    -- Examine interior digits of p
    set S := (Finset.Ico 1 L).filter (fun k => D[k]! ≠ 0)
    by_cases hS : S.Nonempty
    · set j := S.min' hS
      have hj_mem : j ∈ S := Finset.min'_mem S hS
      have hj_ico : j ∈ Finset.Ico 1 L := (Finset.mem_filter.mp hj_mem).1
      have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj_ico).1
      have hjL : j < L := (Finset.mem_Ico.mp hj_ico).2
      have hDj : D[j]! ≠ 0 := (Finset.mem_filter.mp hj_mem).2
      have h_before : ∀ k, 1 ≤ k → k < j → D[k]! = 0 := by
        intro k hk1 hkj
        by_contra hkne
        have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hk1, by omega⟩, hkne⟩
        have hle := Finset.min'_le S k hkS
        omega
      have hsym_j : D[L - j]! = D[j]! := by
        have h := pal_getElem!_symm hpal (by omega : j < D.length)
        have hsub : D.length - 1 - j = L - j := by omega
        rwa [hsub] at h
      have hDLj_ne0 : D[L - j]! ≠ 0 := by rwa [hsym_j]
      have hLj_mem : L - j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hDLj_ne0⟩
      have hj_le_Lj : j ≤ L - j := Finset.min'_le S (L - j) hLj_mem
      have hDLj_ne1 : D[L - j]! ≠ 1 := by
        intro heq
        apply h1
        rw [← heq, getElem!_pos D (L - j) (by omega)]
        exact List.getElem_mem (by omega)
      have hDLj_ge2 : 2 ≤ D[L - j]! := by omega
      have hDL_eq3 : D[L]! = 3 := by
        have h := div_pow_length_sub_one hp0
        have hsub : D.length - 1 = L := by omega
        rw [hsub] at h
        rw [← h, hp_div, hmod3]
      -- Lower bound on p: p >= 3 * 10^L + 2 * 10^(L - j)
      have hp_sum : p = ∑ i ∈ Finset.range (L + 1), D[i]! * 10 ^ i := by
        rw [← Nat.ofDigits_digits 10 p, ofDigits_eq_sum_range, hD_len]
      have hp_lb2 : 3 * 10 ^ L + 2 * 10 ^ (L - j) ≤ p := by
        rw [hp_sum]
        have hsub : ({L - j, L} : Finset ℕ) ⊆ Finset.range (L + 1) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Finset.mem_range]
          rcases hx with rfl | rfl <;> omega
        have hsum_le : ∑ i ∈ ({L - j, L} : Finset ℕ), D[i]! * 10 ^ i ≤
            ∑ i ∈ Finset.range (L + 1), D[i]! * 10 ^ i :=
          Finset.sum_le_sum_of_subset hsub
        have hne_idx : L - j ≠ L := by omega
        rw [Finset.sum_pair hne_idx, hDL_eq3] at hsum_le
        have hmul : 2 * 10 ^ (L - j) ≤ D[L - j]! * 10 ^ (L - j) :=
          Nat.mul_le_mul_right _ hDLj_ge2
        omega
      have hp2_lb2 : 9 * 10 ^ (2 * L) + 10 ^ (2 * L - j + 1) ≤ p ^ 2 := by
        have hexp : 10 ^ L * 10 ^ (L - j) = 10 ^ (2 * L - j) := by
          rw [← pow_add]
          congr 1
          omega
        have hexp2 : 10 ^ (2 * L - j + 1) = 10 * 10 ^ (2 * L - j) := by ring
        nlinarith [pow_pos (by norm_num : 0 < 10) (L - j),
          pow_pos (by norm_num : 0 < 10) (2 * L - j)]
      -- Upper bound on p^2 via digits of p^2
      have hp_modj : p % 10 ^ j = 3 :=
        mod_pow_eq_of_zero_digits hp0 hj1 (by dsimp only [D] at hD_len; omega) hmod3 h_before
      have hp2_modj : p ^ 2 % 10 ^ j = 9 := by
        rw [pow_two, Nat.mul_mod, hp_modj]
        have h10j : 10 ≤ 10 ^ j := le_self_pow₀ (by norm_num) (by omega)
        exact Nat.mod_eq_of_lt (by omega)
      have hD2_take : D2.take j = 9 :: List.replicate (j - 1) 0 :=
        digits_take_eq_nine_zeros hj1 (by dsimp only [D2] at hD2_len; omega) hp2_modj
      have hD2_zero_low : ∀ k, 1 ≤ k → k < j → D2[k]! = 0 := by
        intro k hk1 hkj
        have htk : D2[k]! = (D2.take j)[k]! := by
          rw [getElem!_pos D2 k (by omega), getElem!_pos (D2.take j) k (by simp [hD2_len]; omega),
            List.getElem_take]
        have hk_eq : k = (k - 1) + 1 := by omega
        rw [htk, hD2_take, getElem!_pos _ _ (by simp; omega)]
        conv_lhs => arg 2; rw [hk_eq]
        rw [List.getElem_cons_succ, List.getElem_replicate]
      have hD2_zero_high : ∀ i ∈ Finset.Ico (2 * L - j + 1) (2 * L), D2[i]! = 0 := by
        intro i hi
        rw [Finset.mem_Ico] at hi
        set k := 2 * L - i
        have hk1 : 1 ≤ k := by omega
        have hkj : k < j := by omega
        have hsym := pal_getElem!_symm hpal2 (by dsimp only [D2] at hD2_len; omega : k < (Nat.digits 10 (p ^ 2)).length)
        have hsub : (Nat.digits 10 (p ^ 2)).length - 1 - k = i := by
          change D2.length - 1 - k = i
          omega
        rw [hsub] at hsym
        change D2[i]! = D2[k]! at hsym
        rw [hsym, hD2_zero_low k hk1 hkj]
      have hD2_top : D2[2 * L]! = 9 := by
        have h := div_pow_length_sub_one hp2_0
        have hsub : (Nat.digits 10 (p ^ 2)).length - 1 = 2 * L := by
          change D2.length - 1 = 2 * L
          omega
        rw [hsub] at h
        have hpal2_div := pal_div_pow_eq_mod hp2_0 hpal2
        rw [hsub, hp2_mod] at hpal2_div
        change p ^ 2 / 10 ^ (2 * L) = D2[2 * L]! at h
        rw [← h, hpal2_div]
      have hp2_sum : p ^ 2 = ∑ i ∈ Finset.range (2 * L + 1), D2[i]! * 10 ^ i := by
        rw [← Nat.ofDigits_digits 10 (p ^ 2), ofDigits_eq_sum_range, hD2_len]
      have hp2_split : p ^ 2 =
          (∑ i ∈ Finset.range (2 * L - j + 1), D2[i]! * 10 ^ i) +
          (∑ i ∈ Finset.Ico (2 * L - j + 1) (2 * L), D2[i]! * 10 ^ i) +
          D2[2 * L]! * 10 ^ (2 * L) := by
        rw [hp2_sum, Finset.sum_range_succ, ← Finset.sum_range_add_sum_Ico _ (by omega : 2 * L - j + 1 ≤ 2 * L)]
      have hmid0 : ∑ i ∈ Finset.Ico (2 * L - j + 1) (2 * L), D2[i]! * 10 ^ i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hD2_zero_high i hi, zero_mul]
      have hlow_lt : ∑ i ∈ Finset.range (2 * L - j + 1), D2[i]! * 10 ^ i < 10 ^ (2 * L - j + 1) :=
        sum_digits_lt_pow (2 * L - j + 1) (fun i => D2[i]!) (fun _ _ => digits_getElem!_lt)
      rw [hmid0, add_zero, hD2_top] at hp2_split
      omega
    · -- S is empty: all interior digits are 0, so 3 ∣ p
      have h_all_zero : ∀ k, 1 ≤ k → k < L → D[k]! = 0 := by
        intro k hk1 hkL
        by_contra hne
        exact hS ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hk1, hkL⟩, hne⟩⟩
      have hp_modL : p % 10 ^ L = 3 :=
        mod_pow_eq_of_zero_digits hp0 hL1 (by dsimp only [D] at hD_len; omega) hmod3 h_all_zero
      have hp_eq : p = 3 * 10 ^ L + 3 := by
        have hdiv_mod := Nat.div_add_mod p (10 ^ L)
        rw [hp_div, hmod3, hp_modL] at hdiv_mod
        linarith
      have h3dvd : 3 ∣ p := ⟨10 ^ L + 1, by linarith⟩
      rcases hp.eq_one_or_self_of_dvd 3 h3dvd with h | h <;> omega
  · -- Case p % 10 = 7
    have hlo : 49 * 10 ^ (2 * L) ≤ p ^ 2 := by
      have : 7 * 10 ^ L ≤ p := by rwa [hmod7] at hp_lb
      nlinarith [hpow2L]
    have hhi : p ^ 2 < 64 * 10 ^ (2 * L) := by
      have : p < 8 * 10 ^ L := by rwa [hmod7] at hp_ub
      nlinarith [hpow2L]
    have hp2_mod : p ^ 2 % 10 = 9 := by
      rw [pow_two, Nat.mul_mod, hmod7]
    set D2 := Nat.digits 10 (p ^ 2)
    have hD2_gt : 2 * L + 1 < D2.length := by
      apply (Nat.lt_digits_length_iff (by norm_num) (p ^ 2)).mpr
      calc 10 ^ (2 * L + 1) = 10 * 10 ^ (2 * L) := by ring
        _ ≤ 49 * 10 ^ (2 * L) := by omega
        _ ≤ p ^ 2 := hlo
    have hD2_le : D2.length ≤ 2 * L + 2 := by
      apply (Nat.digits_length_le_iff (by norm_num) (p ^ 2)).mpr
      calc p ^ 2 < 64 * 10 ^ (2 * L) := hhi
        _ < 100 * 10 ^ (2 * L) := by nlinarith [pow_pos (by norm_num : 0 < 10) (2 * L)]
        _ = 10 ^ (2 * L + 2) := by ring
    have hD2_sub : D2.length - 1 = 2 * L + 1 := by omega
    have hdiv2 : p ^ 2 / 10 ^ (2 * L + 1) = 9 := by
      have h := pal_div_pow_eq_mod hp2_0 hpal2
      rwa [hD2_sub, hp2_mod] at h
    have h90 : 9 * 10 ^ (2 * L + 1) ≤ p ^ 2 := by
      rw [← hdiv2]
      exact Nat.div_mul_le_self (p ^ 2) (10 ^ (2 * L + 1))
    have h90' : 90 * 10 ^ (2 * L) ≤ p ^ 2 := by
      calc 90 * 10 ^ (2 * L) = 9 * 10 ^ (2 * L + 1) := by ring
        _ ≤ p ^ 2 := h90
    omega
  · -- Case p % 10 = 9
    have hlo : 81 * 10 ^ (2 * L) ≤ p ^ 2 := by
      have : 9 * 10 ^ L ≤ p := by rwa [hmod9] at hp_lb
      nlinarith [hpow2L]
    have hhi : p ^ 2 < 100 * 10 ^ (2 * L) := by
      have : p < 10 * 10 ^ L := by rwa [hmod9] at hp_ub
      nlinarith [hpow2L]
    have hp2_mod : p ^ 2 % 10 = 1 := by
      rw [pow_two, Nat.mul_mod, hmod9]
    set D2 := Nat.digits 10 (p ^ 2)
    have hD2_gt : 2 * L + 1 < D2.length := by
      apply (Nat.lt_digits_length_iff (by norm_num) (p ^ 2)).mpr
      calc 10 ^ (2 * L + 1) = 10 * 10 ^ (2 * L) := by ring
        _ ≤ 81 * 10 ^ (2 * L) := by omega
        _ ≤ p ^ 2 := hlo
    have hD2_le : D2.length ≤ 2 * L + 2 := by
      apply (Nat.digits_length_le_iff (by norm_num) (p ^ 2)).mpr
      calc p ^ 2 < 100 * 10 ^ (2 * L) := hhi
        _ = 10 ^ (2 * L + 2) := by ring
    have hD2_sub : D2.length - 1 = 2 * L + 1 := by omega
    have hdiv2 : p ^ 2 / 10 ^ (2 * L + 1) = 1 := by
      have h := pal_div_pow_eq_mod hp2_0 hpal2
      rwa [hD2_sub, hp2_mod] at h
    have hlt20 : p ^ 2 < 2 * 10 ^ (2 * L + 1) := by
      have hlt := Nat.lt_mul_div_succ (p ^ 2) (pow_pos (by norm_num : 0 < 10) (2 * L + 1))
      rw [hdiv2, mul_comm] at hlt
      exact hlt
    have hlt20' : p ^ 2 < 20 * 10 ^ (2 * L) := by
      calc p ^ 2 < 2 * 10 ^ (2 * L + 1) := hlt20
        _ = 20 * 10 ^ (2 * L) := by ring
    omega
