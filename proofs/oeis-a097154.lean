import OMAStatements.S_oeis_a097154

-- Proof of oeis-a097154
-- Credit: @lettucrisp

namespace OeisA097154

open OMA.S_oeis_a097154

private lemma foldr_max_le : ∀ (L : List ℕ) (M : ℕ), (∀ d ∈ L, d ≤ M) → L.foldr max 0 ≤ M
  | [], _, _ => Nat.zero_le _
  | d :: t, M, h => by
    simp only [List.foldr_cons]
    exact max_le (h d (List.mem_cons_self ..)) (foldr_max_le t M (fun x hx => h x (List.mem_cons_of_mem d hx)))

private lemma maxDigit_le_nine (x : ℕ) : maxDigit x ≤ 9 := by
  unfold maxDigit
  refine foldr_max_le _ 9 fun d hd => ?_
  have hlt : d < 10 := Nat.digits_lt_base (by norm_num) hd
  omega

private lemma foldr_max_eq_zero : ∀ (L : List ℕ), L.foldr max 0 = 0 → ∀ d ∈ L, d = 0
  | [], _, _, h => nomatch h
  | d :: t, h, x, hx => by
    simp only [List.foldr_cons, Nat.max_eq_zero_iff] at h
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact h.1
    · exact foldr_max_eq_zero t h.2 x hx'

private lemma ofDigits_eq_zero : ∀ (L : List ℕ), (∀ d ∈ L, d = 0) → Nat.ofDigits 10 L = 0
  | [], _ => rfl
  | d :: t, h => by
    simp [Nat.ofDigits_cons, h d (List.mem_cons_self ..),
      ofDigits_eq_zero t (fun x hx => h x (List.mem_cons_of_mem d hx))]

private lemma maxDigit_pos {x : ℕ} (hx : x ≠ 0) : 1 ≤ maxDigit x := by
  by_contra h
  have h0 : maxDigit x = 0 := by omega
  have hall : ∀ d ∈ Nat.digits 10 x, d = 0 := foldr_max_eq_zero _ h0
  have hx0 : x = 0 := by
    rw [← Nat.ofDigits_digits 10 x]
    exact ofDigits_eq_zero _ hall
  exact hx hx0

private lemma ofDigits_mod_nine : ∀ L : List ℕ, Nat.ofDigits 10 L % 9 = L.sum % 9
  | [] => rfl
  | d :: t => by
    rw [Nat.ofDigits_cons, List.sum_cons]
    have ih := ofDigits_mod_nine t
    omega

private lemma reverse_mod_nine (x : ℕ) : reverse x % 9 = x % 9 := by
  unfold reverse
  rw [ofDigits_mod_nine, List.sum_reverse, ← ofDigits_mod_nine, Nat.ofDigits_digits]

private lemma ofDigits_append (L1 L2 : List ℕ) :
    Nat.ofDigits 10 (L1 ++ L2) = Nat.ofDigits 10 L1 + 10 ^ L1.length * Nat.ofDigits 10 L2 := by
  induction L1 with
  | nil => simp [Nat.ofDigits]
  | cons d t ih =>
    simp only [List.cons_append, Nat.ofDigits_cons, List.length_cons, ih]
    ring

private lemma ofDigits_lt_pow : ∀ L : List ℕ, (∀ d ∈ L, d < 10) → Nat.ofDigits 10 L < 10 ^ L.length
  | [], _ => by simp [Nat.ofDigits]
  | d :: t, h => by
    simp only [Nat.ofDigits_cons, List.length_cons]
    have hd : d < 10 := h d (List.mem_cons_self ..)
    have ih := ofDigits_lt_pow t (fun x hx => h x (List.mem_cons_of_mem d hx))
    have hpow : 10 ^ (t.length + 1) = 10 * 10 ^ t.length := by ring
    omega

private lemma small_fixed : ∀ x < 100, maxDigit x = 9 → reverse x = x + 9 → x = 89 := by
  decide

private lemma no_large_fixed {x : ℕ} (hx : 100 ≤ x) (hrev : reverse x = x + 9) : False := by
  have hx0 : x ≠ 0 := by omega
  set L := Nat.digits 10 x
  have hL_lt : ∀ d ∈ L, d < 10 := fun d hd => Nat.digits_lt_base (by norm_num) hd
  have hofL : Nat.ofDigits 10 L = x := Nat.ofDigits_digits 10 x
  have hL_len : 3 ≤ L.length := by
    by_contra hlt
    have h1 : x < 10 ^ L.length := by rw [← hofL]; exact ofDigits_lt_pow L hL_lt
    have h2 : L.length ≤ 2 := by omega
    have h3 : 10 ^ L.length ≤ 10 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
    omega
  -- Split L = d0 :: d1 :: R with R nonempty and last element a
  cases hL0 : L with
  | nil => rw [hL0] at hL_len; simp at hL_len
  | cons d0 L1 =>
    cases hL1 : L1 with
    | nil => rw [hL0, hL1] at hL_len; simp at hL_len
    | cons d1 R =>
      have hR_ne : R ≠ [] := by
        intro hnil
        rw [hL0, hL1, hnil] at hL_len
        simp at hL_len
      have hR_split : R = R.dropLast ++ [R.getLast hR_ne] := (List.dropLast_append_getLast hR_ne).symm
      set M := R.dropLast
      set a := R.getLast hR_ne
      set k := M.length
      have hL_eq : L = d0 :: d1 :: (M ++ [a]) := by rw [hL0, hL1, hR_split]
      have hd0 : d0 < 10 := hL_lt d0 (by rw [hL_eq]; simp)
      have hd1 : d1 < 10 := hL_lt d1 (by rw [hL_eq]; simp)
      have ha_lt : a < 10 := hL_lt a (by rw [hL_eq]; simp)
      have hM_lt : ∀ d ∈ M, d < 10 := fun d hd => hL_lt d (by rw [hL_eq]; simp [hd])
      -- Last digit of digits 10 x is nonzero
      have hL_ne : L ≠ [] := by rw [hL_eq]; simp
      have ha_pos : 1 ≤ a := by
        have hlast := Nat.getLast_digit_ne_zero 10 hx0
        have heq_last : L.getLast hL_ne = a := by
          simp [hL_eq]
        have : a ≠ 0 := by rw [← heq_last]; exact hlast
        omega
      -- Express x in terms of d0, d1, M, a
      have hx_decomp : x = d0 + 10 * d1 + 100 * Nat.ofDigits 10 M + 100 * 10 ^ k * a := by
        rw [← hofL, hL_eq, Nat.ofDigits_cons, Nat.ofDigits_cons, ofDigits_append]
        simp [Nat.ofDigits]
        ring
      have hM_bound : Nat.ofDigits 10 M < 10 ^ k := ofDigits_lt_pow M hM_lt
      have hx_upper : x < (a + 1) * (100 * 10 ^ k) := by
        have h1 : d0 + 10 * d1 < 100 := by omega
        have h2 : 100 * Nat.ofDigits 10 M + 100 ≤ 100 * 10 ^ k := by omega
        nlinarith
      -- Express reverse x
      have hLrev : L.reverse = a :: (M.reverse ++ [d1, d0]) := by
        rw [hL_eq]
        simp [List.reverse_append, List.append_assoc]
      have hrev_decomp : reverse x =
          a + 10 * Nat.ofDigits 10 M.reverse + 10 * 10 ^ k * d1 + 100 * 10 ^ k * d0 := by
        unfold reverse
        change Nat.ofDigits 10 L.reverse = _
        rw [hLrev, Nat.ofDigits_cons, ofDigits_append]
        simp [Nat.ofDigits, List.length_reverse]
        ring
      -- Step A: Compare mod 10 to determine d0
      have hrev_mod10 : reverse x % 10 = a := by
        rw [hrev_decomp]
        have : a + 10 * Nat.ofDigits 10 M.reverse + 10 * 10 ^ k * d1 + 100 * 10 ^ k * d0 =
            a + 10 * (Nat.ofDigits 10 M.reverse + 10 ^ k * d1 + 10 * 10 ^ k * d0) := by ring
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha_lt]
      have hx_mod10 : x % 10 = d0 := by
        rw [hx_decomp]
        have : d0 + 10 * d1 + 100 * Nat.ofDigits 10 M + 100 * 10 ^ k * a =
            d0 + 10 * (d1 + 10 * Nat.ofDigits 10 M + 10 * 10 ^ k * a) := by ring
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd0]
      have hd0_pos : 1 ≤ d0 := by
        by_contra h0
        have hd00 : d0 = 0 := by omega
        have hMr_lt : Nat.ofDigits 10 M.reverse < 10 ^ k := by
          have := ofDigits_lt_pow M.reverse (fun d hd => hM_lt d (List.mem_reverse.mp hd))
          simpa using this
        have hrev_lt : reverse x < 100 * 10 ^ k := by
          rw [hrev_decomp, hd00]
          have h10k : 1 ≤ 10 ^ k := Nat.one_le_pow k 10 (by norm_num)
          nlinarith
        have hx_ge : 100 * 10 ^ k ≤ x := by
          have h1 : 100 * 10 ^ k * 1 ≤ 100 * 10 ^ k * a := Nat.mul_le_mul_left _ ha_pos
          rw [hx_decomp]; omega
        omega
      have hd0_eq : d0 = a + 1 := by
        have h1 : (x + 9) % 10 = (d0 + 9) % 10 := by rw [Nat.add_mod, hx_mod10]
        have h2 : a = (d0 + 9) % 10 := by rw [← hrev_mod10, hrev, h1]
        omega
      -- Step B: Size comparison forces d1 = 0 AND x % 100 ≥ 91 forces d1 = 9, contradiction!
      have h10k : 1 ≤ 10 ^ k := Nat.one_le_pow k 10 (by norm_num)
      have hrev_ge : (a + 1) * (100 * 10 ^ k) + 10 * 10 ^ k * d1 ≤ reverse x := by
        rw [hrev_decomp, hd0_eq]
        have hcomm : 100 * 10 ^ k * (a + 1) = (a + 1) * (100 * 10 ^ k) := by ring
        omega
      have hd1_zero : d1 = 0 := by
        by_contra hne
        have hd1_ge1 : 1 ≤ d1 := by omega
        have : (a + 1) * (100 * 10 ^ k) + 10 ≤ reverse x := by nlinarith
        omega
      have hx_lower : (a + 1) * (100 * 10 ^ k) ≤ x + 9 := by nlinarith
      have hx_mod100 : x % 100 = d0 + 10 * d1 := by
        rw [hx_decomp]
        have : d0 + 10 * d1 + 100 * Nat.ofDigits 10 M + 100 * 10 ^ k * a =
            (d0 + 10 * d1) + 100 * (Nat.ofDigits 10 M + 10 ^ k * a) := by ring
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      have h100_dvd : 100 ∣ (a + 1) * (100 * 10 ^ k) := ⟨(a + 1) * 10 ^ k, by ring⟩
      rcases h100_dvd with ⟨Q, hQ⟩
      rw [hQ] at hx_lower hx_upper
      have hx_rem : x % 100 ≥ 91 := by omega
      rw [hx_mod100, hd1_zero] at hx_rem
      omega

private lemma main_proof : {x : ℕ | f x = x} = {0, 89} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hfx
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      have hmd_pos : 1 ≤ maxDigit x := maxDigit_pos hx0
      have hmd_le : maxDigit x ≤ 9 := maxDigit_le_nine x
      have hrev_ge : maxDigit x ≤ reverse x := by
        by_contra hlt
        have hzero : reverse x - maxDigit x = 0 := Nat.sub_eq_zero_of_le (by omega)
        change reverse x - maxDigit x = x at hfx
        omega
      have hrev_eq : reverse x = x + maxDigit x := by
        change reverse x - maxDigit x = x at hfx
        omega
      have hmod9 : (x + maxDigit x) % 9 = x % 9 := by
        rw [← hrev_eq, reverse_mod_nine]
      have hmd9 : maxDigit x = 9 := by omega
      rw [hmd9] at hrev_eq
      by_cases hlt : x < 100
      · exact small_fixed x hlt hmd9 hrev_eq
      · exact (no_large_fixed (by omega) hrev_eq).elim
  · rintro (rfl | rfl) <;> decide

end OeisA097154

theorem OMA.solution : type_of% @OMA.S_oeis_a097154.main :=
  OeisA097154.main_proof
