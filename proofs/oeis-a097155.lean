import OMAStatements.S_oeis_a097155

namespace OMA.P_oeis_a097155

lemma le_foldr_max (L : List ℕ) : ∀ d ∈ L, d ≤ L.foldr max 0 := by
  induction L with
  | nil => simp
  | cons h t ih =>
    intro d hd
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hd with rfl | hd
    · exact le_max_left _ _
    · exact le_trans (ih d hd) (le_max_right _ _)

lemma foldr_max_le (L : List ℕ) (hL : ∀ d ∈ L, d < 10) : L.foldr max 0 ≤ 9 := by
  induction L with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldr_cons]
    have h1 := hL h (by simp)
    have h2 := ih (fun d hd => hL d (by simp [hd]))
    omega

lemma ofDigits_eq_zero (L : List ℕ) (h : Nat.ofDigits 10 L = 0) : ∀ d ∈ L, d = 0 := by
  induction L with
  | nil => simp
  | cons hd t ih =>
    rw [Nat.ofDigits_cons] at h
    intro d hdm
    rcases List.mem_cons.mp hdm with rfl | hdm
    · omega
    · exact ih (by omega) d hdm

lemma ofDigits_zeros (L : List ℕ) (h : ∀ d ∈ L, d = 0) : Nat.ofDigits 10 L = 0 := by
  induction L with
  | nil => simp
  | cons hd t ih =>
    rw [Nat.ofDigits_cons, h hd (by simp), ih (fun d hdm => h d (by simp [hdm]))]

lemma rev_modEq (x : ℕ) : OMA.S_oeis_a097155.rev x ≡ x [MOD 9] := by
  unfold OMA.S_oeis_a097155.rev
  have h1 := Nat.ofDigits_modEq 10 9 (Nat.digits 10 x).reverse
  have h2 := Nat.ofDigits_modEq 10 9 (Nat.digits 10 x)
  rw [Nat.ofDigits_digits] at h2
  norm_num [Nat.ofDigits_one, List.sum_reverse] at h1 h2
  exact h1.trans h2.symm

end OMA.P_oeis_a097155

open OMA.P_oeis_a097155 in
theorem OMA.solution : type_of% @OMA.S_oeis_a097155.main := by
  intro x
  constructor
  swap
  · rintro (rfl | rfl) <;> decide
  intro hfx
  rcases Nat.eq_zero_or_pos x with hx0 | hxpos
  · exact Or.inl hx0
  right
  unfold OMA.S_oeis_a097155.f at hfx
  set L := Nat.digits 10 x with hL
  have hdig : ∀ d ∈ L, d < 10 := fun d hd => Nat.digits_lt_base (by norm_num) hd
  have hm9 : OMA.S_oeis_a097155.maxDigit x ≤ 9 := foldr_max_le L hdig
  have hrev : OMA.S_oeis_a097155.rev x = x + OMA.S_oeis_a097155.maxDigit x := by omega
  have hmod := rev_modEq x
  rw [hrev] at hmod
  have hm : OMA.S_oeis_a097155.maxDigit x = 0 ∨ OMA.S_oeis_a097155.maxDigit x = 9 := by
    unfold Nat.ModEq at hmod
    omega
  have hLne : L ≠ [] := by
    rw [hL]; exact Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have hlast : L.getLast hLne ≠ 0 := Nat.getLast_digit_ne_zero 10 (by omega)
  have hlastle : L.getLast hLne ≤ OMA.S_oeis_a097155.maxDigit x :=
    le_foldr_max L _ (List.getLast_mem hLne)
  rcases hm with hm | hm
  · omega
  rw [hm] at hrev
  -- decompose the digit list
  have hx10 : 10 ≤ x := by
    by_contra hlt
    push Not at hlt
    have hd : L = [x] := by rw [hL]; exact Nat.digits_of_lt 10 x (by omega) hlt
    have : OMA.S_oeis_a097155.rev x = x := by
      unfold OMA.S_oeis_a097155.rev; rw [← hL, hd]; simp
    omega
  have hLc : L = (x % 10) :: Nat.digits 10 (x / 10) := by
    rw [hL]; exact Nat.digits_def' (by norm_num) hxpos
  have htne : Nat.digits 10 (x / 10) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  obtain ⟨mid, a, hmid⟩ := (List.eq_nil_or_concat (Nat.digits 10 (x / 10))).resolve_left htne
  set d0 := x % 10 with hd0
  have hLf : L = d0 :: (mid ++ [a]) := by rw [hLc, hmid, List.concat_eq_append]
  have ha : a < 10 := hdig a (by rw [hLf]; simp)
  have hd0lt : d0 < 10 := Nat.mod_lt _ (by norm_num)
  have hmidd : ∀ d ∈ mid, d < 10 := fun d hd => hdig d (by rw [hLf]; simp [hd])
  set M := Nat.ofDigits 10 mid with hM
  set M' := Nat.ofDigits 10 mid.reverse with hM'
  set Q := 10 ^ mid.length with hQ
  have hMlt : M < Q := Nat.ofDigits_lt_base_pow_length (by norm_num) hmidd
  have hM'lt : M' < Q := by
    rw [hQ, ← List.length_reverse]
    exact Nat.ofDigits_lt_base_pow_length (by norm_num) (fun d hd => hmidd d (List.mem_reverse.mp hd))
  have hxe : x = d0 + 10 * (M + Q * a) := by
    have := Nat.ofDigits_digits 10 x
    rw [← hL, hLf, Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_singleton] at this
    rw [← this]
  have hre : OMA.S_oeis_a097155.rev x = a + 10 * (M' + Q * d0) := by
    unfold OMA.S_oeis_a097155.rev
    rw [← hL, hLf, List.reverse_cons, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.cons_append, Nat.ofDigits_cons, Nat.ofDigits_append,
      Nat.ofDigits_singleton, List.length_reverse]
  rw [hre, hxe] at hrev
  have hcase : d0 = a + 1 ∨ (d0 = 0 ∧ a = 9) := by omega
  rcases hcase with hc | ⟨hc1, hc2⟩
  · have hQa : Q * d0 = Q * a + Q := by rw [hc]; ring
    have hM'0 : M' = 0 := by omega
    have hmid0 : ∀ d ∈ mid, d = 0 := fun d hd =>
      ofDigits_eq_zero mid.reverse hM'0 d (List.mem_reverse.mpr hd)
    have hM0 : M = 0 := ofDigits_zeros mid hmid0
    have hQ1 : Q = 1 := by omega
    have hmidnil : mid = [] := by
      rw [hQ] at hQ1
      have : mid.length = 0 := by
        by_contra hne
        have : 10 ^ 1 ≤ 10 ^ mid.length := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact List.eq_nil_of_length_eq_zero this
    have hmax : OMA.S_oeis_a097155.maxDigit x = max d0 (max a 0) := by
      unfold OMA.S_oeis_a097155.maxDigit
      rw [← hL, hLf, hmidnil]
      rfl
    rw [hm] at hmax
    rw [hQ1, hM0] at hxe
    omega
  · rw [hc1, hc2] at hrev
    omega
