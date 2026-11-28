import OMAStatements.S_oeis_a328544
import Mathlib

open OMA.S_oeis_a328544


set_option maxRecDepth 100000 in
theorem small_case : ∀ k < 1000, (∀ d ∈ dec k, List.IsInfix (dec k) (dec (k * d))) → k = 0 ∨ k = 1 ∨ k = 5 ∨ k = 6 ∨ k = 11 ∨ k = 111 := by
  decide +kernel

theorem dec_pos {k : ℕ} (hk : k ≠ 0) : dec k = (Nat.digits 10 k).reverse := by
  simp [dec, hk]

theorem no_zero_digit {k : ℕ} (hg : good k) (hk : 10 ≤ k) : 0 ∉ Nat.digits 10 k := by
  intro h0
  have hk0 : k ≠ 0 := by omega
  have hmem : 0 ∈ dec k := by rw [dec_pos hk0]; exact List.mem_reverse.2 h0
  have hi := hg 0 hmem
  rw [Nat.mul_zero] at hi
  have hl := hi.length_le
  rw [dec_pos hk0, List.length_reverse] at hl
  simp [dec] at hl
  have := Nat.lt_base_pow_length_digits (b := 10) (m := k) (by norm_num)
  have h10 : (10:ℕ) ^ (Nat.digits 10 k).length ≤ 10 ^ 1 := Nat.pow_le_pow_right (by norm_num) hl
  omega

theorem big_case {k : ℕ} (hg : good k) (hk : 1000 ≤ k) : ∀ d ∈ Nat.digits 10 k, d = 1 := by
  intro d hd
  by_contra hne
  have hk0 : k ≠ 0 := by omega
  have h0 := no_zero_digit hg (by omega)
  have hd0 : d ≠ 0 := by rintro rfl; exact h0 hd
  have hd9 : d < 10 := Nat.digits_lt_base (by norm_num) hd
  have hd2 : 2 ≤ d := by omega
  have hmem : d ∈ dec k := by rw [dec_pos hk0]; exact List.mem_reverse.2 hd
  have hi := hg d hmem
  have hkd0 : k * d ≠ 0 := Nat.mul_ne_zero hk0 hd0
  rw [dec_pos hk0, dec_pos hkd0, List.reverse_infix] at hi
  obtain ⟨s, t, hst⟩ := hi
  rw [List.append_assoc] at hst
  have hval := congrArg (Nat.ofDigits 10) hst
  rw [Nat.ofDigits_digits, Nat.ofDigits_append, Nat.ofDigits_append, Nat.ofDigits_digits] at hval
  set L := (Nat.digits 10 k).length with hL
  have hkL : k < 10 ^ L := Nat.lt_base_pow_length_digits (by norm_num)
  have hL4 : 4 ≤ L := by
    by_contra hL3
    have : (10:ℕ) ^ L ≤ 10 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hs : s.length = 0 := by
    by_contra hs
    have h10 : (10:ℕ) ≤ 10 ^ s.length := by
      calc (10:ℕ) = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ s.length := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 10 * k ≤ 10 ^ s.length * (k + 10 ^ L * Nat.ofDigits 10 t) := by
      calc 10 * k ≤ 10 ^ s.length * k := Nat.mul_le_mul_right _ h10
        _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
    have : k * d ≤ k * 9 := Nat.mul_le_mul_left _ (by omega)
    omega
  rw [hs, pow_zero, one_mul] at hval
  have hs' : s = [] := List.length_eq_zero_iff.1 hs
  rw [hs'] at hval
  simp only [Nat.ofDigits_nil, zero_add] at hval
  -- k * d = k + 10^L * T
  have hdiv : 10000 ∣ 10 ^ L := by
    have : (10:ℕ) ^ 4 ∣ 10 ^ L := Nat.pow_dvd_pow 10 hL4
    simpa using this
  obtain ⟨q, hq⟩ := hdiv
  have hkey : k * d = k + 10000 * (q * Nat.ofDigits 10 t) := by rw [← hval, hq]; ring
  have hk10 : k % 10 = 0 := by
    interval_cases d <;> omega
  apply h0
  rw [Nat.digits_def' (by norm_num) (by omega), hk10]
  exact List.mem_cons_self

theorem digits_repunit (m : ℕ) : Nat.digits 10 (repunit m) = List.replicate m 1 := by
  unfold repunit
  apply Nat.digits_ofDigits _ (by norm_num)
  · intro x hx
    rw [List.eq_of_mem_replicate hx]; norm_num
  · intro h
    rw [List.getLast_replicate]; norm_num

theorem repunit_good (m : ℕ) (hm : 1 ≤ m) : good (repunit m) := by
  have hne : repunit m ≠ 0 := by
    intro h
    have := digits_repunit m
    rw [h, Nat.digits_zero] at this
    have := congrArg List.length this
    simp at this
    omega
  intro d hd
  rw [dec_pos hne, List.mem_reverse, digits_repunit] at hd
  rw [List.eq_of_mem_replicate hd, Nat.mul_one]

theorem OMA.solution : type_of% @OMA.S_oeis_a328544.main := by
  intro k
  constructor
  · intro hg
    by_cases hk : k < 1000
    · rcases small_case k hk hg with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr ⟨1, le_refl _, by rw [h]; decide⟩))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr ⟨2, by norm_num, by rw [h]; decide⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨3, by norm_num, by rw [h]; decide⟩))
    · have h1 := big_case hg (by omega)
      refine Or.inr (Or.inr (Or.inr ⟨(Nat.digits 10 k).length, ?_, ?_⟩))
      · have : Nat.digits 10 k ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
        exact List.length_pos_iff.2 this
      · have hrep : Nat.digits 10 k = List.replicate (Nat.digits 10 k).length 1 :=
          List.eq_replicate_iff.2 ⟨rfl, h1⟩
        unfold repunit
        rw [← hrep, Nat.ofDigits_digits]
  · rintro (h | h | h | ⟨m, hm, rfl⟩)
    · subst h; unfold good; decide
    · subst h; unfold good; decide
    · subst h; unfold good; decide
    · exact repunit_good m hm
