import OMAStatements.S_oeis_a082274
import Mathlib

-- Problem: A082274, palindromes n such that n + 2 is also a palindrome.
-- Upstream: formal-conjectures statements/oeis-a082274.lean (declaration OMA.S_oeis_a082274.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: for n = d + 10 m with m > 0, a palindrome's leading digit equals its last digit d.
-- If d < 8 the leading digit of n + 2 would be d + 2; if d = 8 then n + 2 ends in 0; if d = 9
-- then m starts with 9 while m + 1 starts with 1, which forces m + 1 to be a power of 10.

namespace OMA.P_oeis_a082274

open OMA.S_oeis_a082274

theorem digits_pow_sub_one (k : ℕ) : Nat.digits 10 (10 ^ k - 1) = List.replicate k 9 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
    rw [show 10 ^ (k + 1) - 1 = 9 + 10 * (10 ^ k - 1) by rw [pow_succ]; omega,
      Nat.digits_add 10 (by norm_num) 9 _ (by norm_num) (Or.inl (by norm_num)), ih,
      List.replicate_succ]

theorem digits_pow_add_one (k : ℕ) (hk : 0 < k) :
    Nat.digits 10 (10 ^ k + 1) = 1 :: (List.replicate (k - 1) 0 ++ [1]) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 : 1 ≤ 10 ^ j := Nat.one_le_pow _ _ (by norm_num)
  rw [show 10 ^ (j + 1) + 1 = 1 + 10 * 10 ^ j by rw [pow_succ]; ring,
    Nat.digits_add 10 (by norm_num) 1 _ (by norm_num) (Or.inl (by norm_num)),
    show (10 : ℕ) ^ j = 10 ^ j * 1 by ring, Nat.digits_base_pow_mul (by norm_num) (by norm_num)]
  simp

theorem pal_getLast (L : List ℕ) (a : ℕ) (h : (a :: L).reverse = a :: L) (hL : L ≠ []) :
    L.getLast hL = a := by
  have := congrArg (fun l => l.head?) h
  simp only [List.head?_reverse, List.head?_cons] at this
  rw [List.getLast?_cons, List.getLast?_eq_some_getLast hL] at this
  simpa using this

theorem last_bounds (x : ℕ) (hx : x ≠ 0) :
    (Nat.digits 10 x).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hx) *
        10 ^ ((Nat.digits 10 x).length - 1) ≤ x ∧
      x < ((Nat.digits 10 x).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hx) + 1) *
        10 ^ ((Nat.digits 10 x).length - 1) := by
  set D := Nat.digits 10 x with hD
  have hne : D ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hx
  set t := D.getLast hne
  have hsplit : D = D.dropLast ++ [t] := (List.dropLast_append_getLast hne).symm
  have hlen : D.dropLast.length = D.length - 1 := List.length_dropLast
  have hval : x = Nat.ofDigits 10 D.dropLast + 10 ^ (D.length - 1) * t := by
    have h := Nat.ofDigits_digits 10 x
    rw [← hD, hsplit, Nat.ofDigits_append, hlen] at h
    simpa [Nat.ofDigits] using h.symm
  have hlt : Nat.ofDigits 10 D.dropLast < 10 ^ (D.length - 1) := by
    rw [← hlen]
    apply Nat.ofDigits_lt_base_pow_length (by norm_num)
    intro y hy
    exact Nat.digits_lt_base (by norm_num) (List.mem_of_mem_dropLast hy)
  show t * 10 ^ (D.length - 1) ≤ x ∧ x < (t + 1) * 10 ^ (D.length - 1)
  rw [hval]
  constructor
  · rw [mul_comm t]
    exact Nat.le_add_left _ _
  · rw [add_mul, one_mul, mul_comm t]
    linarith

theorem main' : ∀ n : ℕ, 0 < n →
    (Pal n ∧ Pal (n + 2) ↔ n ≤ 7 ∨ ∃ k : ℕ, 0 < k ∧ n = 10^k - 1) := by
  intro n hn
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h7 : n ≤ 7
    · exact Or.inl h7
    right
    unfold Pal at h1 h2
    obtain ⟨d, m, hd, rfl⟩ : ∃ d m, d < 10 ∧ n = d + 10 * m :=
      ⟨n % 10, n / 10, Nat.mod_lt _ (by norm_num), (Nat.mod_add_div n 10).symm⟩
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have : d = 8 ∨ d = 9 := by omega
      rcases this with rfl | rfl
      · exact absurd h2 (by norm_num)
      · exact ⟨1, by norm_num, by norm_num⟩
    have hm0 : m ≠ 0 := by omega
    have hDm : Nat.digits 10 m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hm0
    rw [Nat.digits_add 10 (by norm_num) d m hd (Or.inr hm0)] at h1
    have hlast := pal_getLast _ _ h1 hDm
    have hnz := Nat.getLast_digit_ne_zero 10 hm0
    have hd9 : d ≤ 7 ∨ d = 8 ∨ d = 9 := by omega
    rcases hd9 with hd7 | rfl | rfl
    · rw [show d + 10 * m + 2 = (d + 2) + 10 * m by ring,
        Nat.digits_add 10 (by norm_num) (d + 2) m (by omega) (Or.inr hm0)] at h2
      have := pal_getLast _ _ h2 hDm
      omega
    · rw [show 8 + 10 * m + 2 = 0 + 10 * (m + 1) by ring,
        Nat.digits_add 10 (by norm_num) 0 (m + 1) (by norm_num) (Or.inr (by omega))] at h2
      have hm1 : m + 1 ≠ 0 := by omega
      have := pal_getLast _ _ h2 (Nat.digits_ne_nil_iff_ne_zero.mpr hm1)
      exact absurd this (Nat.getLast_digit_ne_zero 10 hm1)
    · rw [show 9 + 10 * m + 2 = 1 + 10 * (m + 1) by ring,
        Nat.digits_add 10 (by norm_num) 1 (m + 1) (by norm_num) (Or.inr (by omega))] at h2
      have hm1 : m + 1 ≠ 0 := by omega
      have hl1 := pal_getLast _ _ h2 (Nat.digits_ne_nil_iff_ne_zero.mpr hm1)
      obtain ⟨b1, b2⟩ := last_bounds m hm0
      obtain ⟨c1, c2⟩ := last_bounds (m + 1) hm1
      rw [hlast] at b1 b2
      rw [hl1] at c1 c2
      set l := (Nat.digits 10 m).length - 1
      set l' := (Nat.digits 10 (m + 1)).length - 1
      have hll : l < l' := by
        by_contra hc
        have : 10 ^ l' ≤ 10 ^ l := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hll' : 10 ^ (l + 1) ≤ 10 ^ l' := Nat.pow_le_pow_right (by norm_num) hll
      rw [pow_succ] at hll'
      have hm' : m + 1 = 10 ^ l * 10 := by omega
      refine ⟨l + 2, by omega, ?_⟩
      rw [show 10 ^ (l + 2) = 10 ^ l * 10 * 10 by ring]
      omega
  · rintro (h | ⟨k, hk, rfl⟩)
    · unfold Pal
      rw [Nat.digits_of_lt 10 n (by omega) (by omega),
        Nat.digits_of_lt 10 (n + 2) (by omega) (by omega)]
      simp
    · unfold Pal
      have h1 : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
      rw [show 10 ^ k - 1 + 2 = 10 ^ k + 1 by omega, digits_pow_sub_one,
        digits_pow_add_one k hk]
      simp

end OMA.P_oeis_a082274

theorem OMA.solution : type_of% @OMA.S_oeis_a082274.main := OMA.P_oeis_a082274.main'
