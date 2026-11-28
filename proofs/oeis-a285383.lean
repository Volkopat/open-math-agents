import OMAStatements.S_oeis_a285383
import Mathlib

/-!
# A285383: the limiting 0-word of 0 -> 11, 1 -> 01 is A035263 shifted by one

Letter 2j of the image of a word w is 1 - w(j) (0 goes to 11, 1 goes to 01) and letter 2j+1 is
always 1. So letter 0 of S(k) is k mod 2, and for 1 ≤ i < 2^k letter i of S(k) depends only on
the 2-adic valuation of i: it is 1 when i is odd, and letter 2j is 1 - letter j. The same two
rules hold for A035263(i) = v2(2i) mod 2, which gives letter i of S(k) = A035263(i). Then
a(n) = letter n-1 of S(2n) = A035263(n-1) for n ≥ 2, and a(1) = letter 0 of S(2) = 0 = A035263(0).
-/

namespace OMA.P285383

open OMA.S_oeis_a285383

/-- 0 goes to 1, every other letter goes to 0. -/
def neg01 (c : ℕ) : ℕ := if c = 0 then 1 else 0

lemma morph_length (c : ℕ) : (morph c).length = 2 := by
  cases c <;> rfl

lemma flatMap_length (w : List ℕ) : (w.flatMap morph).length = 2 * w.length := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [List.flatMap_cons, List.length_append, morph_length, ih, List.length_cons]
    ring

/-- Letter 2j of the image of w is 1 - w(j). -/
lemma flatMap_even (w : List ℕ) (j : ℕ) :
    (w.flatMap morph)[2 * j]? = w[j]?.map neg01 := by
  induction w generalizing j with
  | nil => simp
  | cons c w ih =>
    rw [List.flatMap_cons]
    cases j with
    | zero =>
      cases c <;> simp [morph, neg01]
    | succ j =>
      rw [List.getElem?_append_right (by rw [morph_length]; omega), morph_length]
      have h : 2 * (j + 1) - 2 = 2 * j := by omega
      rw [h, ih]
      simp

/-- Letter 2j+1 of the image of w is 1. -/
lemma flatMap_odd (w : List ℕ) (j : ℕ) :
    (w.flatMap morph)[2 * j + 1]? = w[j]?.map (fun _ => 1) := by
  induction w generalizing j with
  | nil => simp
  | cons c w ih =>
    rw [List.flatMap_cons]
    cases j with
    | zero =>
      cases c <;> simp [morph]
    | succ j =>
      rw [List.getElem?_append_right (by rw [morph_length]; omega), morph_length]
      have h : 2 * (j + 1) + 1 - 2 = 2 * j + 1 := by omega
      rw [h, ih]
      simp

lemma iter_succ (k : ℕ) : iter (k + 1) = (iter k).flatMap morph := rfl

lemma iter_length (k : ℕ) : (iter k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iter_succ, flatMap_length, ih, pow_succ]; ring

lemma A_odd (j : ℕ) : A035263 (2 * j + 1) = 1 := by
  unfold A035263
  have h : padicValNat 2 (2 * (2 * j + 1)) = 1 := by
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by omega)]
  rw [h]

lemma A_even (j : ℕ) (hj : 1 ≤ j) : A035263 (2 * j) = neg01 (A035263 j) := by
  unfold A035263 neg01
  have h : padicValNat 2 (2 * (2 * j)) = 1 + padicValNat 2 (2 * j) := by
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
  rw [h]
  split_ifs with h' <;> omega

/-- For 1 ≤ i < 2^k, letter i of S(k) is A035263(i). -/
lemma iter_letter (k : ℕ) : ∀ i, 1 ≤ i → i < 2 ^ k → (iter k)[i]? = some (A035263 i) := by
  induction k with
  | zero => intro i h1 h2; simp at h2; omega
  | succ k ih =>
    intro i h1 h2
    rw [iter_succ]
    rw [pow_succ] at h2
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [flatMap_even, ih j (by omega) (by omega)]
      simp [A_even j (by omega)]
    · rw [flatMap_odd]
      have hj : j < (iter k).length := by rw [iter_length]; omega
      rw [List.getElem?_eq_getElem hj]
      simp [A_odd]

theorem sol : type_of% @OMA.S_oeis_a285383.main := by
  intro n hn
  unfold a
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    simp [iter, morph, A035263]
  · rw [List.getD_eq_getElem?_getD, iter_letter (2 * n) (n - 1) (by omega) ?_]
    · simp
    · have := @Nat.lt_two_pow_self (2 * n)
      omega

end OMA.P285383

theorem OMA.solution : type_of% @OMA.S_oeis_a285383.main := OMA.P285383.sol

