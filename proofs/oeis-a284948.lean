import OMAStatements.S_oeis_a284948
import Mathlib

/-!
# A284948: the 1-limiting word of 0 -> 10, 1 -> 00 is A096268 shifted by two

Under 0 -> 10, 1 -> 00, letter 2j of the image of w is 1 - w(j) and letter 2j+1 is 0. So for
1 ≤ i < 2^k, letter i of S(k) is V(i) = v2(i) mod 2: V is 0 at odd i and V(2j) = 1 - V(j).
Under 0 -> 01, 1 -> 00, letter 2j of the image is 0 and letter 2j+1 is 1 - w(j), so for i < 2^k
letter i of T(k) is V(i+1). Then a(n) = V(n-1) = A096268(n-2) for n > 1.
-/

namespace OMA.P284948

open OMA.S_oeis_a284948

/-- 0 goes to 1, every other letter goes to 0. -/
def neg01 (c : ℕ) : ℕ := if c = 0 then 1 else 0

/-- The parity of the 2-adic valuation. -/
def V (i : ℕ) : ℕ := padicValNat 2 i % 2

lemma morph_length (c : ℕ) : (morph c).length = 2 := by
  cases c <;> rfl

lemma pdMorph_length (c : ℕ) : (pdMorph c).length = 2 := by
  cases c <;> rfl

lemma flatMap_length (w : List ℕ) : (w.flatMap morph).length = 2 * w.length := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [List.flatMap_cons, List.length_append, morph_length, ih, List.length_cons]
    ring

lemma pd_flatMap_length (w : List ℕ) : (w.flatMap pdMorph).length = 2 * w.length := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [List.flatMap_cons, List.length_append, pdMorph_length, ih, List.length_cons]
    ring

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

lemma flatMap_odd (w : List ℕ) (j : ℕ) :
    (w.flatMap morph)[2 * j + 1]? = w[j]?.map (fun _ => 0) := by
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

lemma pd_flatMap_even (w : List ℕ) (j : ℕ) :
    (w.flatMap pdMorph)[2 * j]? = w[j]?.map (fun _ => 0) := by
  induction w generalizing j with
  | nil => simp
  | cons c w ih =>
    rw [List.flatMap_cons]
    cases j with
    | zero =>
      cases c <;> simp [pdMorph]
    | succ j =>
      rw [List.getElem?_append_right (by rw [pdMorph_length]; omega), pdMorph_length]
      have h : 2 * (j + 1) - 2 = 2 * j := by omega
      rw [h, ih]
      simp

lemma pd_flatMap_odd (w : List ℕ) (j : ℕ) :
    (w.flatMap pdMorph)[2 * j + 1]? = w[j]?.map neg01 := by
  induction w generalizing j with
  | nil => simp
  | cons c w ih =>
    rw [List.flatMap_cons]
    cases j with
    | zero =>
      cases c <;> simp [pdMorph, neg01]
    | succ j =>
      rw [List.getElem?_append_right (by rw [pdMorph_length]; omega), pdMorph_length]
      have h : 2 * (j + 1) + 1 - 2 = 2 * j + 1 := by omega
      rw [h, ih]
      simp

lemma iter_succ (k : ℕ) : iter (k + 1) = (iter k).flatMap morph := rfl

lemma pdIter_succ (k : ℕ) : pdIter (k + 1) = (pdIter k).flatMap pdMorph := rfl

lemma iter_length (k : ℕ) : (iter k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iter_succ, flatMap_length, ih, pow_succ]; ring

lemma pdIter_length (k : ℕ) : (pdIter k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pdIter_succ, pd_flatMap_length, ih, pow_succ]; ring

lemma V_odd (j : ℕ) : V (2 * j + 1) = 0 := by
  unfold V
  rw [padicValNat.eq_zero_of_not_dvd (by omega)]

lemma V_even (j : ℕ) (hj : 1 ≤ j) : V (2 * j) = neg01 (V j) := by
  unfold V neg01
  have h : padicValNat 2 (2 * j) = 1 + padicValNat 2 j := by
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
  rw [h]
  split_ifs with h' <;> omega

/-- For 1 ≤ i < 2^k, letter i of S(k) is v2(i) mod 2. -/
lemma iter_letter (k : ℕ) : ∀ i, 1 ≤ i → i < 2 ^ k → (iter k)[i]? = some (V i) := by
  induction k with
  | zero => intro i h1 h2; simp at h2; omega
  | succ k ih =>
    intro i h1 h2
    rw [iter_succ]
    rw [pow_succ] at h2
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [flatMap_even, ih j (by omega) (by omega)]
      simp [V_even j (by omega)]
    · rw [flatMap_odd]
      have hj : j < (iter k).length := by rw [iter_length]; omega
      rw [List.getElem?_eq_getElem hj]
      simp [V_odd]

/-- For i < 2^k, letter i of T(k) is v2(i+1) mod 2. -/
lemma pdIter_letter (k : ℕ) : ∀ i, i < 2 ^ k → (pdIter k)[i]? = some (V (i + 1)) := by
  induction k with
  | zero =>
    intro i h2
    obtain rfl : i = 0 := by simp at h2; omega
    simp [pdIter, V]
  | succ k ih =>
    intro i h2
    rw [pdIter_succ]
    rw [pow_succ] at h2
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [pd_flatMap_even]
      have hj : j < (pdIter k).length := by rw [pdIter_length]; omega
      rw [List.getElem?_eq_getElem hj]
      simp [V_odd]
    · rw [pd_flatMap_odd, ih j (by omega)]
      have h : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
      rw [h, V_even (j + 1) (by omega)]
      simp

theorem sol : type_of% @OMA.S_oeis_a284948.main := by
  intro n hn
  unfold a A096268
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    iter_letter (2 * n + 1) (n - 1) (by omega) ?_, pdIter_letter (n - 2 + 1) (n - 2) ?_]
  · simp
    congr 1
    omega
  · have := @Nat.lt_two_pow_self (n - 2 + 1)
    omega
  · have := @Nat.lt_two_pow_self (2 * n + 1)
    omega

end OMA.P284948

theorem OMA.solution : type_of% @OMA.S_oeis_a284948.main := OMA.P284948.sol

