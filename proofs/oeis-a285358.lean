import OMAStatements.S_oeis_a285358
import Mathlib

/-!
# A285358: the fixed point of 0 -> 10, 1 -> 1101 is A284929 shifted by one

Write tau for 0 -> 10, 1 -> 1101 and sigma for 0 -> 01, 1 -> 1011. For each letter c, tau(c)
followed by 1 is 1 followed by sigma(c) (101 and 11011), so tau(v) 1 = 1 sigma(v) for every word v.
By induction on k this gives X(k+1) = 0 Y(k) r for some word r: X(1) = 01, and
X(k+2) = sigma(0 Y(k) r) = 0 1 sigma(Y(k) r) = 0 tau(Y(k) r) 1 = 0 Y(k+1) tau(r) 1.
So letter n + 1 of X(n+1) is letter n of Y(n), since Y(n) has at least n letters.
-/

namespace OMA.P285358

open OMA.S_oeis_a285358

lemma conj (v : List ℕ) : v.flatMap morph ++ [1] = 1 :: v.flatMap morph2 := by
  induction v with
  | nil => simp
  | cons c v ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.append_assoc, ih]
    cases c <;> simp [morph, morph2]

lemma morph_length (c : ℕ) : 2 ≤ (morph c).length := by
  cases c <;> simp [morph]

lemma flatMap_length (w : List ℕ) : 2 * w.length ≤ (w.flatMap morph).length := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := morph_length c
    omega

lemma iter_length (k : ℕ) : k + 1 ≤ (iter k).length := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    have h := flatMap_length (iter k)
    have h2 : (iter (k + 1)).length = ((iter k).flatMap morph).length := rfl
    omega

lemma key (k : ℕ) : ∃ r, iter2 (k + 1) = 0 :: (iter k ++ r) := by
  induction k with
  | zero => exact ⟨[], rfl⟩
  | succ k ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨r.flatMap morph ++ [1], ?_⟩
    have h1 : iter2 (k + 1 + 1) = (iter2 (k + 1)).flatMap morph2 := rfl
    have h2 : iter (k + 1) = (iter k).flatMap morph := rfl
    rw [h1, hr, h2, List.flatMap_cons]
    have h3 := conj (iter k ++ r)
    rw [List.flatMap_append, List.flatMap_append] at h3
    rw [List.flatMap_append]
    simp only [morph2, List.cons_append, List.nil_append]
    rw [← List.append_assoc, h3]

theorem sol : type_of% @OMA.S_oeis_a285358.main := by
  intro n hn
  unfold a A284929
  obtain ⟨r, hr⟩ := key n
  rw [hr]
  have hlen := iter_length n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by omega)]

end OMA.P285358

theorem OMA.solution : type_of% @OMA.S_oeis_a285358.main := OMA.P285358.sol
