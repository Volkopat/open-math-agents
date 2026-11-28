import OMAStatements.S_oeis_a285076
import Mathlib

/-!
# A285076: the 1-limiting word of 0 -> 10, 1 -> 010 agrees with the 0-limiting word from n = 3

Write Q for the squared morphism. Q(10) = 10 z and Q(01) = 01 z with the same tail
z = 0101001010. By induction on k ≥ 1, S(2k) = 01 v and S(2k+1) = 10 v w for some words v, w:
S(2) = 01 010 and S(3) = 10 010 1001010, and applying Q (a morphism, so it splits over
concatenation) gives S(2k+2) = 01 (z Q(v)) and S(2k+3) = 10 (z Q(v)) Q(w). Every letter has an
image of length at least 2, so S(k) has at least 2^k letters, and letter n - 1 (counting from 0)
of both words lies in the common block v once n ≥ 3.
-/

namespace OMA.P285076

open OMA.S_oeis_a285076

lemma morph_length_ge (c : ℕ) : 2 ≤ (morph c).length := by
  cases c <;> simp [morph]

lemma flatMap_length_ge (w : List ℕ) : 2 * w.length ≤ (w.flatMap morph).length := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := morph_length_ge c
    omega

lemma iter_length (k : ℕ) : 2 ^ k ≤ (iter k).length := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    rw [iter, pow_succ]
    have := flatMap_length_ge (iter k)
    omega

/-- The squared morphism. -/
def sq (w : List ℕ) : List ℕ := (w.flatMap morph).flatMap morph

lemma sq_append (u v : List ℕ) : sq (u ++ v) = sq u ++ sq v := by
  simp [sq, List.flatMap_append]

lemma iter_add_two (k : ℕ) : iter (k + 2) = sq (iter k) := rfl

/-- The common tail of the squared images of 10 and 01. -/
def z : List ℕ := [0, 1, 0, 1, 0, 0, 1, 0, 1, 0]

lemma sq_10 : sq [1, 0] = [1, 0] ++ z := by decide

lemma sq_01 : sq [0, 1] = [0, 1] ++ z := by decide

lemma key (k : ℕ) (hk : 1 ≤ k) :
    ∃ v w : List ℕ, iter (2 * k) = [0, 1] ++ v ∧ iter (2 * k + 1) = [1, 0] ++ v ++ w := by
  induction k, hk using Nat.le_induction with
  | base => exact ⟨[0, 1, 0], [1, 0, 0, 1, 0, 1, 0], by decide, by decide⟩
  | succ k hk ih =>
    obtain ⟨v, w, h1, h2⟩ := ih
    refine ⟨z ++ sq v, sq w, ?_, ?_⟩
    · have e : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [e, iter_add_two, h1, sq_append, sq_01, List.append_assoc]
    · have e : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
      rw [e, iter_add_two, h2, sq_append, sq_append, sq_10]
      simp only [List.append_assoc]

theorem sol : type_of% @OMA.S_oeis_a285076.main := by
  intro n hn
  obtain ⟨v, w, h1, h2⟩ := key n (by omega)
  have hlen : 2 ^ (2 * n) ≤ 2 + v.length := by
    have := iter_length (2 * n)
    rw [h1, List.length_append] at this
    simpa [Nat.add_comm] using this
  have hn2 : n < 2 ^ n := Nat.lt_two_pow_self
  have hpow : 2 ^ n ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt : n - 3 < v.length := by omega
  unfold a A285073
  rw [h1, h2]
  have hm : n - 1 = (n - 3) + 2 := by omega
  rw [hm]
  simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
  rw [List.getD_append _ _ _ _ hlt]

end OMA.P285076

theorem OMA.solution : type_of% @OMA.S_oeis_a285076.main := OMA.P285076.sol

