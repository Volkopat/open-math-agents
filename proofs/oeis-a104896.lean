import OMAStatements.S_oeis_a104896
import Mathlib

/-!
Proof of the A104896 conjecture. Write Q m for: m > 0 and no decimal digit of m is 0, 1 or 2,
and c M for the number of m < M with Q m. For r < 10, Q (r + 10 N) holds exactly when r ≥ 3 and
(N = 0 or Q N), since the digits of r + 10 N are r followed by the digits of N. Hence each block
of ten numbers 10 N, ..., 10 N + 9 contributes 7 when N = 0 or Q N and 0 otherwise, which gives
c (10 (N + 1)) = 7 c (N + 1) + 7. With c 1 = 0 this is the recurrence of a, so a n = c (10 ^ n).
-/

namespace OMA.P104896

open OMA.S_oeis_a104896

/-- m is positive and none of its decimal digits is 0, 1 or 2. -/
def Q (m : ℕ) : Prop := 0 < m ∧ ∀ d ∈ Nat.digits 10 m, d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 2

instance : DecidablePred Q := fun m => by unfold Q; infer_instance

/-- The indicator of Q. -/
def f (m : ℕ) : ℕ := if Q m then 1 else 0

/-- The number of m < M with Q m. -/
def c (M : ℕ) : ℕ := ∑ m ∈ Finset.range M, f m

lemma key (N r : ℕ) (hr : r < 10) : Q (r + 10 * N) ↔ (3 ≤ r ∧ (N = 0 ∨ Q N)) := by
  by_cases h : r = 0 ∧ N = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp [Q]
  · have hxy : r ≠ 0 ∨ N ≠ 0 := by tauto
    have hd : Nat.digits 10 (r + 10 * N) = r :: Nat.digits 10 N :=
      Nat.digits_add 10 (by norm_num) r N hr hxy
    unfold Q
    rw [hd]
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨_, ⟨h0, h1, h2⟩, hrest⟩
      refine ⟨by omega, ?_⟩
      rcases Nat.eq_zero_or_pos N with hN | hN
      · exact Or.inl hN
      · exact Or.inr ⟨hN, hrest⟩
    · rintro ⟨h3, hN⟩
      refine ⟨by omega, ⟨by omega, by omega, by omega⟩, ?_⟩
      rcases hN with hN | ⟨_, hN⟩
      · subst hN
        simp
      · exact hN

lemma blk (N : ℕ) :
    ∑ x ∈ Finset.range 10, f (10 * N + x) = if (N = 0 ∨ Q N) then 7 else 0 := by
  have hc : ∀ x ∈ Finset.range 10, f (10 * N + x) =
      if (3 ≤ x ∧ (N = 0 ∨ Q N)) then 1 else 0 := by
    intro x hx
    have hx' : x < 10 := Finset.mem_range.mp hx
    unfold f
    rw [show 10 * N + x = x + 10 * N by ring]
    simp only [key N x hx']
  rw [Finset.sum_congr rfl hc]
  by_cases hq : (N = 0 ∨ Q N)
  · simp only [hq, and_true, if_true]
    decide
  · simp only [hq, and_false, if_false, Finset.sum_const_zero]

lemma step (N : ℕ) : c (10 * (N + 1)) = 7 * c (N + 1) + 7 := by
  induction N with
  | zero =>
    have h1 : c (10 * (0 + 1)) = c (10 * 0) + ∑ x ∈ Finset.range 10, f (10 * 0 + x) := by
      unfold c
      rw [show 10 * (0 + 1) = 10 * 0 + 10 by ring, Finset.sum_range_add]
    rw [h1, blk]
    have hf0 : f 0 = 0 := by simp [f, Q]
    simp [c, hf0]
  | succ k ih =>
    have h1 : c (10 * (k + 1 + 1)) = c (10 * (k + 1)) +
        ∑ x ∈ Finset.range 10, f (10 * (k + 1) + x) := by
      unfold c
      rw [show 10 * (k + 1 + 1) = 10 * (k + 1) + 10 by ring, Finset.sum_range_add]
    have h2 : c (k + 1 + 1) = c (k + 1) + f (k + 1) := by
      unfold c
      rw [Finset.sum_range_succ]
    rw [h1, blk, ih, h2]
    have hne : ¬ (k + 1 = 0) := by omega
    by_cases hq : Q (k + 1)
    · have hfq : f (k + 1) = 1 := by simp [f, hq]
      simp only [hne, hq, or_true, if_true, hfq]
      ring
    · have hfq : f (k + 1) = 0 := by simp [f, hq]
      simp only [hne, hq, or_false, if_false, hfq]
      ring

lemma card_eq (M : ℕ) : ((Finset.range M).filter
      (fun m => 0 < m ∧ ∀ d ∈ Nat.digits 10 m, d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 2)).card = c M := by
  rw [Finset.card_filter]
  rfl

lemma a_eq (n : ℕ) : a n = c (10 ^ n) := by
  induction n with
  | zero =>
    have hf0 : f 0 = 0 := by simp [f, Q]
    simp only [a, pow_zero, c, Finset.sum_range_one, hf0]
  | succ k ih =>
    have hpos : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨N, hN⟩ : ∃ N, 10 ^ k = N + 1 := ⟨10 ^ k - 1, by omega⟩
    rw [a, ih, pow_succ, hN, show (N + 1) * 10 = 10 * (N + 1) by ring, step]

theorem sol : type_of% @OMA.S_oeis_a104896.main := by
  intro n
  rw [card_eq, a_eq]

end OMA.P104896

theorem OMA.solution : type_of% @OMA.S_oeis_a104896.main := OMA.P104896.sol
