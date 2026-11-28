import OMAStatements.S_oeis_a120160
import Mathlib

/-!
# OEIS A120160: exactly 5*a(n) nonnegative integers have n digits in fractional base 5/4

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. Let S(n) = a(1) + ... + a(n); then S(1) = 1 and S(n+1) = S(n) + ceil(S(n)/4). Claim: the integers
with at most n digits are exactly [0, 5*S(n)). For n = 1 this is [0, 5). Step: m has at most n+1
digits iff m < 5 or 4*floor(m/5) has at most n digits, i.e. 4*floor(m/5) < 5*S(n); for an integer q,
4q < B iff q < ceil(B/4), so the condition is m < 5*ceil(5*S(n)/4) = 5*(S(n) + ceil(S(n)/4)) =
5*S(n+1). Hence the integers with exactly n digits form [5*S(n-1), 5*S(n)), of size 5*a(n) (with
S(0) = 0).
-/

open OMA.S_oeis_a120160

namespace OMA.A120160Proof

abbrev S (n : ℕ) : ℕ := (aS n).2

lemma S_zero : S 0 = 0 := rfl

lemma S_one : S 1 = 1 := rfl

lemma S_succ (n : ℕ) : S (n + 1) = S n + a (n + 1) := by
  cases n with
  | zero => rfl
  | succ n => rfl

lemma S_step (n : ℕ) (hn : 1 ≤ n) :
    S (n + 1) = S n + (S n + 3) / 4 := by
  cases n with
  | zero => omega
  | succ n => rfl

lemma S_pos (n : ℕ) : 1 ≤ S (n + 1) := by
  induction n with
  | zero => rw [Nat.zero_add, S_one]
  | succ n ih =>
    rw [S_succ]
    omega

lemma digitLength_pos (m : ℕ) : 1 ≤ digitLength m := by
  rw [digitLength]
  split <;> omega

lemma digitLength_le_one (m : ℕ) : digitLength m ≤ 1 ↔ m < 5 := by
  by_cases hm : m < 5
  · rw [digitLength, if_pos hm]
    omega
  · rw [digitLength, if_neg hm]
    have hp := digitLength_pos (4 * (m / 5))
    omega

lemma digitLength_le (n m : ℕ) :
    digitLength m ≤ n + 1 ↔ m < 5 * S (n + 1) := by
  induction n generalizing m with
  | zero =>
    simpa only [Nat.zero_add, S_one, Nat.mul_one] using digitLength_le_one m
  | succ n ih =>
    have hp := S_pos n
    have hs := S_step (n + 1) (by omega)
    by_cases hm : m < 5
    · rw [digitLength, if_pos hm]
      rw [hs]
      omega
    · rw [digitLength, if_neg hm]
      have hlength :
          1 + digitLength (4 * (m / 5)) ≤ n + 1 + 1 ↔
            digitLength (4 * (m / 5)) ≤ n + 1 := by omega
      rw [hlength, ih, hs]
      have hround :
          4 * (m / 5) < 5 * S (n + 1) ↔
            m / 5 < S (n + 1) + (S (n + 1) + 3) / 4 := by omega
      rw [hround]
      omega

lemma digitLength_eq_interval (n : ℕ) :
    {m : ℕ | digitLength m = n + 1} =
      Set.Ico (5 * S n) (5 * S (n + 1)) := by
  ext m
  simp only [Set.mem_ofPred_eq, Set.mem_Ico]
  have hupper := digitLength_le n m
  cases n with
  | zero =>
    have hp := digitLength_pos m
    rw [S_zero]
    omega
  | succ n =>
    have hlower := digitLength_le n m
    omega

end OMA.A120160Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a120160.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [OMA.A120160Proof.digitLength_eq_interval]
  rw [← Finset.coe_Ico, Set.ncard_coe_finset, Nat.card_Ico]
  rw [OMA.A120160Proof.S_succ]
  simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.add_sub_cancel_left]
