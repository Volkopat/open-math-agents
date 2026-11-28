import OMAStatements.S_oeis_a188819
import Mathlib

open OMA.S_oeis_a188819

namespace P188819

theorem al0 : allowed 0 = {0} := by decide
theorem al1 : allowed 1 = {0} := by decide
theorem al4 : allowed 4 = {0} := by decide
theorem al2 : allowed 2 = {0, 1, 4, 5} := by decide
theorem al3 : allowed 3 = {0, 1, 4, 5} := by decide
theorem al6 : allowed 6 = {0, 1, 4, 5} := by decide
theorem al5 : allowed 5 = {0, 2} := by decide
theorem al7 : allowed 7 = {0, 1, 2, 3, 4, 5, 6, 7} := by decide

theorem cs (n u : ℕ) : continuations (n + 1) u = ∑ v ∈ allowed u, continuations n v := rfl

def F2 (n : ℕ) : ℤ := 2 * n + 1 + (n % 2 : ℕ)
def F5 (n : ℕ) : ℤ := 2 * n + 1 - (n % 2 : ℕ)
def F7 (n : ℕ) : ℤ := 4 * n ^ 2 + 4 * n + 1 - (n % 2 : ℕ)

theorem cl : ∀ n : ℕ, continuations n 0 = 1 ∧ continuations n 1 = 1 ∧ continuations n 4 = 1 ∧
    continuations n 2 = F2 n ∧ continuations n 3 = F2 n ∧ continuations n 6 = F2 n ∧
    continuations n 5 = F5 n ∧ continuations n 7 = F7 n := by
  intro n
  induction n with
  | zero => simp [continuations, F2, F5, F7]
  | succ n ih =>
    obtain ⟨h0, h1, h4, h2, h3, h6, h5, h7⟩ := ih
    have hp : (n + 1) % 2 = 1 - n % 2 := by omega
    have hb : n % 2 ≤ 1 := by omega
    simp only [cs, al0, al1, al4, al2, al3, al6, al5, al7]
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    rw [h0, h1, h4, h2, h3, h6, h5, h7]
    simp only [F2, F5, F7, hp]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> norm_num <;> push_cast <;> ring_nf <;> simp

theorem arr (n : ℕ) (hn : 0 < n) : arrays n = 4 * (n : ℤ) ^ 2 + 4 * n + 1 - (n % 2 : ℕ) := by
  unfold arrays
  rw [if_neg (by omega), (cl n).2.2.2.2.2.2.2]
  rfl

end P188819

theorem OMA.solution : type_of% @OMA.S_oeis_a188819.main := by
  refine ⟨fun n hn he => ?_, fun n hn ho => ?_, fun n => ?_⟩
  · rw [P188819.arr n hn, Nat.even_iff.mp he]; push_cast; ring
  · rw [P188819.arr n hn, Nat.odd_iff.mp ho]; push_cast; ring
  · rcases Nat.lt_or_ge n 5 with hn | hn
    · interval_cases n <;> decide
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      have hz : numerator (k + 5) = 0 := by
        unfold numerator; split_ifs <;> first | omega | rfl
      simp only [delayed, show 1 ≤ k + 5 by omega, show 3 ≤ k + 5 by omega, show 4 ≤ k + 5 by omega,
        if_true, show k + 5 - 1 = k + 4 by omega, show k + 5 - 3 = k + 2 by omega,
        show k + 5 - 4 = k + 1 by omega, hz]
      rw [P188819.arr _ (by omega), P188819.arr _ (by omega), P188819.arr _ (by omega),
        P188819.arr _ (by omega)]
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · rw [show (k + 5) % 2 = 1 by omega, show (k + 4) % 2 = 0 by omega,
          show (k + 2) % 2 = 0 by omega, show (k + 1) % 2 = 1 by omega]
        push_cast; ring
      · rw [show (k + 5) % 2 = 0 by omega, show (k + 4) % 2 = 1 by omega,
          show (k + 2) % 2 = 1 by omega, show (k + 1) % 2 = 0 by omega]
        push_cast; ring
