import OMAStatements.S_oeis_a392003
import Mathlib

namespace OMA.S_oeis_a392003

def dot (n : ℕ) (p : ℤ) : Prop :=
  p = 1 - n ∨ (2 - (n : ℤ) ≤ p ∧ p ≤ n ∧ 2 ∣ ((n : ℤ) - p))

theorem pat : ∀ n : ℕ, 1 ≤ n → ∀ p : ℤ, ca163 n p = true ↔ ¬ dot n p := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro p
    have ha : ca163 0 (p - 1) = true ↔ p - 1 = 0 := by simp [ca163]
    have hb : ca163 0 p = true ↔ p = 0 := by simp [ca163]
    have hc : ca163 0 (p + 1) = true ↔ p + 1 = 0 := by simp [ca163]
    rw [show ca163 1 p = rule163 (ca163 0 (p - 1)) (ca163 0 p) (ca163 0 (p + 1)) from rfl]
    generalize ca163 0 (p - 1) = a at *
    generalize ca163 0 p = b at *
    generalize ca163 0 (p + 1) = c at *
    simp only [dot] at *
    cases a <;> cases b <;> cases c <;> simp [rule163] at * <;> push_cast <;> omega
  | succ n hn ih =>
    intro p
    have ha := ih (p - 1)
    have hb := ih p
    have hc := ih (p + 1)
    simp only [ca163]
    generalize ca163 n (p - 1) = a at *
    generalize ca163 n p = b at *
    generalize ca163 n (p + 1) = c at *
    simp only [dot] at *
    cases a <;> cases b <;> cases c <;> simp [rule163] at * <;> push_cast <;> try omega

def c (k : ℕ) : ℕ := if k = 0 then 1 else if k = 1 then 0 else if k % 2 = 1 then 1 else 0

def T (m : ℕ) : ℕ := ∑ k ∈ Finset.range (m + 1), c k * 2 ^ (m - k)

theorem T_succ (m : ℕ) : T (m + 1) = 2 * T m + c (m + 1) := by
  unfold T
  rw [Finset.sum_range_succ, Finset.mul_sum]
  simp only [Nat.sub_self, pow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have : k ≤ m := by simp at hk; omega
  rw [show m + 1 - k = (m - k) + 1 by omega, pow_succ]
  ring

theorem T_even (n : ℕ) : 6 * T (2 * (n + 1)) + 4 = 7 * 4 ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show 2 * (n + 1 + 1) = (2 * (n + 1) + 1) + 1 by ring, T_succ, T_succ]
    have h1 : c (2 * (n + 1) + 1 + 1) = 0 := by unfold c; split_ifs <;> omega
    have h2 : c (2 * (n + 1) + 1) = 1 := by unfold c; split_ifs <;> omega
    rw [h1, h2, pow_succ]
    omega

theorem A_eq (n : ℕ) (hn : 1 ≤ n) : A266753 n = T (2 * n) := by
  unfold A266753 T
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  have h := pat n hn ((k : ℤ) - n)
  have hk' : k < 2 * n + 1 := Finset.mem_range.mp hk
  by_cases hb : ca163 n ((k : ℤ) - n) = true
  · rw [if_pos hb]
    have := h.1 hb
    unfold dot at this
    unfold c
    split_ifs <;> omega
  · rw [if_neg hb]
    have : ¬¬ dot n ((k : ℤ) - n) := fun hh => hb (h.2 hh)
    have := not_not.mp this
    unfold dot at this
    unfold c
    split_ifs <;> omega

end OMA.S_oeis_a392003

theorem OMA.solution : type_of% @OMA.S_oeis_a392003.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [OMA.S_oeis_a392003.A_eq (m + 1) hn]
  have h := OMA.S_oeis_a392003.T_even m
  generalize OMA.S_oeis_a392003.T (2 * (m + 1)) = t at *
  unfold OMA.S_oeis_a392003.a
  rw [show 2 * (m + 1) = 2 * (m + 1) from rfl, pow_mul]
  have h4 : ((2 : ℤ) ^ 2) ^ (m + 1) = 4 ^ (m + 1) := by norm_num
  rw [h4]
  have h' : (6 : ℤ) * t + 4 = 7 * 4 ^ (m + 1) := by exact_mod_cast h
  have hn1 : (-1 : ℤ) ^ (2 * (m + 1)) = 1 := by rw [pow_mul]; norm_num
  rw [hn1]
  omega
