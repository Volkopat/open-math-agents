import OMAStatements.S_oeis_a296159
import Mathlib

/-!
# A296159: Barker's recurrence

Depending on the parity of n, the factor (n − i) mod 2 (resp. (n − i + 1) mod 2) selects either
the even or the odd i ≤ floor((n−1)/2). The even i ≤ M sum to K(K+1) with K = floor(M/2), and the
odd i ≤ M sum to K² with K = floor((M+1)/2) (induction on M). In each parity class K grows by 1
when n grows by 4, so a(n) − 2a(n−4) + a(n−8) = 2 for every n ≥ 9; the recurrence is the
difference of this identity at n and at n − 1.
-/

namespace PA296159

theorem evenSum (m : ℕ) :
    ((∑ i ∈ Finset.Icc 1 m, i * ((i + 1) % 2) : ℕ) : ℤ) =
      ((m / 2 : ℕ) : ℤ) * (((m / 2 : ℕ) : ℤ) + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, ih, Nat.cast_mul]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · rw [show (m + 1 + 1) % 2 = 0 by omega, show (m + 1) / 2 = m / 2 by omega]
      generalize m / 2 = K
      push_cast
      ring
    · have e : (m : ℤ) + 1 = 2 * ((m / 2 : ℕ) : ℤ) + 2 := by
        have : m + 1 = 2 * (m / 2) + 2 := by omega
        exact_mod_cast this
      rw [show (m + 1 + 1) % 2 = 1 by omega, show (m + 1) / 2 = m / 2 + 1 by omega]
      generalize m / 2 = K at e ⊢
      push_cast
      linear_combination e

theorem oddSum (m : ℕ) :
    ((∑ i ∈ Finset.Icc 1 m, i * (i % 2) : ℕ) : ℤ) = (((m + 1) / 2 : ℕ) : ℤ) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, ih, Nat.cast_mul]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · have e : (m : ℤ) + 1 = 2 * (((m + 1) / 2 : ℕ) : ℤ) + 1 := by
        have : m + 1 = 2 * ((m + 1) / 2) + 1 := by omega
        exact_mod_cast this
      rw [show (m + 1) % 2 = 1 by omega, show (m + 1 + 1) / 2 = (m + 1) / 2 + 1 by omega]
      generalize (m + 1) / 2 = K at e ⊢
      push_cast
      linear_combination e
    · rw [show (m + 1) % 2 = 0 by omega, show (m + 1 + 1) / 2 = (m + 1) / 2 by omega]
      generalize (m + 1) / 2 = K
      push_cast
      ring

theorem closed (x : ℕ) :
    (OMA.S_oeis_a296159.a x : ℤ) = if x % 2 = 1 then (((((x) - 1) / 2 / 2 : ℕ) : ℤ) * (((((x) - 1) / 2 / 2 : ℕ) : ℤ) + 1)) else (((((x) - 1) / 2 + 1) / 2 : ℕ) : ℤ) ^ 2 := by
  unfold OMA.S_oeis_a296159.a
  split_ifs with hx
  · have h : ∀ i ∈ Finset.Icc 1 ((x - 1) / 2), i * ((x - i) % 2) =
        i * ((i + 1) % 2) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      congr 1
      omega
    rw [Finset.sum_congr rfl h, evenSum]
  · have h : ∀ i ∈ Finset.Icc 1 ((x - 1) / 2), i * ((x - i) % 2) =
        i * (i % 2) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      congr 1
      omega
    rw [Finset.sum_congr rfl h, oddSum]

end PA296159

theorem OMA.solution : type_of% @OMA.S_oeis_a296159.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  rw [show m + 9 - 1 = m + 8 by omega, show m + 9 - 4 = m + 5 by omega,
    show m + 9 - 5 = m + 4 by omega, show m + 9 - 8 = m + 1 by omega, show m + 9 - 9 = m by omega,
    PA296159.closed, PA296159.closed, PA296159.closed, PA296159.closed, PA296159.closed, PA296159.closed]
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · rw [if_pos (show (m + 9) % 2 = 1 by omega), if_neg (show ¬ (m + 8) % 2 = 1 by omega),
      if_pos (show (m + 5) % 2 = 1 by omega), if_neg (show ¬ (m + 4) % 2 = 1 by omega),
      if_pos (show (m + 1) % 2 = 1 by omega), if_neg (show ¬ m % 2 = 1 by omega)]
    rw [show (m + 9 - 1) / 2 / 2 = (m + 1 - 1) / 2 / 2 + 2 by omega,
      show (m + 5 - 1) / 2 / 2 = (m + 1 - 1) / 2 / 2 + 1 by omega,
      show ((m + 8 - 1) / 2 + 1) / 2 = ((m - 1) / 2 + 1) / 2 + 2 by omega,
      show ((m + 4 - 1) / 2 + 1) / 2 = ((m - 1) / 2 + 1) / 2 + 1 by omega]
    generalize (m + 1 - 1) / 2 / 2 = A
    generalize ((m + 1 - 1) / 2 + 1) / 2 = B
    generalize (m - 1) / 2 / 2 = C
    generalize ((m - 1) / 2 + 1) / 2 = D
    push_cast
    ring
  · rw [if_neg (show ¬ (m + 9) % 2 = 1 by omega), if_pos (show (m + 8) % 2 = 1 by omega),
      if_neg (show ¬ (m + 5) % 2 = 1 by omega), if_pos (show (m + 4) % 2 = 1 by omega),
      if_neg (show ¬ (m + 1) % 2 = 1 by omega), if_pos (show m % 2 = 1 by omega)]
    rw [show ((m + 9 - 1) / 2 + 1) / 2 = ((m + 1 - 1) / 2 + 1) / 2 + 2 by omega,
      show ((m + 5 - 1) / 2 + 1) / 2 = ((m + 1 - 1) / 2 + 1) / 2 + 1 by omega,
      show (m + 8 - 1) / 2 / 2 = (m - 1) / 2 / 2 + 2 by omega,
      show (m + 4 - 1) / 2 / 2 = (m - 1) / 2 / 2 + 1 by omega]
    generalize (m + 1 - 1) / 2 / 2 = A
    generalize ((m + 1 - 1) / 2 + 1) / 2 = B
    generalize (m - 1) / 2 / 2 = C
    generalize ((m - 1) / 2 + 1) / 2 = D
    push_cast
    ring
