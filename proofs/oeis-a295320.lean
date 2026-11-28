import OMAStatements.S_oeis_a295320
import Mathlib

/-!
# A295320: Barker's recurrence

Depending on the parity of n, the parity factor selects either the even or the odd i in the
range. The even i ≤ M contribute n·K(K+1) − 2K(K+1)(2K+1)/3 with K = floor(M/2), and the odd
i ≤ M contribute n·K² − K(4K² − 1)/3 with K = floor((M+1)/2) (induction on M, in ℚ). Within each
parity class K grows by 1 when n grows by 4, so the third difference with step 4,
a(n) − 3a(n−4) + 3a(n−8) − a(n−12), is the same constant for both classes, and the recurrence
(its difference at n and n − 1) is checked by substituting the closed forms.
-/

namespace PA295320

theorem evenSum (n m : ℕ) (hm : m ≤ n) :
    ((∑ i ∈ Finset.Icc 1 m, i * (n - i) * ((i + 1) % 2) : ℕ) : ℚ) =
      (n : ℚ) * ((m / 2 : ℕ) : ℚ) * (((m / 2 : ℕ) : ℚ) + 1) -
        2 * ((m / 2 : ℕ) : ℚ) * (((m / 2 : ℕ) : ℚ) + 1) * (2 * ((m / 2 : ℕ) : ℚ) + 1) / 3 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, ih (by omega), Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub (show m + 1 ≤ n by omega)]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · rw [show (m + 1 + 1) % 2 = 0 by omega, show (m + 1) / 2 = m / 2 by omega]
      generalize m / 2 = K
      push_cast
      ring
    · have e : (m : ℚ) + 1 = 2 * (((m / 2 : ℕ)) : ℚ) + 2 := by
        have : m + 1 = 2 * (m / 2) + 2 := by omega
        exact_mod_cast this
      rw [show (m + 1 + 1) % 2 = 1 by omega, show (m + 1) / 2 = m / 2 + 1 by omega]
      generalize m / 2 = K at e ⊢
      push_cast
      rw [e]
      ring

theorem oddSum (n m : ℕ) (hm : m ≤ n) :
    ((∑ i ∈ Finset.Icc 1 m, i * (n - i) * (i % 2) : ℕ) : ℚ) =
      (n : ℚ) * (((m + 1) / 2 : ℕ) : ℚ) ^ 2 -
        (((m + 1) / 2 : ℕ) : ℚ) * (4 * (((m + 1) / 2 : ℕ) : ℚ) ^ 2 - 1) / 3 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, ih (by omega), Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub (show m + 1 ≤ n by omega)]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · have e : (m : ℚ) + 1 = 2 * ((((m + 1) / 2 : ℕ)) : ℚ) + 1 := by
        have : m + 1 = 2 * ((m + 1) / 2) + 1 := by omega
        exact_mod_cast this
      rw [show (m + 1) % 2 = 1 by omega, show (m + 1 + 1) / 2 = (m + 1) / 2 + 1 by omega]
      generalize (m + 1) / 2 = K at e ⊢
      push_cast
      rw [e]
      ring
    · rw [show (m + 1) % 2 = 0 by omega, show (m + 1 + 1) / 2 = (m + 1) / 2 by omega]
      generalize (m + 1) / 2 = K
      push_cast
      ring

theorem closed (x : ℕ) :
    (OMA.S_oeis_a295320.a x : ℚ) = if x % 2 = 1 then (((x : ℕ) : ℚ) * ((((x) - 1) / 2 / 2 : ℕ) : ℚ) * (((((x) - 1) / 2 / 2 : ℕ) : ℚ) + 1) - 2 * ((((x) - 1) / 2 / 2 : ℕ) : ℚ) * (((((x) - 1) / 2 / 2 : ℕ) : ℚ) + 1) * (2 * ((((x) - 1) / 2 / 2 : ℕ) : ℚ) + 1) / 3) else (((x : ℕ) : ℚ) * (((((x) - 1) / 2 + 1) / 2 : ℕ) : ℚ) ^ 2 - (((((x) - 1) / 2 + 1) / 2 : ℕ) : ℚ) * (4 * (((((x) - 1) / 2 + 1) / 2 : ℕ) : ℚ) ^ 2 - 1) / 3) := by
  unfold OMA.S_oeis_a295320.a
  split_ifs with hx
  · have h : ∀ i ∈ Finset.Icc 1 (((x) - 1) / 2), i * (x - i) * ((x - i) % 2) =
        i * (x - i) * ((i + 1) % 2) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      congr 1
      omega
    rw [Finset.sum_congr rfl h, evenSum x _ (by omega)]
  · have h : ∀ i ∈ Finset.Icc 1 (((x) - 1) / 2), i * (x - i) * ((x - i) % 2) =
        i * (x - i) * (i % 2) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      congr 1
      omega
    rw [Finset.sum_congr rfl h, oddSum x _ (by omega)]

end PA295320

theorem OMA.solution : type_of% @OMA.S_oeis_a295320.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
  rw [show m + 13 - 1 = m + 12 by omega, show m + 13 - 4 = m + 9 by omega,
    show m + 13 - 5 = m + 8 by omega, show m + 13 - 8 = m + 5 by omega,
    show m + 13 - 9 = m + 4 by omega, show m + 13 - 12 = m + 1 by omega,
    show m + 13 - 13 = m by omega]
  have key : ((OMA.S_oeis_a295320.a (m + 13) : ℤ) : ℚ) = (((OMA.S_oeis_a295320.a (m + 12) : ℤ) + 3 * OMA.S_oeis_a295320.a (m + 9) -
      3 * OMA.S_oeis_a295320.a (m + 8) - 3 * OMA.S_oeis_a295320.a (m + 5) + 3 * OMA.S_oeis_a295320.a (m + 4) + OMA.S_oeis_a295320.a (m + 1) -
      OMA.S_oeis_a295320.a m : ℤ) : ℚ) := by
    push_cast
    rw [PA295320.closed, PA295320.closed, PA295320.closed, PA295320.closed, PA295320.closed, PA295320.closed, PA295320.closed,
      PA295320.closed]
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm
    · rw [if_pos (show (m + 13) % 2 = 1 by omega),
        if_neg (show ¬ (m + 12) % 2 = 1 by omega),
        if_pos (show (m + 9) % 2 = 1 by omega),
        if_neg (show ¬ (m + 8) % 2 = 1 by omega),
        if_pos (show (m + 5) % 2 = 1 by omega),
        if_neg (show ¬ (m + 4) % 2 = 1 by omega),
        if_pos (show (m + 1) % 2 = 1 by omega),
        if_neg (show ¬ (m) % 2 = 1 by omega)]
      rw [show ((m + 13) - 1) / 2 / 2 = ((m + 1) - 1) / 2 / 2 + 3 by omega,
        show ((m + 9) - 1) / 2 / 2 = ((m + 1) - 1) / 2 / 2 + 2 by omega,
        show ((m + 5) - 1) / 2 / 2 = ((m + 1) - 1) / 2 / 2 + 1 by omega,
        show (((m + 12) - 1) / 2 + 1) / 2 = (((m) - 1) / 2 + 1) / 2 + 3 by omega,
        show (((m + 8) - 1) / 2 + 1) / 2 = (((m) - 1) / 2 + 1) / 2 + 2 by omega,
        show (((m + 4) - 1) / 2 + 1) / 2 = (((m) - 1) / 2 + 1) / 2 + 1 by omega]
      generalize ((m + 1) - 1) / 2 / 2 = A
      generalize (((m) - 1) / 2 + 1) / 2 = B
      push_cast
      ring
    · rw [if_neg (show ¬ (m + 13) % 2 = 1 by omega),
        if_pos (show (m + 12) % 2 = 1 by omega),
        if_neg (show ¬ (m + 9) % 2 = 1 by omega),
        if_pos (show (m + 8) % 2 = 1 by omega),
        if_neg (show ¬ (m + 5) % 2 = 1 by omega),
        if_pos (show (m + 4) % 2 = 1 by omega),
        if_neg (show ¬ (m + 1) % 2 = 1 by omega),
        if_pos (show (m) % 2 = 1 by omega)]
      rw [show (((m + 13) - 1) / 2 + 1) / 2 = (((m + 1) - 1) / 2 + 1) / 2 + 3 by omega,
        show (((m + 9) - 1) / 2 + 1) / 2 = (((m + 1) - 1) / 2 + 1) / 2 + 2 by omega,
        show (((m + 5) - 1) / 2 + 1) / 2 = (((m + 1) - 1) / 2 + 1) / 2 + 1 by omega,
        show ((m + 12) - 1) / 2 / 2 = ((m) - 1) / 2 / 2 + 3 by omega,
        show ((m + 8) - 1) / 2 / 2 = ((m) - 1) / 2 / 2 + 2 by omega,
        show ((m + 4) - 1) / 2 / 2 = ((m) - 1) / 2 / 2 + 1 by omega]
      generalize (((m + 1) - 1) / 2 + 1) / 2 = A
      generalize ((m) - 1) / 2 / 2 = B
      push_cast
      ring
  exact_mod_cast key
