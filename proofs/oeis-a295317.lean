import OMAStatements.S_oeis_a295317
import Mathlib

/-!
# A295317: Barker's recurrence

The selected i are the odd i ≤ m = floor((n−1)/2), i.e. 1, 3, ..., 2K − 1 with K = floor((m+1)/2), so a(n) = n·K² − K(4K² − 1)/3 (induction on m, in ℚ).
Since K grows by 1 when n grows by 4, the third difference with step 4,
a(n) − 3a(n−4) + 3a(n−8) − a(n−12), is the same constant for every n; the recurrence is the
difference of this identity at n and at n − 1, checked by substituting the closed form.
-/

namespace PA295317

theorem partialSum (n m : ℕ) (hm : m ≤ n) :
    ((∑ i ∈ Finset.Icc 1 m, i * (n - i) * (i % 2) : ℕ) : ℚ) = (n : ℚ) * (((m + 1) / 2 : ℕ) : ℚ) ^ 2 - (((m + 1) / 2 : ℕ) : ℚ) * (4 * (((m + 1) / 2 : ℕ) : ℚ) ^ 2 - 1) / 3 := by
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

theorem closed (x : ℕ) : (OMA.S_oeis_a295317.a x : ℚ) = ((x : ℕ) : ℚ) * (((((x) - 1) / 2 + 1) / 2 : ℕ) : ℚ) ^ 2 - (((((x) - 1) / 2 + 1) / 2 : ℕ) : ℚ) * (4 * (((((x) - 1) / 2 + 1) / 2 : ℕ) : ℚ) ^ 2 - 1) / 3 := by
  unfold OMA.S_oeis_a295317.a
  exact partialSum x ((x - 1) / 2) (by omega)

end PA295317

open OMA.S_oeis_a295317 in
theorem OMA.solution : type_of% @OMA.S_oeis_a295317.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
  rw [show m + 13 - 1 = m + 12 by omega, show m + 13 - 4 = m + 9 by omega,
    show m + 13 - 5 = m + 8 by omega, show m + 13 - 8 = m + 5 by omega,
    show m + 13 - 9 = m + 4 by omega, show m + 13 - 12 = m + 1 by omega,
    show m + 13 - 13 = m by omega]
  have key : ((a (m + 13) : ℤ) : ℚ) = (((a (m + 12) : ℤ) + 3 * a (m + 9) -
      3 * a (m + 8) - 3 * a (m + 5) + 3 * a (m + 4) + a (m + 1) -
      a m : ℤ) : ℚ) := by
    push_cast
    rw [PA295317.closed, PA295317.closed, PA295317.closed, PA295317.closed, PA295317.closed, PA295317.closed, PA295317.closed,
      PA295317.closed]
    rw [show (((m + 13) - 1) / 2 + 1) / 2 = (((m + 1) - 1) / 2 + 1) / 2 + 3 by omega,
      show (((m + 9) - 1) / 2 + 1) / 2 = (((m + 1) - 1) / 2 + 1) / 2 + 2 by omega,
      show (((m + 5) - 1) / 2 + 1) / 2 = (((m + 1) - 1) / 2 + 1) / 2 + 1 by omega,
      show (((m + 12) - 1) / 2 + 1) / 2 = (((m) - 1) / 2 + 1) / 2 + 3 by omega,
      show (((m + 8) - 1) / 2 + 1) / 2 = (((m) - 1) / 2 + 1) / 2 + 2 by omega,
      show (((m + 4) - 1) / 2 + 1) / 2 = (((m) - 1) / 2 + 1) / 2 + 1 by omega]
    generalize (((m + 1) - 1) / 2 + 1) / 2 = A
    generalize (((m) - 1) / 2 + 1) / 2 = B
    push_cast
    ring
  exact_mod_cast key
