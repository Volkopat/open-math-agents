import OMAStatements.S_oeis_a111942
import Mathlib

/-!
# A111942: Mathar's recurrence for `(-1)^(n-1) ⌊(n-1)/2⌋! ⌊n/2⌋!`

Split by parity.

* `n = 2m + 3`: `a n = (m+1)!²`, `a (n-1) = -m! (m+1)!`, `a (n-2) = m!²`, and
  `4 (m+1)² - 2 (m+1) - (2m+2)(2m+1) = 0`.
* `n = 2m + 4`: `a n = -(m+1)! (m+2)!`, `a (n-1) = (m+1)!²`, `a (n-2) = -m! (m+1)!`, and
  `-4 (m+1)(m+2) + 2 (m+1) + (2m+3)(2m+2) = 0`.
-/

open OMA.S_oeis_a111942 in
theorem OMA.solution : type_of% @OMA.S_oeis_a111942.main := by
  -- closed forms on the two parity classes
  have hodd : ∀ m : ℕ, a (2 * m + 1) = (m.factorial : ℤ) * (m.factorial : ℤ) := by
    intro m
    unfold a
    rw [if_neg (by omega)]
    have e1 : 2 * m + 1 - 1 = 2 * m := by omega
    have e2 : 2 * m / 2 = m := by omega
    have e3 : (2 * m + 1) / 2 = m := by omega
    rw [e1, e2, e3, pow_mul]
    norm_num
  have heven : ∀ m : ℕ, a (2 * m + 2) = -((m.factorial : ℤ) * ((m + 1).factorial : ℤ)) := by
    intro m
    unfold a
    rw [if_neg (by omega)]
    have e1 : 2 * m + 2 - 1 = 2 * m + 1 := by omega
    have e2 : (2 * m + 1) / 2 = m := by omega
    have e3 : (2 * m + 2) / 2 = m + 1 := by omega
    rw [e1, e2, e3, pow_succ, pow_mul]
    norm_num
  intro n hn
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · -- `n = 2k`, `k ≥ 2`
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have e0 : 2 * (m + 2) = 2 * (m + 1) + 2 := by ring
    have e1 : 2 * (m + 2) - 1 = 2 * (m + 1) + 1 := by omega
    have e2 : 2 * (m + 2) - 2 = 2 * m + 2 := by omega
    rw [e1, e2, hodd, heven, e0, heven]
    have f1 : ((m + 1).factorial : ℤ) = ((m : ℤ) + 1) * (m.factorial : ℤ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have f2 : ((m + 1 + 1).factorial : ℤ) = ((m : ℤ) + 2) * ((m : ℤ) + 1) * (m.factorial : ℤ) := by
      rw [Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    rw [f2, f1]
    push_cast
    ring
  · -- `n = 2k + 1`, `k ≥ 1`
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have e1 : 2 * (m + 1) + 1 - 1 = 2 * m + 2 := by omega
    have e2 : 2 * (m + 1) + 1 - 2 = 2 * m + 1 := by omega
    rw [e1, e2, hodd, heven, hodd]
    have f1 : ((m + 1).factorial : ℤ) = ((m : ℤ) + 1) * (m.factorial : ℤ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [f1]
    push_cast
    ring
