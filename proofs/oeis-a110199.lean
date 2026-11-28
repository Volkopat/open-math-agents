import OMAStatements.S_oeis_a110199
import Mathlib

open OMA.S_oeis_a110199 in
theorem OMA.solution : type_of% @OMA.S_oeis_a110199.main := by
  intro n hn
  obtain ⟨i, rfl | rfl⟩ : ∃ i, n = 2*i+3 ∨ n = 2*i+4 := ⟨(n-3)/2, by omega⟩
  · simp [a, show ∀ c, (2*i+c)/2 = i+c/2 by omega]
    ring
  · have h1 := succ_mul_catalan_eq_centralBinom (i+2)
    have h2 := succ_mul_catalan_eq_centralBinom (i+1)
    have h3 := Nat.succ_mul_centralBinom_succ (i+1)
    zify at h1 h2 h3
    simp [a, show ∀ c, (2*i+c)/2 = i+c/2 by omega, Finset.sum_range_succ, add_assoc] at h1 h2 h3 ⊢
    refine mul_left_cancel₀ (by positivity : (i:ℤ)+2 ≠ 0) ?_
    linear_combination -2*((i+2)*h1 + h3 - 2*(2*i+3)*h2)
