import OMAStatements.S_oeis_a171556
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a171556.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have p (j : ℕ) : 2 ≤ 3 * catalan j := by
    have := succ_mul_catalan_eq_centralBinom j
    have := j.centralBinom_pos
    rcases (catalan j).eq_zero_or_pos with h | h
    · simp_all
    · omega
  have r (j : ℕ) : ((j:ℤ)+2) * catalan (j+1) = 2*(2*j+1) * catalan j := by
    have h1 := succ_mul_catalan_eq_centralBinom (j+1)
    have h2 := succ_mul_catalan_eq_centralBinom j
    have h3 := j.succ_mul_centralBinom_succ
    zify at h1 h2 h3
    exact mul_left_cancel₀ (by positivity : (j:ℤ)+1 ≠ 0) (by linear_combination (j+1)*h1 + h3 - 2*(2*j+1)*h2)
  have r1 := r (k+1)
  simp [OMA.S_oeis_a171556.a, p, Nat.cast_sub, add_assoc] at r1 ⊢
  linear_combination 3*k*r1 - (3*k+3)*r k
