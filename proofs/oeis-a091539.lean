import OMAStatements.S_oeis_a091539
import Mathlib

open OMA.S_oeis_a091539 in
theorem OMA.solution : type_of% @OMA.S_oeis_a091539.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have d (m : ℕ) : 6 * rescaled (m+2) = numerator (m+2) := Int.mul_ediv_cancel' (by
    obtain ⟨u, hu⟩ : (2:ℤ) ∣ q (m+2) := (by norm_num : (2:ℤ) ∣ 3*((1:ℕ):ℤ)+1).trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega)))
    obtain ⟨v, hv⟩ : (2:ℤ) ∣ (m+2).factorial := mod_cast Nat.dvd_factorial two_pos (by omega)
    exact ⟨3^(m+1)*v - u, by rw [numerator, hu, hv]; ring⟩)
  have e (m : ℕ) : 10 * factor (m+2) = block (m+2) := Int.mul_ediv_cancel' (by
    simp [block, Finset.prod_range_succ', mul_assoc])
  have h2 := d (k+2)
  have h1 := d (k+1)
  have h0 := d k
  have g2 := e (k+2)
  have g1 := e (k+1)
  have g0 := e k
  simp only [a, add_assoc, Nat.reduceAdd, Nat.reduceSubDiff] at *
  refine mul_left_cancel₀ (by norm_num : (60:ℤ) ≠ 0) ?_
  linear_combination (norm := skip) (10*factor (k+4)*h2 + numerator (k+4)*g2) - (3*(k+4:ℤ)-1)*(6*(k+4:ℤ)-5)*(10*factor (k+3)*h1 + numerator (k+3)*g1) + 3*(3*(k+4:ℤ)-5)*(k+3:ℤ)*(3*(k+4:ℤ)-1)*(3*(k+4:ℤ)-4)*(10*factor (k+2)*h0 + numerator (k+2)*g0)
  simp [numerator, block, q, Finset.prod_range_succ, Nat.factorial_succ]
  ring
