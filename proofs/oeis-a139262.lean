import OMAStatements.S_oeis_a139262
import Mathlib

open OMA.S_oeis_a139262 in
theorem OMA.solution : type_of% @OMA.S_oeis_a139262.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have c (j : ℕ) : ((j:ℤ)+1) * (j+1).centralBinom = 2*(2*j+1)*j.centralBinom :=
    mod_cast Nat.succ_mul_centralBinom_succ j
  have h (j : ℕ) : 2 * a j = (j+1) * j.centralBinom - 4^j := by
    rcases j with _ | j
    · simp [a]
    · obtain ⟨c, hc⟩ := Nat.two_dvd_centralBinom_succ j
      exact Int.mul_ediv_cancel' ⟨(j+2)*c - 2*4^j, by rw [hc, pow_succ]; push_cast; ring⟩
  have c1 := c (k+1)
  have h2 := h (k+2)
  have h1 := h (k+1)
  simp [add_assoc] at c1 h1 h2 ⊢
  exact mul_left_cancel₀ two_ne_zero (by
    linear_combination (k+2:ℤ)*k*h2 + 2*(-4*(k+2:ℤ)^2+9*(k+2)-3)*h1 + 8*(k+1:ℤ)*(2*k+1)*h k
      + (k:ℤ)*(k+3)*c1 - 4*(k+1:ℤ)^2*c k)
