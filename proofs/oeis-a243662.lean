import OMAStatements.S_oeis_a243662
import Mathlib

open OMA.S_oeis_a243662 in
theorem OMA.solution : type_of% @OMA.S_oeis_a243662.main := by
  intro n k hk hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  obtain ⟨m, rfl⟩ : ∃ m, n = j+m+1 := ⟨n-j-1, by omega⟩
  simp (disch := omega) [T, A001764, A001263, Nat.cast_choose, show 3*(j+m+1)-j = 2*j+3*m+3 by omega, show 2*j+3*m+3-m = 2*j+2*m+3 by omega, show j+m+1-j = m+1 by omega, show 3*(j+m+1)+1-(j+m+1) = 2*j+2*m+3 by omega, show 3*(j+m+1)-(j+m+1) = 2*j+2*m+2 by omega]
  simp [mul_add, Nat.factorial_succ]
  constructor <;> field_simp <;> ring
