import OMAStatements.S_oeis_a091540

open OMA.S_oeis_a091540 in
theorem OMA.solution : type_of% @OMA.S_oeis_a091540.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have d (m : ℕ) : 6 * a (m+2) = numerator (m+2) := Int.mul_ediv_cancel' (by
    obtain ⟨u, hu⟩ : (2:ℤ) ∣ q (m+2) := (by norm_num : (2:ℤ) ∣ 3*((1:ℕ):ℤ)+1).trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega)))
    obtain ⟨v, hv⟩ : (2:ℤ) ∣ (m+2).factorial := mod_cast Nat.dvd_factorial two_pos (by omega)
    exact ⟨3^(m+1)*v - u, by rw [numerator, hu, hv]; ring⟩)
  have h2 := d (k+2)
  have h1 := d (k+1)
  have h0 := d k
  simp [numerator, q, Finset.prod_range_succ, Nat.factorial_succ, add_assoc] at h0 h1 h2 ⊢
  refine mul_left_cancel₀ (by norm_num : (6:ℤ) ≠ 0) ?_
  linear_combination h2 + (-6*(k+4:ℤ)+5)*h1 + 3*(k+3:ℤ)*(3*k+7)*h0
