import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1
theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1.H2 := by
  intro h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  obtain ⟨S, hS, hc, hs⟩ := hN (9 * N + 5) (by omega)
  have t : ∀ x ∈ S, x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 3 ∨ x % 9 = 6 := by
    intro x hx
    obtain ⟨k, rfl⟩ := hS x hx
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 18 ∧ k = 18 * q + r := ⟨k / 18, k % 18, by omega, by omega⟩
    dsimp only
    rw [show (18 * q + r) * (18 * q + r + 1) = r * (r + 1) + 2 * (9 * (18 * q * q + q * (2 * r + 1))) by ring,
      Nat.add_mul_div_left _ _ two_pos, Nat.add_mul_mod_self_left]
    interval_cases r <;> simp
  obtain h | h | h : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  · simp_all
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 h
    have := t a (by simp)
    simp at hs
    omega
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.1 h
    have := t a (by simp)
    have := t b (by simp)
    simp at hs
    omega
