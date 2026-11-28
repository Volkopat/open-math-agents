import OMAStatements.S_oeis_a325524

namespace OMA.S_oeis_a325524

theorem sel_iff (n : ℕ) : selected n ↔ 0 < n ∧ ¬ (3 ∣ n ∧ selected (n / 3)) ∧ ¬ (4 ∣ n ∧ selected (n / 4)) := by
  rw [selected]
  by_cases h : 0 < n <;> simp [h]

theorem sel_of {n : ℕ} (h3 : n % 3 ≠ 0) (h4 : n % 4 ≠ 0) (h0 : 0 < n) : selected n := by
  rw [sel_iff]
  refine ⟨h0, ?_, ?_⟩
  · rintro ⟨h, -⟩; omega
  · rintro ⟨h, -⟩; omega

theorem win : ∀ x : ℕ, ∃ d, 1 ≤ d ∧ d ≤ 3 ∧ (x + d) % 3 ≠ 0 ∧ (x + d) % 4 ≠ 0 := by
  have h : ∀ r : ℕ, r < 12 → ∃ d, d < 4 ∧ 1 ≤ d ∧ (r + d) % 3 ≠ 0 ∧ (r + d) % 4 ≠ 0 := by decide
  intro x
  obtain ⟨d, hd2, hd1, h2, h3⟩ := h (x % 12) (Nat.mod_lt _ (by omega))
  exact ⟨d, hd1, by omega, by omega, by omega⟩

end OMA.S_oeis_a325524

theorem OMA.solution : type_of% @OMA.S_oeis_a325524.main := by
  intro x y ⟨hxy, hx, hy, hz⟩
  refine ⟨by omega, ?_⟩
  by_contra hc
  obtain ⟨d, h1, h4, h2, h3⟩ := OMA.S_oeis_a325524.win x
  exact hz (x + d) (by omega) (by omega)
    (OMA.S_oeis_a325524.sel_of h2 h3 (by omega))
