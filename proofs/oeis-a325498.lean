import OMAStatements.S_oeis_a325498

namespace OMA.S_oeis_a325498

theorem sel_iff (n : ℕ) : selected n ↔ 0 < n ∧ ¬ (2 ∣ n ∧ selected (n / 2)) ∧ ¬ (3 ∣ n ∧ selected (n / 3)) := by
  rw [selected]
  by_cases h : 0 < n <;> simp [h]

theorem sel_of {n : ℕ} (h2 : n % 2 ≠ 0) (h3 : n % 3 ≠ 0) (h0 : 0 < n) : selected n := by
  rw [sel_iff]
  refine ⟨h0, ?_, ?_⟩
  · rintro ⟨h, -⟩; omega
  · rintro ⟨h, -⟩; omega

theorem win : ∀ x : ℕ, ∃ d, 1 ≤ d ∧ d ≤ 4 ∧ (x + d) % 2 ≠ 0 ∧ (x + d) % 3 ≠ 0 := by
  have h : ∀ r : ℕ, r < 6 → ∃ d, d < 5 ∧ 1 ≤ d ∧ (r + d) % 2 ≠ 0 ∧ (r + d) % 3 ≠ 0 := by decide
  intro x
  obtain ⟨d, hd2, hd1, h2, h3⟩ := h (x % 6) (Nat.mod_lt _ (by omega))
  exact ⟨d, hd1, by omega, by omega, by omega⟩

end OMA.S_oeis_a325498

theorem OMA.solution : type_of% @OMA.S_oeis_a325498.main := by
  intro x y ⟨hxy, hx, hy, hz⟩
  refine ⟨by omega, ?_⟩
  by_contra hc
  obtain ⟨d, h1, h4, h2, h3⟩ := OMA.S_oeis_a325498.win x
  exact hz (x + d) (by omega) (by omega)
    (OMA.S_oeis_a325498.sel_of h2 h3 (by omega))
