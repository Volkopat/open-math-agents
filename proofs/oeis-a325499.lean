import OMAStatements.S_oeis_a325499

namespace OMA.S_oeis_a325499

theorem sel_iff (n : ℕ) : selected n ↔ 0 < n ∧ ¬ (2 ∣ n ∧ selected (n / 2)) ∧ ¬ (3 ∣ n ∧ selected (n / 3)) := by
  rw [selected]
  by_cases h : 0 < n <;> simp [h]

theorem sel_of {n : ℕ} (h2 : n % 2 ≠ 0) (h3 : n % 3 ≠ 0) (h0 : 0 < n) : selected n := by
  rw [sel_iff]
  refine ⟨h0, ?_, ?_⟩
  · rintro ⟨h, -⟩; omega
  · rintro ⟨h, -⟩; omega

def C (z : ℕ) : Prop := (z % 4 = 2 ∧ z % 3 ≠ 0) ∨ (z % 6 = 3 ∧ z % 9 ≠ 0)

instance (z : ℕ) : Decidable (C z) := by unfold C; infer_instance

theorem nsel_of {z : ℕ} (h : C z) : ¬ selected z := by
  rw [sel_iff]
  rintro ⟨h0, h2, h3⟩
  rcases h with ⟨a, b⟩ | ⟨a, b⟩
  · apply h2
    refine ⟨by omega, ?_⟩
    exact sel_of (by omega) (by omega) (by omega)
  · apply h3
    refine ⟨by omega, ?_⟩
    exact sel_of (by omega) (by omega) (by omega)

theorem win : ∀ x : ℕ, ∃ d, 1 ≤ d ∧ d ≤ 7 ∧ C (x + d) := by
  have h : ∀ r : ℕ, r < 36 → ∃ d, d < 8 ∧ 1 ≤ d ∧ C (r + d) := by decide
  intro x
  obtain ⟨d, hd2, hd1, hC⟩ := h (x % 36) (Nat.mod_lt _ (by omega))
  refine ⟨d, hd1, by omega, ?_⟩
  unfold C at hC ⊢
  omega

end OMA.S_oeis_a325499

theorem OMA.solution : type_of% @OMA.S_oeis_a325499.main := by
  intro x y ⟨hxy, hx, hy, hz⟩
  refine ⟨by omega, ?_⟩
  by_contra hc
  obtain ⟨d, h1, h4, hC⟩ := OMA.S_oeis_a325499.win x
  exact hz (x + d) (by omega) (by omega)
    ⟨by omega, OMA.S_oeis_a325499.nsel_of hC⟩
