import OMAStatements.S_oeis_a325525

namespace OMA.S_oeis_a325525

theorem sel_iff (n : ℕ) : selected n ↔ 0 < n ∧ ¬ (3 ∣ n ∧ selected (n / 3)) ∧ ¬ (4 ∣ n ∧ selected (n / 4)) := by
  rw [selected]
  by_cases h : 0 < n <;> simp [h]

theorem sel_of {n : ℕ} (h3 : n % 3 ≠ 0) (h4 : n % 4 ≠ 0) (h0 : 0 < n) : selected n := by
  rw [sel_iff]
  refine ⟨h0, ?_, ?_⟩
  · rintro ⟨h, -⟩; omega
  · rintro ⟨h, -⟩; omega

def C (z : ℕ) : Prop :=
  (z % 3 = 0 ∧ (z / 3) % 3 ≠ 0 ∧ (z / 3) % 4 ≠ 0) ∨ (z % 4 = 0 ∧ (z / 4) % 3 ≠ 0 ∧ (z / 4) % 4 ≠ 0)

instance (z : ℕ) : Decidable (C z) := by unfold C; infer_instance

theorem nsel_of {z : ℕ} (h : C z) (h0 : 0 < z) : ¬ selected z := by
  rw [sel_iff]
  rintro ⟨-, h3, h4⟩
  rcases h with ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact h3 ⟨by omega, sel_of b c (by omega)⟩
  · exact h4 ⟨by omega, sel_of b c (by omega)⟩

set_option maxRecDepth 100000 in
theorem win9 : ∀ x : ℕ, ∃ d, 1 ≤ d ∧ d ≤ 9 ∧ C (x + d) := by
  have h : ∀ r : ℕ, r < 144 → ∃ d, d < 10 ∧ 1 ≤ d ∧ C (r + d) := by decide
  intro x
  obtain ⟨d, hd2, hd1, hC⟩ := h (x % 144) (Nat.mod_lt _ (by omega))
  refine ⟨d, hd1, by omega, ?_⟩
  unfold C at hC ⊢
  omega

set_option maxRecDepth 100000 in
theorem win8 : ∀ x : ℕ, (∃ d, 1 ≤ d ∧ d ≤ 7 ∧ C (x + d)) ∨
    (x % 3 ≠ 0 ∧ x % 4 ≠ 0) ∨ ((x + 8) % 3 ≠ 0 ∧ (x + 8) % 4 ≠ 0) := by
  have h : ∀ r : ℕ, r < 144 → (∃ d, d < 8 ∧ 1 ≤ d ∧ C (r + d)) ∨
      ((r % 3 ≠ 0 ∧ r % 4 ≠ 0) ∨ ((r + 8) % 3 ≠ 0 ∧ (r + 8) % 4 ≠ 0)) := by decide
  intro x
  rcases h (x % 144) (Nat.mod_lt _ (by omega)) with ⟨d, hd2, hd1, hC⟩ | h2
  · refine Or.inl ⟨d, hd1, by omega, ?_⟩
    unfold C at hC ⊢
    omega
  · right
    omega

end OMA.S_oeis_a325525

theorem OMA.solution : type_of% @OMA.S_oeis_a325525.main := by
  intro x y ⟨hxy, hx, hy, hz⟩
  refine ⟨by omega, ?_, ?_⟩
  · by_contra hc
    obtain ⟨d, h1, h4, hC⟩ := OMA.S_oeis_a325525.win9 x
    exact hz (x + d) (by omega) (by omega)
      ⟨by omega, OMA.S_oeis_a325525.nsel_of hC (by omega)⟩
  · intro h8
    rcases OMA.S_oeis_a325525.win8 x with ⟨d, h1, h7, hC⟩ | h | h
    · exact hz (x + d) (by omega) (by omega)
        ⟨by omega, OMA.S_oeis_a325525.nsel_of hC (by omega)⟩
    · exact hx.2 (OMA.S_oeis_a325525.sel_of h.1 h.2 hx.1)
    · have : y = x + 8 := by omega
      subst this
      exact hy.2 (OMA.S_oeis_a325525.sel_of h.1 h.2 hy.1)
