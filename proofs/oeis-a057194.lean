import OMAStatements.S_oeis_a057194

open OMA.S_oeis_a057194 in
lemma OMA.key_a057194 : ∀ n : ℕ, 1 ≤ a (n + 1) ∧ a (n + 1) ≤ b (n + 1) ∧
    (1 ≤ n → a (n + 1) < b (n + 1)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [a, b]
    | 1, _ => simp [a, b]
    | m + 2, ih =>
      have ha : a (m + 2 + 1) = (∏ k : Fin (m + 2), a (k + 1)) * ∑ k : Fin (m + 2), a (k + 1) := by
        rw [a]
      have hb : b (m + 2 + 1) = (∏ k : Fin (m + 2), b (k + 1)) * ∑ k : Fin (m + 2), b (k + 1) := by
        rw [b]
      rw [ha, hb]
      have h1 : ∀ k : Fin (m + 2), 1 ≤ a (k + 1) := fun k => (ih k k.isLt).1
      have h2 : ∀ k : Fin (m + 2), a (k + 1) ≤ b (k + 1) := fun k => (ih k k.isLt).2.1
      have hP : ∏ k : Fin (m + 2), a (k + 1) ≤ ∏ k : Fin (m + 2), b (k + 1) :=
        Finset.prod_le_prod' (fun k _ => h2 k)
      have hPa : 1 ≤ ∏ k : Fin (m + 2), a (k + 1) := Finset.one_le_prod' (fun k _ => h1 k)
      have hSa : 1 ≤ ∑ k : Fin (m + 2), a (k + 1) := by
        calc 1 ≤ a ((0 : Fin (m + 2)) + 1) := h1 0
          _ ≤ _ := Finset.single_le_sum (f := fun k : Fin (m + 2) => a (k + 1))
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      have hS : ∑ k : Fin (m + 2), a (k + 1) < ∑ k : Fin (m + 2), b (k + 1) := by
        apply Finset.sum_lt_sum (fun k _ => h2 k)
        refine ⟨⟨1, by omega⟩, Finset.mem_univ _, ?_⟩
        exact (ih 1 (by omega)).2.2 le_rfl
      refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, fun _ => ?_⟩
      · exact Nat.mul_le_mul hP hS.le
      · calc _ ≤ (∏ k : Fin (m + 2), b (k + 1)) * ∑ k : Fin (m + 2), a (k + 1) :=
              Nat.mul_le_mul_right _ hP
          _ < _ := Nat.mul_lt_mul_of_pos_left hS (by omega)

theorem OMA.solution : type_of% @OMA.S_oeis_a057194.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (OMA.key_a057194 m).2.2 (by omega)
