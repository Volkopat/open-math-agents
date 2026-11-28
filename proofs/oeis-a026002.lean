import OMAStatements.S_oeis_a026002

/-! Proof. `2·mm i j = D(i, j+2) + D(i+2, j)`: on the boundary this is `D(i,2) = 2i²+2i+1`
(and its mirror), inside both sides satisfy the same three-term recurrence. On the diagonal the
symmetry `D(i,j) = D(j,i)` gives `mm (n-1) (n-1) = D(n-1, n+1)`. -/

namespace OMA.S_oeis_a026002

lemma D_zero_right (i : ℕ) : D i 0 = 1 := by
  cases i <;> simp [D]

lemma D_succ (i j : ℕ) : D (i+1) (j+1) = D i (j+1) + D i j + D (i+1) j := by
  simp [D]

lemma D_one (i : ℕ) : D i 1 = 2 * i + 1 := by
  induction i with
  | zero => simp [D]
  | succ i ih => rw [D_succ, ih, D_zero_right, D_zero_right]; ring

lemma D_two (i : ℕ) : D i 2 = 2 * i * i + 2 * i + 1 := by
  induction i with
  | zero => simp [D]
  | succ i ih => rw [D_succ, ih, D_one, D_one]; ring

lemma D_symm : ∀ i j : ℕ, D i j = D j i
  | 0, j => by rw [D_zero_right]; simp [D]
  | i + 1, 0 => by rw [D_zero_right]; simp [D]
  | i + 1, j + 1 => by
    rw [D_succ, D_succ, D_symm i (j+1), D_symm i j, D_symm (i+1) j]; ring

lemma key : ∀ i j : ℕ, 2 * mm i j = D i (j+2) + D (i+2) j
  | i, 0 => by
    simp only [mm]; rw [D_two, D_zero_right]; ring
  | 0, j + 1 => by
    simp only [mm]; rw [D_symm 2 (j+1), D_two]; simp [D]; ring
  | i + 1, j + 1 => by
    simp only [mm]
    have h1 := key (i+1) j
    have h2 := key i j
    have h3 := key i (j+1)
    have e1 : D (i+1) (j+1+2) = D i (j+3) + D i (j+2) + D (i+1) (j+2) := D_succ i (j+2)
    have e2 : D (i+1+2) (j+1) = D (i+2) (j+1) + D (i+2) j + D (i+3) j := D_succ (i+2) j
    rw [e1, e2]
    linear_combination h1 + h2 + h3

theorem solution_main : ∀ n : ℕ, 1 ≤ n → m n n = a n := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [m, a, Nat.add_sub_cancel]
  have h := key k k
  rw [D_symm (k+2) k] at h
  have : D k (k + 1 + 1) = D k (k+2) := rfl
  rw [this]
  omega

end OMA.S_oeis_a026002

theorem OMA.solution : type_of% @OMA.S_oeis_a026002.main := OMA.S_oeis_a026002.solution_main
