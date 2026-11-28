import Mathlib

namespace OMA.S_oeis_a225894

def lexRow2 (a0 a1 b0 b1 : ℕ) : Prop :=
  a0 < b0 ∨ (a0 = b0 ∧ a1 ≤ b1)

def lexCol (n : ℕ) (f g : Fin n → ℕ) : Prop :=
  f = g ∨ ∃ r : Fin n, (∀ j : Fin n, j.1 < r.1 → f j = g j) ∧ f r < g r

def isLexValid (n : ℕ) (M : Fin n → Fin 2 → ℕ) : Prop :=
  (∀ r : Fin (n - 1), lexRow2 (M ⟨r.1, by omega⟩ 0) (M ⟨r.1, by omega⟩ 1)
                              (M ⟨r.1 + 1, by omega⟩ 0) (M ⟨r.1 + 1, by omega⟩ 1)) ∧
  lexCol n (fun r => M r 0) (fun r => M r 1)

def isValid (n : ℕ) (A : Fin n → Fin 2 → Fin 2) : Prop :=
  ∃ B : Fin n → Fin 2 → Fin 2,
    (∑ r : Fin n, ∑ c : Fin 2, (B r c).1) ≤ 1 ∧
    isLexValid n (fun r c => (A r c).1 + (B r c).1)

instance (n : ℕ) (A : Fin n → Fin 2 → Fin 2) : Decidable (isValid n A) := by
  unfold isValid isLexValid lexRow2 lexCol
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {A : Fin n → Fin 2 → Fin 2 // isValid n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 5 =
      PowerSeries.X * (4 - 8 * PowerSeries.X + 13 * PowerSeries.X ^ 2 - 7 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * (a (n - 1) : ℤ) - 10 * (a (n - 2) : ℤ) + 10 * (a (n - 3) : ℤ) - 5 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ) := by
  sorry

end OMA.S_oeis_a225894
