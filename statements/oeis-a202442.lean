import Mathlib

namespace OMA.S_oeis_a202442

def avoids3 (b0 b1 b2 : Fin 2) : Prop :=
  ¬(b0 = 0 ∧ b1 = 0 ∧ b2 = 1) ∧ ¬(b0 = 1 ∧ b1 = 1 ∧ b2 = 0)

def isValid (n : ℕ) (A : Fin (n + 2) → Fin 5 → Fin 2) : Prop :=
  (∀ r : Fin (n + 2), ∀ c : Fin 3,
    avoids3 (A r ⟨c.1, by omega⟩) (A r ⟨c.1 + 1, by omega⟩) (A r ⟨c.1 + 2, by omega⟩)) ∧
  (∀ c : Fin 5, ∀ r : Fin n,
    avoids3 (A ⟨r.1, by omega⟩ c) (A ⟨r.1 + 1, by omega⟩ c) (A ⟨r.1 + 2, by omega⟩ c)) ∧
  (∀ r : Fin n, ∀ c : Fin 3,
    avoids3 (A ⟨r.1, by omega⟩ ⟨c.1, by omega⟩) (A ⟨r.1 + 1, by omega⟩ ⟨c.1 + 1, by omega⟩) (A ⟨r.1 + 2, by omega⟩ ⟨c.1 + 2, by omega⟩))

instance (n : ℕ) (A : Fin (n + 2) → Fin 5 → Fin 2) : Decidable (isValid n A) := by
  unfold isValid avoids3
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {A : Fin (n + 2) → Fin 5 → Fin 2 // isValid n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * ((1 - PowerSeries.X) ^ 5 * (1 + PowerSeries.X) ^ 2) =
      2 * PowerSeries.X * (112 - 148 * PowerSeries.X - 114 * PowerSeries.X ^ 2 + 285 * PowerSeries.X ^ 3 - 74 * PowerSeries.X ^ 4 - 122 * PowerSeries.X ^ 5 + 84 * PowerSeries.X ^ 6 - 15 * PowerSeries.X ^ 7) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = ((n : ℚ) ^ 4 + 24 * (n : ℚ) ^ 3 + 149 * (n : ℚ) ^ 2 + 492 * (n : ℚ) + 468) / 6) ∧
    (∀ n : ℕ, 1 < n → Odd n → (a n : ℚ) = ((n : ℚ) ^ 4 + 24 * (n : ℚ) ^ 3 + 149 * (n : ℚ) ^ 2 + 498 * (n : ℚ) + 492) / 6) := by
  sorry

end OMA.S_oeis_a202442
