import Mathlib

namespace OMA.S_oeis_a202443

def avoids3 (b0 b1 b2 : Fin 2) : Prop :=
  ¬(b0 = 0 ∧ b1 = 0 ∧ b2 = 1) ∧ ¬(b0 = 1 ∧ b1 = 1 ∧ b2 = 0)

def isValid (n : ℕ) (A : Fin (n + 2) → Fin 6 → Fin 2) : Prop :=
  (∀ r : Fin (n + 2), ∀ c : Fin 4,
    avoids3 (A r ⟨c.1, by omega⟩) (A r ⟨c.1 + 1, by omega⟩) (A r ⟨c.1 + 2, by omega⟩)) ∧
  (∀ c : Fin 6, ∀ r : Fin n,
    avoids3 (A ⟨r.1, by omega⟩ c) (A ⟨r.1 + 1, by omega⟩ c) (A ⟨r.1 + 2, by omega⟩ c)) ∧
  (∀ r : Fin n, ∀ c : Fin 4,
    avoids3 (A ⟨r.1, by omega⟩ ⟨c.1, by omega⟩) (A ⟨r.1 + 1, by omega⟩ ⟨c.1 + 1, by omega⟩) (A ⟨r.1 + 2, by omega⟩ ⟨c.1 + 2, by omega⟩))

instance (n : ℕ) (A : Fin (n + 2) → Fin 6 → Fin 2) : Decidable (isValid n A) := by
  unfold isValid avoids3
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {A : Fin (n + 2) → Fin 6 → Fin 2 // isValid n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * ((1 - PowerSeries.X) ^ 5 * (1 + PowerSeries.X) ^ 2) =
      2 * PowerSeries.X * (169 - 220 * PowerSeries.X - 141 * PowerSeries.X ^ 2 + 424 * PowerSeries.X ^ 3 - 133 * PowerSeries.X ^ 4 - 176 * PowerSeries.X ^ 5 + 137 * PowerSeries.X ^ 6 - 28 * PowerSeries.X ^ 7) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = (2 / 3 : ℚ) * ((n : ℚ) ^ 4 + 12 * (n : ℚ) ^ 3 + 59 * (n : ℚ) ^ 2 + 177 * (n : ℚ) + 159)) ∧
    (∀ n : ℕ, 1 < n → Odd n → (a n : ℚ) = (2 / 3 : ℚ) * ((n : ℚ) ^ 4 + 12 * (n : ℚ) ^ 3 + 59 * (n : ℚ) ^ 2 + 183 * (n : ℚ) + 168)) := by
  sorry

end OMA.S_oeis_a202443
