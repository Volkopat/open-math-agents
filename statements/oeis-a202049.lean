import Mathlib

namespace OMA.S_oeis_a202049

def avoids3 (b0 b1 b2 : Fin 2) : Prop :=
  ¬(b0 = 0 ∧ b1 = 0 ∧ b2 = 1) ∧ ¬(b0 = 1 ∧ b1 = 1 ∧ b2 = 0)

def isValid (n : ℕ) (A : Fin (n + 2) → Fin 7 → Fin 2) : Prop :=
  (∀ r : Fin (n + 2), ∀ c : Fin 5,
    avoids3 (A r ⟨c.1, by omega⟩) (A r ⟨c.1 + 1, by omega⟩) (A r ⟨c.1 + 2, by omega⟩)) ∧
  (∀ c : Fin 7, ∀ r : Fin n,
    avoids3 (A ⟨r.1, by omega⟩ c) (A ⟨r.1 + 1, by omega⟩ c) (A ⟨r.1 + 2, by omega⟩ c))

instance (n : ℕ) (A : Fin (n + 2) → Fin 7 → Fin 2) : Decidable (isValid n A) := by
  unfold isValid avoids3
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {A : Fin (n + 2) → Fin 7 → Fin 2 // isValid n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 8 =
      14 * PowerSeries.X * (69 - 316 * PowerSeries.X + 699 * PowerSeries.X ^ 2 - 918 * PowerSeries.X ^ 3 + 755 * PowerSeries.X ^ 4 - 384 * PowerSeries.X ^ 5 + 111 * PowerSeries.X ^ 6 - 14 * PowerSeries.X ^ 7) ∧
    ∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) + 56 * (a (n - 3) : ℤ) - 70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) - 28 * (a (n - 6) : ℤ) + 8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ) := by
  sorry

end OMA.S_oeis_a202049
