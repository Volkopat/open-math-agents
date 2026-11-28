import Mathlib

namespace OMA.S_oeis_a202050

def avoids3 (b0 b1 b2 : Fin 2) : Prop :=
  ¬(b0 = 0 ∧ b1 = 0 ∧ b2 = 1) ∧ ¬(b0 = 1 ∧ b1 = 1 ∧ b2 = 0)

def isValid (n : ℕ) (A : Fin (n + 2) → Fin 8 → Fin 2) : Prop :=
  (∀ r : Fin (n + 2), ∀ c : Fin 6,
    avoids3 (A r ⟨c.1, by omega⟩) (A r ⟨c.1 + 1, by omega⟩) (A r ⟨c.1 + 2, by omega⟩)) ∧
  (∀ c : Fin 8, ∀ r : Fin n,
    avoids3 (A ⟨r.1, by omega⟩ c) (A ⟨r.1 + 1, by omega⟩ c) (A ⟨r.1 + 2, by omega⟩ c))

instance (n : ℕ) (A : Fin (n + 2) → Fin 8 → Fin 2) : Decidable (isValid n A) := by
  unfold isValid avoids3
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {A : Fin (n + 2) → Fin 8 → Fin 2 // isValid n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 9 =
      16 * PowerSeries.X * (87 - 457 * PowerSeries.X + 1183 * PowerSeries.X ^ 2 - 1869 * PowerSeries.X ^ 3 + 1925 * PowerSeries.X ^ 4 - 1307 * PowerSeries.X ^ 5 + 567 * PowerSeries.X ^ 6 - 143 * PowerSeries.X ^ 7 + 16 * PowerSeries.X ^ 8) ∧
    ∀ n : ℕ, 9 < n →
      (a n : ℤ) = 9 * (a (n - 1) : ℤ) - 36 * (a (n - 2) : ℤ) + 84 * (a (n - 3) : ℤ) - 126 * (a (n - 4) : ℤ) + 126 * (a (n - 5) : ℤ) - 84 * (a (n - 6) : ℤ) + 36 * (a (n - 7) : ℤ) - 9 * (a (n - 8) : ℤ) + (a (n - 9) : ℤ) := by
  sorry

end OMA.S_oeis_a202050
