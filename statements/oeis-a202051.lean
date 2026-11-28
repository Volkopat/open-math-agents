import Mathlib

namespace OMA.S_oeis_a202051

def avoids3 (b0 b1 b2 : Fin 2) : Prop :=
  ¬(b0 = 0 ∧ b1 = 0 ∧ b2 = 1) ∧ ¬(b0 = 1 ∧ b1 = 1 ∧ b2 = 0)

def isValid (n : ℕ) (A : Fin (n + 2) → Fin 9 → Fin 2) : Prop :=
  (∀ r : Fin (n + 2), ∀ c : Fin 7,
    avoids3 (A r ⟨c.1, by omega⟩) (A r ⟨c.1 + 1, by omega⟩) (A r ⟨c.1 + 2, by omega⟩)) ∧
  (∀ c : Fin 9, ∀ r : Fin n,
    avoids3 (A ⟨r.1, by omega⟩ c) (A ⟨r.1 + 1, by omega⟩ c) (A ⟨r.1 + 2, by omega⟩ c))

instance (n : ℕ) (A : Fin (n + 2) → Fin 9 → Fin 2) : Decidable (isValid n A) := by
  unfold isValid avoids3
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {A : Fin (n + 2) → Fin 9 → Fin 2 // isValid n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 10 =
      18 * PowerSeries.X * (107 - 634 * PowerSeries.X + 1880 * PowerSeries.X ^ 2 - 3472 * PowerSeries.X ^ 3 + 4298 * PowerSeries.X ^ 4 - 3652 * PowerSeries.X ^ 5 + 2114 * PowerSeries.X ^ 6 - 800 * PowerSeries.X ^ 7 + 179 * PowerSeries.X ^ 8 - 18 * PowerSeries.X ^ 9) ∧
    ∀ n : ℕ, 10 < n →
      (a n : ℤ) = 10 * (a (n - 1) : ℤ) - 45 * (a (n - 2) : ℤ) + 120 * (a (n - 3) : ℤ) - 210 * (a (n - 4) : ℤ) + 252 * (a (n - 5) : ℤ) - 210 * (a (n - 6) : ℤ) + 120 * (a (n - 7) : ℤ) - 45 * (a (n - 8) : ℤ) + 10 * (a (n - 9) : ℤ) - (a (n - 10) : ℤ) := by
  sorry

end OMA.S_oeis_a202051
