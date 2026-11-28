import Mathlib

namespace OMA.S_oeis_a269658

def isValid (n : ℕ) (f : Fin 5 → Fin (n + 1)) : Prop :=
  ∀ i j : Fin 4, i.1 < j.1 →
    ¬((f ⟨i.1 + 1, by omega⟩).1 = (f ⟨i.1, by omega⟩).1 + 1 ∧
      f ⟨j.1, by omega⟩ = f ⟨i.1, by omega⟩ ∧
      f ⟨j.1 + 1, by omega⟩ = f ⟨i.1 + 1, by omega⟩)

instance (n : ℕ) (f : Fin 5 → Fin (n + 1)) : Decidable (isValid n f) := by
  unfold isValid; infer_instance

def a (n : ℕ) : ℕ :=
  Fintype.card {f : Fin 5 → Fin (n + 1) // isValid n f}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 6 =
      1 + 20 * PowerSeries.X + 84 * PowerSeries.X ^ 2 + 8 * PowerSeries.X ^ 3 + 7 * PowerSeries.X ^ 4 ∧
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 15 * (a (n - 2) : ℤ) + 20 * (a (n - 3) : ℤ) -
      15 * (a (n - 4) : ℤ) + 6 * (a (n - 5) : ℤ) - (a (n - 6) : ℤ)) ∧
    ∀ n : ℕ, a n = (n + 1) ^ 5 - 3 * n * (n + 1) := by
  sorry

end OMA.S_oeis_a269658
