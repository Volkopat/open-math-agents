import Mathlib

namespace OMA.S_oeis_a229014

def med3 (a b c : ℕ) : ℕ :=
  max (min a b) (min (max a b) c)

def isValid (n : ℕ) (y : Fin 4 → Fin (n + 1)) : Prop :=
  ∃ x : Fin 6 → Fin (n + 1),
    (∀ i : Fin 5, x ⟨i.1, by omega⟩ ≠ x ⟨i.1 + 1, by omega⟩) ∧
    ∀ i : Fin 4, (y i).1 = med3 (x ⟨i.1, by omega⟩).1 (x ⟨i.1 + 1, by omega⟩).1 (x ⟨i.1 + 2, by omega⟩).1

instance (n : ℕ) (y : Fin 4 → Fin (n + 1)) : Decidable (isValid n y) := by
  unfold isValid med3; infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {y : Fin 4 → Fin (n + 1) // isValid n y}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 5 =
      PowerSeries.X * (2 - PowerSeries.X) * (1 + 11 * PowerSeries.X + 3 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * (a (n - 1) : ℤ) - 10 * (a (n - 2) : ℤ) + 10 * (a (n - 3) : ℤ) - 5 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ) := by
  sorry

end OMA.S_oeis_a229014
