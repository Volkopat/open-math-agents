import Mathlib

namespace OMA.S_oeis_a229015

def med3 (a b c : ℕ) : ℕ :=
  max (min a b) (min (max a b) c)

def isValid (n : ℕ) (y : Fin 5 → Fin (n + 1)) : Prop :=
  ∃ x : Fin 7 → Fin (n + 1),
    (∀ i : Fin 6, x ⟨i.1, by omega⟩ ≠ x ⟨i.1 + 1, by omega⟩) ∧
    ∀ i : Fin 5, (y i).1 = med3 (x ⟨i.1, by omega⟩).1 (x ⟨i.1 + 1, by omega⟩).1 (x ⟨i.1 + 2, by omega⟩).1

instance (n : ℕ) (y : Fin 5 → Fin (n + 1)) : Decidable (isValid n y) := by
  unfold isValid med3; infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {y : Fin 5 → Fin (n + 1) // isValid n y}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 6 =
      PowerSeries.X * (2 + 45 * PowerSeries.X + 20 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 + PowerSeries.X ^ 5) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 15 * (a (n - 2) : ℤ) + 20 * (a (n - 3) : ℤ) - 15 * (a (n - 4) : ℤ) + 6 * (a (n - 5) : ℤ) - (a (n - 6) : ℤ) := by
  sorry

end OMA.S_oeis_a229015
