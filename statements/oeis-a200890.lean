import Mathlib

namespace OMA.S_oeis_a200890

def isValid (n : ℕ) (x : Fin 7 → Fin (n + 1)) : Prop :=
  ∀ i : Fin 5, ¬(x ⟨i.1, by omega⟩ < x ⟨i.1 + 1, by omega⟩ ∧ x ⟨i.1 + 2, by omega⟩ < x ⟨i.1 + 1, by omega⟩)

instance (n : ℕ) (x : Fin 7 → Fin (n + 1)) : Decidable (isValid n x) := by
  unfold isValid
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {x : Fin 7 → Fin (n + 1) // isValid n x}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 8 =
      PowerSeries.X * (65 + 184 * PowerSeries.X + 11 * PowerSeries.X ^ 2 - 224 * PowerSeries.X ^ 3 + 48 * PowerSeries.X ^ 4 - 27 * PowerSeries.X ^ 5 + 8 * PowerSeries.X ^ 6 - PowerSeries.X ^ 7) ∧
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) + 56 * (a (n - 3) : ℤ) - 70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) - 28 * (a (n - 6) : ℤ) + 8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ)) := by
  sorry

end OMA.S_oeis_a200890
