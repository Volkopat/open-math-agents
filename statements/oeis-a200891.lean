import Mathlib

namespace OMA.S_oeis_a200891

def isValid (n : ℕ) (x : Fin 8 → Fin (n + 1)) : Prop :=
  ∀ i : Fin 6, ¬(x ⟨i.1, by omega⟩ < x ⟨i.1 + 1, by omega⟩ ∧ x ⟨i.1 + 2, by omega⟩ < x ⟨i.1 + 1, by omega⟩)

instance (n : ℕ) (x : Fin 8 → Fin (n + 1)) : Decidable (isValid n x) := by
  unfold isValid
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {x : Fin 8 → Fin (n + 1) // isValid n x}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 9 =
      PowerSeries.X * (114 + 665 * PowerSeries.X + 357 * PowerSeries.X ^ 2 - 953 * PowerSeries.X ^ 3 - 37 * PowerSeries.X ^ 4 - 47 * PowerSeries.X ^ 5 + 37 * PowerSeries.X ^ 6 - 9 * PowerSeries.X ^ 7 + PowerSeries.X ^ 8) ∧
    (∀ n : ℕ, 9 < n →
      (a n : ℤ) = 9 * (a (n - 1) : ℤ) - 36 * (a (n - 2) : ℤ) + 84 * (a (n - 3) : ℤ) - 126 * (a (n - 4) : ℤ) + 126 * (a (n - 5) : ℤ) - 84 * (a (n - 6) : ℤ) + 36 * (a (n - 7) : ℤ) - 9 * (a (n - 8) : ℤ) + (a (n - 9) : ℤ)) := by
  sorry

end OMA.S_oeis_a200891
