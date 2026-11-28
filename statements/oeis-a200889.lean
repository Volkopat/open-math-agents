import Mathlib

namespace OMA.S_oeis_a200889

def isValid (n : ℕ) (x : Fin 6 → Fin (n + 1)) : Prop :=
  ∀ i : Fin 4, ¬(x ⟨i.1, by omega⟩ < x ⟨i.1 + 1, by omega⟩ ∧ x ⟨i.1 + 2, by omega⟩ < x ⟨i.1 + 1, by omega⟩)

instance (n : ℕ) (x : Fin 6 → Fin (n + 1)) : Decidable (isValid n x) := by
  unfold isValid
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {x : Fin 6 → Fin (n + 1) // isValid n x}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 7 =
      PowerSeries.X * (37 + 33 * PowerSeries.X + PowerSeries.X ^ 2 - 54 * PowerSeries.X ^ 3 + 21 * PowerSeries.X ^ 4 - 7 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6) ∧
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * (a (n - 1) : ℤ) - 21 * (a (n - 2) : ℤ) + 35 * (a (n - 3) : ℤ) - 35 * (a (n - 4) : ℤ) + 21 * (a (n - 5) : ℤ) - 7 * (a (n - 6) : ℤ) + (a (n - 7) : ℤ)) := by
  sorry

end OMA.S_oeis_a200889
