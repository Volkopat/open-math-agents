import Mathlib

namespace OMA.S_oeis_a200791

def isValid (n : ℕ) (x : Fin 9 → Fin (n + 1)) : Prop :=
  ∀ i : Fin 7, ¬(x ⟨i.1, by omega⟩ < x ⟨i.1 + 1, by omega⟩ ∧ x ⟨i.1 + 1, by omega⟩ < x ⟨i.1 + 2, by omega⟩)

instance (n : ℕ) (x : Fin 9 → Fin (n + 1)) : Decidable (isValid n x) := by
  unfold isValid
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {x : Fin 9 → Fin (n + 1) // isValid n x}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 10 =
      PowerSeries.X * (512 + 9729 * PowerSeries.X + 37570 * PowerSeries.X ^ 2 + 39065 * PowerSeries.X ^ 3 + 11862 * PowerSeries.X ^ 4 + 551 * PowerSeries.X ^ 5 + 124 * PowerSeries.X ^ 6 - 45 * PowerSeries.X ^ 7 + 10 * PowerSeries.X ^ 8 - PowerSeries.X ^ 9) ∧
    (∀ n : ℕ, 10 < n →
      (a n : ℤ) = 10 * (a (n - 1) : ℤ) - 45 * (a (n - 2) : ℤ) + 120 * (a (n - 3) : ℤ) - 210 * (a (n - 4) : ℤ) + 252 * (a (n - 5) : ℤ) - 210 * (a (n - 6) : ℤ) + 120 * (a (n - 7) : ℤ) - 45 * (a (n - 8) : ℤ) + 10 * (a (n - 9) : ℤ) - (a (n - 10) : ℤ)) := by
  sorry

end OMA.S_oeis_a200791
