import Mathlib

namespace OMA.S_oeis_a200789

def isValid (n : ℕ) (x : Fin 7 → Fin (n + 1)) : Prop :=
  ∀ i : Fin 5, ¬(x ⟨i.1, by omega⟩ < x ⟨i.1 + 1, by omega⟩ ∧ x ⟨i.1 + 1, by omega⟩ < x ⟨i.1 + 2, by omega⟩)

instance (n : ℕ) (x : Fin 7 → Fin (n + 1)) : Decidable (isValid n x) := by
  unfold isValid
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {x : Fin 7 → Fin (n + 1) // isValid n x}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 8 =
      PowerSeries.X * (128 + 767 * PowerSeries.X + 960 * PowerSeries.X ^ 2 + 123 * PowerSeries.X ^ 3 + 60 * PowerSeries.X ^ 4 - 28 * PowerSeries.X ^ 5 + 8 * PowerSeries.X ^ 6 - PowerSeries.X ^ 7) ∧
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) + 56 * (a (n - 3) : ℤ) - 70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) - 28 * (a (n - 6) : ℤ) + 8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ)) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (5040 + 40704 * (n : ℚ) + 127582 * (n : ℚ) ^ 2 + 199213 * (n : ℚ) ^ 3 + 169960 * (n : ℚ) ^ 4 + 80626 * (n : ℚ) ^ 5 + 19978 * (n : ℚ) ^ 6 + 2017 * (n : ℚ) ^ 7) / 5040 := by
  sorry

end OMA.S_oeis_a200789
