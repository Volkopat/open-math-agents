import Mathlib

namespace OMA.S_oeis_a202334

def win2Ok (b0 b1 b2 : Fin 2) : Prop :=
  2 * b0.1 + b1.1 ≤ 2 * b1.1 + b2.1

def isValid (n : ℕ) (A : Fin (n + 1) → Fin 8 → Fin 2) : Prop :=
  (∀ r : Fin (n + 1), ∀ c : Fin 6,
    win2Ok (A r ⟨c.1, by omega⟩) (A r ⟨c.1 + 1, by omega⟩) (A r ⟨c.1 + 2, by omega⟩)) ∧
  (∀ c : Fin 8, ∀ r : Fin (n - 1),
    win2Ok (A ⟨r.1, by omega⟩ c) (A ⟨r.1 + 1, by omega⟩ c) (A ⟨r.1 + 2, by omega⟩ c))

instance (n : ℕ) (A : Fin (n + 1) → Fin 8 → Fin 2) : Decidable (isValid n A) := by
  unfold isValid win2Ok
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {A : Fin (n + 1) → Fin 8 → Fin 2 // isValid n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 9 =
      PowerSeries.X * (100 - 532 * PowerSeries.X + 1400 * PowerSeries.X ^ 2 - 2254 * PowerSeries.X ^ 3 + 2366 * PowerSeries.X ^ 4 - 1636 * PowerSeries.X ^ 5 + 722 * PowerSeries.X ^ 6 - 185 * PowerSeries.X ^ 7 + 21 * PowerSeries.X ^ 8) ∧
    ∀ n : ℕ, 9 < n →
      (a n : ℤ) = 9 * (a (n - 1) : ℤ) - 36 * (a (n - 2) : ℤ) + 84 * (a (n - 3) : ℤ) - 126 * (a (n - 4) : ℤ) + 126 * (a (n - 5) : ℤ) - 84 * (a (n - 6) : ℤ) + 36 * (a (n - 7) : ℤ) - 9 * (a (n - 8) : ℤ) + (a (n - 9) : ℤ) := by
  sorry

end OMA.S_oeis_a202334
