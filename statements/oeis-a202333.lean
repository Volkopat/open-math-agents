import Mathlib

namespace OMA.S_oeis_a202333

def win2Ok (b0 b1 b2 : Fin 2) : Prop :=
  2 * b0.1 + b1.1 ≤ 2 * b1.1 + b2.1

def isValid (n : ℕ) (A : Fin (n + 1) → Fin 7 → Fin 2) : Prop :=
  (∀ r : Fin (n + 1), ∀ c : Fin 5,
    win2Ok (A r ⟨c.1, by omega⟩) (A r ⟨c.1 + 1, by omega⟩) (A r ⟨c.1 + 2, by omega⟩)) ∧
  (∀ c : Fin 7, ∀ r : Fin (n - 1),
    win2Ok (A ⟨r.1, by omega⟩ c) (A ⟨r.1 + 1, by omega⟩ c) (A ⟨r.1 + 2, by omega⟩ c))

instance (n : ℕ) (A : Fin (n + 1) → Fin 7 → Fin 2) : Decidable (isValid n A) := by
  unfold isValid win2Ok
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {A : Fin (n + 1) → Fin 7 → Fin 2 // isValid n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 8 =
      PowerSeries.X * (81 - 378 * PowerSeries.X + 854 * PowerSeries.X ^ 2 - 1148 * PowerSeries.X ^ 3 + 966 * PowerSeries.X ^ 4 - 502 * PowerSeries.X ^ 5 + 148 * PowerSeries.X ^ 6 - 19 * PowerSeries.X ^ 7) ∧
    ∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) + 56 * (a (n - 3) : ℤ) - 70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) - 28 * (a (n - 6) : ℤ) + 8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ) := by
  sorry

end OMA.S_oeis_a202333
