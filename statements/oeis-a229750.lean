import Mathlib

namespace OMA.S_oeis_a229750

def mistakes (n : ℕ) (A : Fin n → Fin 3 → Fin 4) : ℕ :=
  (∑ r : Fin n, ∑ c : Fin 2, if A r ⟨c.1, by omega⟩ = A r ⟨c.1 + 1, by omega⟩ then 1 else 0) +
  (∑ r : Fin (n - 1),
    ((∑ c : Fin 3, if A ⟨r.1, by omega⟩ c = A ⟨r.1 + 1, by omega⟩ c then 1 else 0) +
     (∑ c : Fin 2, if A ⟨r.1, by omega⟩ ⟨c.1, by omega⟩ = A ⟨r.1 + 1, by omega⟩ ⟨c.1 + 1, by omega⟩ then 1 else 0) +
     (∑ c : Fin 2, if A ⟨r.1, by omega⟩ ⟨c.1 + 1, by omega⟩ = A ⟨r.1 + 1, by omega⟩ ⟨c.1, by omega⟩ then 1 else 0)))

def isRowMajor (n : ℕ) (A : Fin n → Fin 3 → Fin 4) : Prop :=
  ∀ i : Fin (3 * n), ∀ v : ℕ, v < (A ⟨i.1 / 3, by omega⟩ ⟨i.1 % 3, by omega⟩).1 →
    ∃ j : Fin (3 * n), j.1 < i.1 ∧ (A ⟨j.1 / 3, by omega⟩ ⟨j.1 % 3, by omega⟩).1 = v

instance (n : ℕ) (A : Fin n → Fin 3 → Fin 4) : Decidable (isRowMajor n A) := by
  unfold isRowMajor; infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {A : Fin n → Fin 3 → Fin 4 // mistakes n A = 2 ∧ isRowMajor n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * ((1 - PowerSeries.X) ^ 3 * (1 - 2 * PowerSeries.X) ^ 3) =
      PowerSeries.X * (1 + 51 * PowerSeries.X + 91 * PowerSeries.X ^ 2 - 1118 * PowerSeries.X ^ 3 +
        1706 * PowerSeries.X ^ 4 - 176 * PowerSeries.X ^ 5 - 612 * PowerSeries.X ^ 6 - 64 * PowerSeries.X ^ 7) ∧
    ∀ n : ℕ, 2 < n → (a n : ℚ) = (2 * (1732 + 117 * (2 : ℚ) ^ n) + (-4084 + 279 * (2 : ℚ) ^ n) * (n : ℚ) +
      (484 + 9 * (2 : ℚ) ^ n) * (n : ℚ) ^ 2) / 8 := by
  sorry

end OMA.S_oeis_a229750
