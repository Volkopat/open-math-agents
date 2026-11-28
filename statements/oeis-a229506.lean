import Mathlib

namespace OMA.S_oeis_a229506

def mistakes (n : ℕ) (A : Fin n → Fin 4 → Fin 3) : ℕ :=
  (∑ r : Fin (n - 1), ((∑ c : Fin 3, if A ⟨r.1, by omega⟩ ⟨c.1, by omega⟩ = A ⟨r.1 + 1, by omega⟩ ⟨c.1 + 1, by omega⟩ then 1 else 0) + (∑ c : Fin 3, if A ⟨r.1, by omega⟩ ⟨c.1 + 1, by omega⟩ = A ⟨r.1 + 1, by omega⟩ ⟨c.1, by omega⟩ then 1 else 0)))

def isRowMajor (n : ℕ) (A : Fin n → Fin 4 → Fin 3) : Prop :=
  ∀ i : Fin (4 * n), ∀ v : ℕ, v < (A ⟨i.1 / 4, by omega⟩ ⟨i.1 % 4, by omega⟩).1 →
    ∃ j : Fin (4 * n), j.1 < i.1 ∧ (A ⟨j.1 / 4, by omega⟩ ⟨j.1 % 4, by omega⟩).1 = v

instance (n : ℕ) (A : Fin n → Fin 4 → Fin 3) : Decidable (isRowMajor n A) := by
  unfold isRowMajor; infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {A : Fin n → Fin 4 → Fin 3 // mistakes n A = 1 ∧ isRowMajor n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - 9 * PowerSeries.X) ^ 2 = 288 * PowerSeries.X ^ 2 * (1 - PowerSeries.X) * (1 - 3 * PowerSeries.X) ∧
    ∀ n : ℕ, 2 < n → (a n : ℤ) = 64 * 3 ^ (2 * n - 5) * (8 * (n : ℤ) - 3) := by
  sorry

end OMA.S_oeis_a229506
