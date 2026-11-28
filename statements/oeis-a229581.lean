import Mathlib

namespace OMA.S_oeis_a229581

def mistakes (n : ℕ) (A : Fin n → Fin 3 → Fin 3) : ℕ :=
  (∑ r : Fin n, (∑ c : Fin 2, if A r ⟨c.1, by omega⟩ = A r ⟨c.1 + 1, by omega⟩ then 1 else 0)) +
  (∑ r : Fin (n - 1), ((∑ c : Fin 2, if A ⟨r.1, by omega⟩ ⟨c.1 + 1, by omega⟩ = A ⟨r.1 + 1, by omega⟩ ⟨c.1, by omega⟩ then 1 else 0)))

def isRowMajor (n : ℕ) (A : Fin n → Fin 3 → Fin 3) : Prop :=
  ∀ i : Fin (3 * n), ∀ v : ℕ, v < (A ⟨i.1 / 3, by omega⟩ ⟨i.1 % 3, by omega⟩).1 →
    ∃ j : Fin (3 * n), j.1 < i.1 ∧ (A ⟨j.1 / 3, by omega⟩ ⟨j.1 % 3, by omega⟩).1 = v

instance (n : ℕ) (A : Fin n → Fin 3 → Fin 3) : Decidable (isRowMajor n A) := by
  unfold isRowMajor; infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {A : Fin n → Fin 3 → Fin 3 // mistakes n A = 1 ∧ isRowMajor n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - 6 * PowerSeries.X) ^ 2 = 2 * PowerSeries.X * (1 + 2 * PowerSeries.X) ∧
    ∀ n : ℕ, 0 < n → (a n : ℚ) = (2 : ℚ) ^ n * (3 : ℚ) ^ ((n : ℤ) - 2) * (4 * (n : ℚ) - 1) := by
  sorry

end OMA.S_oeis_a229581
