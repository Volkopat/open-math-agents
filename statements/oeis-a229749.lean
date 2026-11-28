import Mathlib

namespace OMA.S_oeis_a229749

def mistakes (n : ℕ) (A : Fin n → Fin 2 → Fin 4) : ℕ :=
  (∑ r : Fin n, if A r 0 = A r 1 then 1 else 0) +
  (∑ r : Fin (n - 1),
    ((if A ⟨r.1, by omega⟩ 0 = A ⟨r.1 + 1, by omega⟩ 0 then 1 else 0) +
    (if A ⟨r.1, by omega⟩ 1 = A ⟨r.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if A ⟨r.1, by omega⟩ 0 = A ⟨r.1 + 1, by omega⟩ 1 then 1 else 0) +
    (if A ⟨r.1, by omega⟩ 1 = A ⟨r.1 + 1, by omega⟩ 0 then 1 else 0)))

def isRowMajor (n : ℕ) (A : Fin n → Fin 2 → Fin 4) : Prop :=
  ∀ i : Fin (2 * n), ∀ v : ℕ, v < (A ⟨i.1 / 2, by omega⟩ ⟨i.1 % 2, by omega⟩).1 →
    ∃ j : Fin (2 * n), j.1 < i.1 ∧ (A ⟨j.1 / 2, by omega⟩ ⟨j.1 % 2, by omega⟩).1 = v

instance (n : ℕ) (A : Fin n → Fin 2 → Fin 4) : Decidable (isRowMajor n A) := by
  unfold isRowMajor; infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {A : Fin n → Fin 2 → Fin 4 // mistakes n A = 2 ∧ isRowMajor n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - 2 * PowerSeries.X) ^ 3 = PowerSeries.X ^ 2 * (3 + 42 * PowerSeries.X + 98 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3) ∧
    ∀ n : ℕ, 2 < n → (a n : ℤ) = 2 ^ (n - 3) * (195 - 192 * (n : ℤ) + 49 * (n : ℤ) ^ 2) := by
  sorry

end OMA.S_oeis_a229749
