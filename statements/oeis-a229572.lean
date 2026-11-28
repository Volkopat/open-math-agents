import Mathlib

namespace OMA.S_oeis_a229572

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
  if n = 0 then 0 else Fintype.card {A : Fin n → Fin 2 → Fin 4 // mistakes n A = 1 ∧ isRowMajor n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - 2 * PowerSeries.X) ^ 2 = PowerSeries.X * (1 + 2 * PowerSeries.X + 6 * PowerSeries.X ^ 2) ∧
    (∀ n : ℕ, 1 < n → (a n : ℤ) = 2 ^ (n - 2) * (7 * (n : ℤ) - 8)) ∧
    PowerSeries.mk (fun n => (a n : ℚ) / (n.factorial : ℚ)) = 2 + PowerSeries.C (1 / 2 : ℚ) * (3 * PowerSeries.X + PowerSeries.rescale 2 (PowerSeries.exp ℚ) * (7 * PowerSeries.X - 4)) := by
  sorry

end OMA.S_oeis_a229572
