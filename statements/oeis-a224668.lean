import Mathlib

namespace OMA.S_oeis_a224668

def isIdempotent2x2 (a b c d : ℕ) : Prop :=
  a * a + b * c = a ∧ b * (a + d) = b ∧ c * (a + d) = c ∧ d * d + b * c = d

def isValid (n : ℕ) (A : Fin 6 → Fin 6 → Fin (n + 1)) : Prop :=
  ∀ i j : Fin 5,
    isIdempotent2x2 (A i.castSucc j.castSucc).1 (A i.castSucc j.succ).1
      (A i.succ j.castSucc).1 (A i.succ j.succ).1

instance (n : ℕ) (A : Fin 6 → Fin 6 → Fin (n + 1)) : Decidable (isValid n A) := by
  unfold isValid isIdempotent2x2
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {A : Fin 6 → Fin 6 → Fin (n + 1) // isValid n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 3 =
      2 * PowerSeries.X * (214 - 371 * PowerSeries.X + 163 * PowerSeries.X ^ 2) ∧
    ∀ n : ℕ, 3 < n →
      (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) + (a (n - 3) : ℤ) := by
  sorry

end OMA.S_oeis_a224668
