import Mathlib

namespace OMA.S_oeis_a224673

def isIdempotent2x2 (a b c d : ℕ) : Prop :=
  a * a + b * c = a ∧ b * (a + d) = b ∧ c * (a + d) = c ∧ d * d + b * c = d

def isValid (n : ℕ) (A : Fin (n + 1) → Fin 6 → Fin 3) : Prop :=
  ∀ (i : Fin n) (j : Fin 5),
    isIdempotent2x2 (A i.castSucc j.castSucc).1 (A i.castSucc j.succ).1
      (A i.succ j.castSucc).1 (A i.succ j.succ).1

instance (n : ℕ) (A : Fin (n + 1) → Fin 6 → Fin 3) : Decidable (isValid n A) := by
  unfold isValid isIdempotent2x2
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {A : Fin (n + 1) → Fin 6 → Fin 3 // isValid n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * ((1 - PowerSeries.X) ^ 3 * (1 - PowerSeries.X - PowerSeries.X ^ 2)) =
      PowerSeries.X * (115 - 269 * PowerSeries.X + 68 * PowerSeries.X ^ 2 +
        193 * PowerSeries.X ^ 3 - 118 * PowerSeries.X ^ 4 + 6 * PowerSeries.X ^ 5) ∧
    ∀ n : ℕ, 1 < n →
      (a n : ℝ) = 34 + ((2 : ℝ) ^ (-1 - (n : ℤ)) *
        ((1 - Real.sqrt 5) ^ n * (-11 + 53 * Real.sqrt 5) +
         (1 + Real.sqrt 5) ^ n * (11 + 53 * Real.sqrt 5))) / Real.sqrt 5 +
        14 * (1 + (n : ℝ)) + (5 / 2 : ℝ) * (1 + (n : ℝ)) * (2 + (n : ℝ)) := by
  sorry

end OMA.S_oeis_a224673
