import Mathlib

namespace OMA.S_oeis_a211490

def valid2x2 (a b c d : ℤ) : Prop :=
  a + b + c + d = 0 ∧ ({a, b, c, d} : Finset ℤ).card ≤ 2

def isValid (n : ℕ) (A : Fin (n + 1) → Fin (n + 1) → ℤ) : Prop :=
  (∀ i j, -4 ≤ A i j ∧ A i j ≤ 4) ∧
  (∀ i j, A i j = A j i) ∧
  (∀ i j : Fin n,
    valid2x2 (A i.castSucc j.castSucc) (A i.castSucc j.succ)
      (A i.succ j.castSucc) (A i.succ j.succ))

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.card {A : Fin (n + 1) → Fin (n + 1) → ℤ // isValid n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * ((1 - PowerSeries.X) * (1 - PowerSeries.X - PowerSeries.X ^ 2)) =
      PowerSeries.X * (13 - 9 * PowerSeries.X - 11 * PowerSeries.X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = 7 + ((2 : ℝ) ^ (1 - (n : ℤ)) *
        ((1 - Real.sqrt 5) ^ n * (-2 + Real.sqrt 5) +
         (1 + Real.sqrt 5) ^ n * (2 + Real.sqrt 5))) / Real.sqrt 5 := by
  sorry

end OMA.S_oeis_a211490
