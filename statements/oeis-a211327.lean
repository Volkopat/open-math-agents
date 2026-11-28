import Mathlib

namespace OMA.S_oeis_a211327

def valid2x2 (a b c d : ℤ) : Prop :=
  a + b + c + d = 0 ∧ ({a, b, c, d} : Finset ℤ).card ≠ 2

def isValid (n : ℕ) (M : Fin (n + 1) → Fin (n + 1) → ℤ) : Prop :=
  (∀ i j : Fin (n + 1), -3 ≤ M i j ∧ M i j ≤ 3) ∧
  (∀ i j : Fin (n + 1), M i j = M j i) ∧
  (∀ i j : Fin n, valid2x2 (M i.castSucc j.castSucc) (M i.castSucc j.succ) (M i.succ j.castSucc) (M i.succ j.succ))

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.card {M : Fin (n + 1) → Fin (n + 1) → ℤ // isValid n M}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * ((1 + PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
      PowerSeries.X * (15 + 18 * PowerSeries.X - 24 * PowerSeries.X ^ 2 - 28 * PowerSeries.X ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → 3 * (a n : ℤ) = -9 * 2 ^ (n / 2) + 29 * 2 ^ n + 1) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → 3 * (a n : ℤ) = -3 * 2 ^ (n / 2 + 2) + 29 * 2 ^ n - 1) := by
  sorry

end OMA.S_oeis_a211327
