import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace OMA.S_oeis_a268461

/-- The ascending pair starting at `i` occurs in reverse at `j`. -/
def reversed {n : ℕ} (w : Fin 7 → Fin (n + 1)) (i j : Fin 6) : Prop :=
  (w i.castSucc).val + 1 = (w i.succ).val ∧
    w i.castSucc = w j.succ ∧ w i.succ = w j.castSucc

/-- The count is indexed from one, with coefficient zero at index zero in the series. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else
    (Nat.card {w : Fin 7 → Fin (n + 1) // ∀ i j : Fin 6, i < j → ¬ reversed w i j} : ℤ)

open PowerSeries in
theorem main :
    ((1 - X) ^ 8 * mk a = X *
      (29 + 937 * X + 2996 * X ^ 2 + 1355 * X ^ 3 - 536 * X ^ 4 + 335 * X ^ 5 -
        88 * X ^ 6 + 13 * X ^ 7 - X ^ 8)) ∧
    (∀ n : ℕ, 9 < n →
      a n = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) -
        70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a268461
