import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace OMA.S_oeis_a269607

/-- The equal adjacent pair starting at `i`. -/
def pair {n : ℕ} (w : Fin 4 → Fin (n + 1)) (i : Fin 3) : Prop :=
  w i.castSucc = w i.succ

/-- The prescribed condition on the values of two successive equal pairs. -/
def allowed {n : ℕ} (w : Fin 4 → Fin (n + 1)) (i j : Fin 3) : Prop :=
  (w i.castSucc).val + 2 ≤ (w j.castSucc).val ∨ (w j.castSucc).val + 2 ≤ (w i.castSucc).val

/-- Every successive pair of repetitions has the required difference. -/
def valid {n : ℕ} (w : Fin 4 → Fin (n + 1)) : Prop :=
  ∀ i j : Fin 3, i < j → pair w i → pair w j →
    (∀ k : Fin 3, i < k → k < j → ¬ pair w k) → allowed w i j

/-- The count starts at one and the power series has zero constant term. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else (Nat.card {w : Fin 4 → Fin (n + 1) // valid w} : ℤ)

open PowerSeries in
theorem main :
    ((1 - X) ^ 5 * mk a = 2 * X * (4 + 11 * X - 4 * X ^ 2 + X ^ 3)) ∧
    (∀ n : ℕ, 5 < n →
      a n = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
        5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a269607
