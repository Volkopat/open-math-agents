import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Generating function and recurrence for OEIS A250355

Source: https://oeis.org/A250355

Position i is indexed from zero. Its value is i plus an offset from 0 to n.
The resulting uniform shift preserves all repetitions. A value occurs more
than twice exactly when a three-element subset of positions has a uniform value.
The formal series begins at index one.
-/

namespace OMA.S_oeis_a250355

abbrev ArrayChoice (n : ℕ) := Fin 6 → Fin (n + 1)

def value {n : ℕ} (w : ArrayChoice n) (i : Fin 6) : ℕ := (w i).val + i.val

def uniform {n : ℕ} (w : ArrayChoice n) (s : Finset (Fin 6)) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, value w i = value w j

def bad {n : ℕ} (w : ArrayChoice n) : Prop :=
  ∃ s : {s : Finset (Fin 6) // s.card = 3}, uniform w s.val

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.card { w : ArrayChoice n // ¬ bad w }

open PowerSeries in
theorem main :
    ((1 - X) ^ 7 * PowerSeries.mk (fun n => (a n : ℤ)) =
      X * (64 + 174 * X + 339 * X ^ 2 + 113 * X ^ 3 + 204 * X ^ 4 + 168 * X ^ 5 -
        847 * X ^ 6 + 783 * X ^ 7 - 336 * X ^ 8 + 58 * X ^ 9)) ∧
    (∀ n : ℕ, 10 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) -
        35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a250355
