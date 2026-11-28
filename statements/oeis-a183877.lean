import Mathlib

/-!
# A183877: Ternary words where every entry is a sum of two other entries

Source: https://oeis.org/A183877

Two other entries means two distinct positions, both different from the target
position. Addition in `Fin 3` is addition modulo 3. Kotešovec's count and
Barker's generating function and linear recurrence are stated below.
-/

namespace OMA.S_oeis_a183877

/-- Every position has two distinct other positions whose letters add to its letter. -/
def Valid {m : ℕ} (w : Fin m → Fin 3) : Prop :=
  ∀ i, ∃ j k, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧ w j + w k = w i

instance {m : ℕ} (w : Fin m → Fin 3) : Decidable (Valid w) := by
  unfold Valid
  infer_instance

/-- The count with the OEIS offset. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter (Valid (m := n+2))).card

/-- Ordinary generating function, with constant coefficient zero. -/
noncomputable def gf : PowerSeries ℤ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℤ))

theorem main :
    a 1 = 1 ∧
    (∀ n ≥ 2, (a n : ℤ) = 3^(n+2) - 2*(n+3 : ℤ)^2) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 6*a (n-1) - 12*a (n-2) + 10*a (n-3) - 3*a (n-4)) ∧
    gf * ((1-PowerSeries.X)^3*(1-3*PowerSeries.X)) =
      PowerSeries.X*(1+25*PowerSeries.X-3*PowerSeries.X^2-33*PowerSeries.X^3+18*PowerSeries.X^4) := by
  sorry

end OMA.S_oeis_a183877
