import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.Int.ModEq

/-!
# Two congruences for A393858

Paul D. Hanna defines A by A(X−X A(6X)/6)=X. For zero constant term
the scaled series has coefficient 6^(k−1)a(k) at every positive k;
thus no division by 6 is needed in the integer coefficient ring.
The inner series starts with X. After truncating A strictly below n,
the missing coefficient a(n) enters the left side at degree n exactly
once; its effect inside the argument starts only at degree n+1.

Source: https://oeis.org/A393858 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a393858

open PowerSeries

noncomputable def scaled {R : Type*} [CommRing R] (c : R) (F : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => match n with
    | 0 => 0
    | k + 1 => c ^ k * F.coeff (k + 1)

noncomputable def inner {R : Type*} [CommRing R] (c : R) (F : PowerSeries R) : PowerSeries R :=
  X * (1 - scaled c F)

noncomputable def a (n : ℕ) : ℤ :=
  let P : PowerSeries ℤ := PowerSeries.mk fun k => if _h : k < n then a k else 0
  (X : PowerSeries ℤ).coeff n - PowerSeries.coeff n (PowerSeries.subst (inner (6 : ℤ) P) P)
termination_by n

theorem main : ∀ n : ℕ, 0 < n →
    (Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k) ∧ Int.ModEq 7 (a n) 1 := by
  sorry

end OMA.S_oeis_a393858
