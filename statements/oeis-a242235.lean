import Mathlib

/-!
# A242235: Number of length n+4+1 0..4 arrays with every value 0..4 appearing at least once in every consecutive 4+2 elements, and new values 0..4 introduced in order.

Source: https://oeis.org/A242235

The empirical formulas listed in the entry, stated below as one conjunction:
* Empirical: a(n) = a(n-1) + a(n-2) + a(n-3) + a(n-4) + a(n-5).
* Empirical g.f.: x*(15 + 20*x + 21*x^2 + 18*x^3 + 11*x^4) / (1 - x - x^2 - x^3 - x^4 - x^5).
  - Colin Barker, Oct 31 2018

The entry also records the conjecture a(n) = 16*A145113(n-1) + A004767(n-2), n > 1 (R. J. Mathar,
Aug 16 2017), which is not formalized here.

Conventions. Offset 1: a(n) counts the arrays `x : Fin (n + 5) → Fin 5` (length n+4+1, entries
0..4) such that
* every block of 6 (= 4+2) consecutive positions contains each of the values 0, 1, 2, 3, 4, and
* new values are introduced in order: whenever a value `v` occurs at a position, every value
  smaller than `v` already occurs at some earlier position.
The recurrence is stated for every `n >= 6` (where all five previous terms are defined). The g.f.
is stated with the denominator multiplied out, as an identity of formal power series over the
integers, for the series `Sum_{n >= 1} a(n) x^n` (coefficient 0 set to 0). The definition
reproduces the listed terms 15, 35, 71, 139, 271, ...
-/

namespace OMA.S_oeis_a242235

/-- Every block of 6 consecutive positions contains each of the values 0..4. -/
def AllInWindows {m : ℕ} (x : Fin m → Fin 5) : Prop :=
  ∀ i : Fin m, i.val + 6 ≤ m → ∀ v : Fin 5, ∃ j : Fin m, i.val ≤ j.val ∧ j.val < i.val + 6 ∧ x j = v

/-- New values are introduced in order. -/
def NewInOrder {m : ℕ} (x : Fin m → Fin 5) : Prop :=
  ∀ j : Fin m, ∀ w : Fin 5, w < x j → ∃ k : Fin m, k < j ∧ x k = w

instance {m : ℕ} (x : Fin m → Fin 5) : Decidable (AllInWindows x) := by
  unfold AllInWindows; infer_instance

instance {m : ℕ} (x : Fin m → Fin 5) : Decidable (NewInOrder x) := by
  unfold NewInOrder; infer_instance

/-- A242235(n): the number of such arrays of length `n + 5`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 5) → Fin 5)).filter (fun x => AllInWindows x ∧ NewInOrder x)).card

open PowerSeries in
theorem main :
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - X - X ^ 2 - X ^ 3 - X ^ 4 - X ^ 5) =
      X * (15 + 20 * X + 21 * X ^ 2 + 18 * X ^ 3 + 11 * X ^ 4) := by
  sorry

end OMA.S_oeis_a242235
