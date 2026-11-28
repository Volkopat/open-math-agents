import Mathlib

/-!
# A242234: Number of length n+3+1 0..3 arrays with every value 0..3 appearing at least once in every consecutive 3+2 elements, and new values 0..3 introduced in order.

Source: https://oeis.org/A242234

The empirical formulas listed in the entry, stated below as one conjunction:
* Empirical: a(n) = a(n-1) +a(n-2) +a(n-3) +a(n-4).
* Empirical g.f.: x*(10 + 12*x + 11*x^2 + 7*x^3) / (1 - x - x^2 - x^3 - x^4). - Colin Barker, Mar 19 2018

The entry also records the conjecture a(n) = 9*A145112(n-1) + A016777(n-1) (R. J. Mathar,
Aug 16 2017), which is not formalized here.

Conventions. Offset 1: a(n) counts the arrays `x : Fin (n + 4) → Fin 4` (length n+3+1, entries
0..3) such that
* every block of 5 (= 3+2) consecutive positions contains each of the values 0, 1, 2, 3, and
* new values are introduced in order: whenever a value `v` occurs at a position, every value
  smaller than `v` already occurs at some earlier position.
The recurrence is stated for every `n >= 5` (where all four previous terms are defined). The g.f.
is stated with the denominator multiplied out, as an identity of formal power series over the
integers, for the series `Sum_{n >= 1} a(n) x^n` (coefficient 0 set to 0). The definition
reproduces the listed terms 10, 22, 43, 82, 157, ...
-/

namespace OMA.S_oeis_a242234

/-- Every block of 5 consecutive positions contains each of the values 0..3. -/
def AllInWindows {m : ℕ} (x : Fin m → Fin 4) : Prop :=
  ∀ i : Fin m, i.val + 5 ≤ m → ∀ v : Fin 4, ∃ j : Fin m, i.val ≤ j.val ∧ j.val < i.val + 5 ∧ x j = v

/-- New values are introduced in order. -/
def NewInOrder {m : ℕ} (x : Fin m → Fin 4) : Prop :=
  ∀ j : Fin m, ∀ w : Fin 4, w < x j → ∃ k : Fin m, k < j ∧ x k = w

instance {m : ℕ} (x : Fin m → Fin 4) : Decidable (AllInWindows x) := by
  unfold AllInWindows; infer_instance

instance {m : ℕ} (x : Fin m → Fin 4) : Decidable (NewInOrder x) := by
  unfold NewInOrder; infer_instance

/-- A242234(n): the number of such arrays of length `n + 4`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 4) → Fin 4)).filter (fun x => AllInWindows x ∧ NewInOrder x)).card

open PowerSeries in
theorem main :
    (∀ n : ℕ, 5 ≤ n → (a n : ℤ) = a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - X - X ^ 2 - X ^ 3 - X ^ 4) =
      X * (10 + 12 * X + 11 * X ^ 2 + 7 * X ^ 3) := by
  sorry

end OMA.S_oeis_a242234
