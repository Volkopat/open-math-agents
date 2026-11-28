import Mathlib

/-!
# A125396: Number of base 8 circular n-digit numbers with adjacent digits differing by 6 or less.

Source: https://oeis.org/A125396
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 8, 62, 470, 3650, 28358, ...).

Conventions:
* A base 8 circular n-digit number (with leading zeros allowed, matching `a 0 = 1`, `a 1 = 8`,
  `a 2 = 62`) is a word `w : Fin n → Fin 8`.
* Circular adjacency requires that for every `i : Fin n`, `w i` and `w ((i + 1) % n)` differ
  by at most 6, expressed as `((w i : ℤ) - (w ((i + 1) % n) : ℤ)).natAbs ≤ 6`.
* At `n = 0`, the unique empty word vacuously satisfies the condition, giving `a 0 = 1`.
  At `n = 1`, `w 0` is adjacent to itself with difference `0 ≤ 6`, giving `a 1 = 8`.

Conjectures (Colin Barker, Jun 02 2017):
G.f.: (1 - x^2 - 12*x^3) / ((1 - x)*(1 - 7*x - 6*x^2)).
a(n) = 1 + ((7-sqrt(73))/2)^n + ((7+sqrt(73))/2)^n for n>0.
a(n) = 8*a(n-1) - a(n-2) - 6*a(n-3) for n>3.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a125396

open PowerSeries

/-- Two base-8 digits differ by at most 6. -/
def adjOk (x y : Fin 8) : Prop :=
  ((x : ℤ) - (y : ℤ)).natAbs ≤ 6

instance (x y : Fin 8) : Decidable (adjOk x y) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A circular word of length `n` over `Fin 8` has all circularly adjacent digits differing
by at most 6. -/
def isValid (n : ℕ) (w : Fin n → Fin 8) : Prop :=
  ∀ i : Fin n, adjOk (w i) (w ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

instance (n : ℕ) (w : Fin n → Fin 8) : Decidable (isValid n w) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A125396: the number of base 8 circular n-digit numbers with adjacent digits differing
by 6 or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (isValid n)).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 7 * X - 6 * X ^ 2)) =
      1 - X ^ 2 - 12 * X ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 1 + ((7 - Real.sqrt 73) / 2) ^ n + ((7 + Real.sqrt 73) / 2) ^ n) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 8 * a (n - 1) - a (n - 2) - 6 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a125396
