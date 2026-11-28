import Mathlib

/-!
# A126531: Number of base 10 n-digit numbers with adjacent digits differing by five or less.

Source: https://oeis.org/A126531
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 10, 80, 660, 5430, 44692, ...).

Conventions:
* A base 10 n-digit number (with leading zeros allowed, matching `a 0 = 1`, `a 1 = 10`,
  `a 2 = 80`) is a word `w : Fin n → Fin 10`.
* Adjacent digits at positions `i` and `i + 1` (for `i : Fin (n - 1)`) differ by at most 5,
  expressed as `((w i : ℤ) - (w (i + 1) : ℤ)).natAbs ≤ 5`.
* At `n = 0`, the unique empty word vacuously satisfies the condition, giving `a 0 = 1`.

Conjectures (Colin Barker, May 31 2017):
G.f.: (1 - x)*(1 + 3*x - x^3) / ((1 + x)*(1 - 9*x + 6*x^2 + 3*x^3 - 2*x^4)).
a(n) = 8*a(n-1) + 3*a(n-2) - 9*a(n-3) - a(n-4) + 2*a(n-5) for n>4.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a126531

open PowerSeries

/-- Two base-10 digits differ by at most 5. -/
def adjOk (x y : Fin 10) : Prop :=
  ((x : ℤ) - (y : ℤ)).natAbs ≤ 5

instance (x y : Fin 10) : Decidable (adjOk x y) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A word of length `n` over `Fin 10` has all adjacent digits differing by at most 5. -/
def isValid (n : ℕ) (w : Fin n → Fin 10) : Prop :=
  ∀ i : Fin (n - 1), adjOk (w ⟨i.val, by omega⟩) (w ⟨i.val + 1, by omega⟩)

instance (n : ℕ) (w : Fin n → Fin 10) : Decidable (isValid n w) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A126531: the number of base 10 n-digit numbers with adjacent digits differing by 5 or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (isValid n)).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 + X) * (1 - 9 * X + 6 * X ^ 2 + 3 * X ^ 3 - 2 * X ^ 4)) =
      (1 - X) * (1 + 3 * X - X ^ 3)) ∧
    (∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 8 * a (n - 1) + 3 * a (n - 2) - 9 * a (n - 3) - a (n - 4) + 2 * a (n - 5)) := by
  sorry

end OMA.S_oeis_a126531
