import Mathlib

/-!
# A126503: Number of base 8 n-digit numbers with adjacent digits differing by four or less.

Source: https://oeis.org/A126503
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 8, 52, 348, 2322, 15500, ...).

Conventions:
* A base 8 n-digit number (with leading zeros allowed, matching `a 0 = 1`, `a 1 = 8`,
  `a 2 = 52`) is a word `w : Fin n → Fin 8`.
* Adjacent digits at positions `i` and `i + 1` (for `i : Fin (n - 1)`) differ by at most 4,
  expressed as `((w i : ℤ) - (w (i + 1) : ℤ)).natAbs ≤ 4`.
* At `n = 0`, the unique empty word vacuously satisfies the condition, giving `a 0 = 1`.

Conjectures (Colin Barker, Jun 01 2017):
G.f.: (1 + 2*x - x^2 - x^3) / (1 - 6*x - 5*x^2 + 3*x^3 + 2*x^4).
a(n) = 6*a(n-1) + 5*a(n-2) - 3*a(n-3) - 2*a(n-4) for n>3.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a126503

open PowerSeries

/-- Two base-8 digits differ by at most 4. -/
def adjOk (x y : Fin 8) : Prop :=
  ((x : ℤ) - (y : ℤ)).natAbs ≤ 4

instance (x y : Fin 8) : Decidable (adjOk x y) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A word of length `n` over `Fin 8` has all adjacent digits differing by at most 4. -/
def isValid (n : ℕ) (w : Fin n → Fin 8) : Prop :=
  ∀ i : Fin (n - 1), adjOk (w ⟨i.val, by omega⟩) (w ⟨i.val + 1, by omega⟩)

instance (n : ℕ) (w : Fin n → Fin 8) : Decidable (isValid n w) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A126503: the number of base 8 n-digit numbers with adjacent digits differing by 4 or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (isValid n)).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 6 * X - 5 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4) =
      1 + 2 * X - X ^ 2 - X ^ 3) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 6 * a (n - 1) + 5 * a (n - 2) - 3 * a (n - 3) - 2 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a126503
