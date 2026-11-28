import Mathlib

/-!
# A126530: Number of base 9 n-digit numbers with adjacent digits differing by five or less.

Source: https://oeis.org/A126530
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 9, 69, 541, 4231, 33101, ...).

Conventions:
* A base 9 n-digit number (with leading zeros allowed, matching `a 0 = 1`, `a 1 = 9`,
  `a 2 = 69`) is a word `w : Fin n → Fin 9`.
* Adjacent digits at positions `i` and `i + 1` (for `i : Fin (n - 1)`) differ by at most 5,
  expressed as `((w i : ℤ) - (w (i + 1) : ℤ)).natAbs ≤ 5`.
* At `n = 0`, the unique empty word vacuously satisfies the condition, giving `a 0 = 1`.

Conjectures (Colin Barker, Jun 01 2017):
G.f.: (1 + 2*x - x^2 - x^3) / ((1 + x)*(1 - 8*x + x^2 + 3*x^3)).
a(n) = 7*a(n-1) + 7*a(n-2) - 4*a(n-3) - 3*a(n-4) for n>3.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a126530

open PowerSeries

/-- Two base-9 digits differ by at most 5. -/
def adjOk (x y : Fin 9) : Prop :=
  ((x : ℤ) - (y : ℤ)).natAbs ≤ 5

instance (x y : Fin 9) : Decidable (adjOk x y) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A word of length `n` over `Fin 9` has all adjacent digits differing by at most 5. -/
def isValid (n : ℕ) (w : Fin n → Fin 9) : Prop :=
  ∀ i : Fin (n - 1), adjOk (w ⟨i.val, by omega⟩) (w ⟨i.val + 1, by omega⟩)

instance (n : ℕ) (w : Fin n → Fin 9) : Decidable (isValid n w) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A126530: the number of base 9 n-digit numbers with adjacent digits differing by 5 or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (isValid n)).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 + X) * (1 - 8 * X + X ^ 2 + 3 * X ^ 3)) =
      1 + 2 * X - X ^ 2 - X ^ 3) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 7 * a (n - 1) + 7 * a (n - 2) - 4 * a (n - 3) - 3 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a126530
