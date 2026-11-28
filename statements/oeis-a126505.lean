import Mathlib

/-!
# A126505: Number of base 10 n-digit numbers with adjacent digits differing by four or less.

Source: https://oeis.org/A126505
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 10, 70, 510, 3720, 27142, ...).

Conventions:
* A base 10 n-digit number (with leading zeros allowed, matching `a 0 = 1`, `a 1 = 10`,
  `a 2 = 70`) is a word `w : Fin n → Fin 10`.
* Adjacent digits at positions `i` and `i + 1` (for `i : Fin (n - 1)`) differ by at most 4,
  expressed as `((w i : ℤ) - (w (i + 1) : ℤ)).natAbs ≤ 4`.
* At `n = 0`, the unique empty word vacuously satisfies the condition, giving `a 0 = 1`.

Conjectures (Colin Barker, May 31 2017):
G.f.: (1 + 3*x - 3*x^2 - 4*x^3 + x^4 + x^5) / (1 - 7*x - 3*x^2 + 6*x^3 + x^4 - x^5).
a(n) = 7*a(n-1) + 3*a(n-2) - 6*a(n-3) - a(n-4) + a(n-5) for n>5.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a126505

open PowerSeries

/-- Two base-10 digits differ by at most 4. -/
def adjOk (x y : Fin 10) : Prop :=
  ((x : ℤ) - (y : ℤ)).natAbs ≤ 4

instance (x y : Fin 10) : Decidable (adjOk x y) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A word of length `n` over `Fin 10` has all adjacent digits differing by at most 4. -/
def isValid (n : ℕ) (w : Fin n → Fin 10) : Prop :=
  ∀ i : Fin (n - 1), adjOk (w ⟨i.val, by omega⟩) (w ⟨i.val + 1, by omega⟩)

instance (n : ℕ) (w : Fin n → Fin 10) : Decidable (isValid n w) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A126505: the number of base 10 n-digit numbers with adjacent digits differing by 4 or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (isValid n)).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 7 * X - 3 * X ^ 2 + 6 * X ^ 3 + X ^ 4 - X ^ 5) =
      1 + 3 * X - 3 * X ^ 2 - 4 * X ^ 3 + X ^ 4 + X ^ 5) ∧
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 7 * a (n - 1) + 3 * a (n - 2) - 6 * a (n - 3) - a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a126505
