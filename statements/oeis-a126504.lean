import Mathlib

/-!
# A126504: Number of base 9 n-digit numbers with adjacent digits differing by four or less.

Source: https://oeis.org/A126504
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 9, 61, 429, 3011, 21141, ...).

Conventions:
* A base 9 n-digit number (with leading zeros allowed, matching `a 0 = 1`, `a 1 = 9`,
  `a 2 = 61`) is a word `w : Fin n → Fin 9`.
* Adjacent digits at positions `i` and `i + 1` (for `i : Fin (n - 1)`) differ by at most 4,
  expressed as `((w i : ℤ) - (w (i + 1) : ℤ)).natAbs ≤ 4`.
* At `n = 0`, the unique empty word vacuously satisfies the condition, giving `a 0 = 1`.

Conjectures (Colin Barker, Jun 01 2017):
G.f.: (1 - x)*(1 + 3*x - x^3) / (1 - 7*x - x^2 + 6*x^3 - x^5).
a(n) = 7*a(n-1) + a(n-2) - 6*a(n-3) + a(n-5) for n>5.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a126504

open PowerSeries

/-- Two base-9 digits differ by at most 4. -/
def adjOk (x y : Fin 9) : Prop :=
  ((x : ℤ) - (y : ℤ)).natAbs ≤ 4

instance (x y : Fin 9) : Decidable (adjOk x y) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A word of length `n` over `Fin 9` has all adjacent digits differing by at most 4. -/
def isValid (n : ℕ) (w : Fin n → Fin 9) : Prop :=
  ∀ i : Fin (n - 1), adjOk (w ⟨i.val, by omega⟩) (w ⟨i.val + 1, by omega⟩)

instance (n : ℕ) (w : Fin n → Fin 9) : Decidable (isValid n w) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A126504: the number of base 9 n-digit numbers with adjacent digits differing by 4 or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (isValid n)).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 7 * X - X ^ 2 + 6 * X ^ 3 - X ^ 5) =
      (1 - X) * (1 + 3 * X - X ^ 3)) ∧
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 7 * a (n - 1) + a (n - 2) - 6 * a (n - 3) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a126504
