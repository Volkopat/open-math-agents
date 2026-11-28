import Mathlib

/-!
# A125468: Number of base 11 circular n-digit numbers with adjacent digits differing by 9 or less.

Source: https://oeis.org/A125468
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.
Offset 0 (data 1, 11, 119, 1271, 13763, 149051, ...).

Conventions:
* A base 11 circular n-digit number (with leading zeros allowed, matching `a 0 = 1`, `a 1 = 11`,
  `a 2 = 119`) is a word `w : Fin n → Fin 11`.
* Circular adjacency requires that for every `i : Fin n`, `w i` and `w ((i + 1) % n)` differ
  by at most 9, expressed as `((w i : ℤ) - (w ((i + 1) % n) : ℤ)).natAbs ≤ 9`.
* At `n = 0`, the unique empty word vacuously satisfies the condition, giving `a 0 = 1`.
  At `n = 1`, `w 0` is adjacent to itself with difference `0 ≤ 9`, giving `a 1 = 11`.

Conjectures (Colin Barker, Jun 04 2017):
G.f.: (1 - x^2 - 18*x^3) / ((1 - x)*(1 - 10*x - 9*x^2)).
a(n) = 1 + (5-sqrt(34))^n + (5+sqrt(34))^n for n>0.
a(n) = 11*a(n-1) - a(n-2) - 9*a(n-3) for n>3.
The generating function is stated after multiplication by its denominator, whose constant
term is one.
-/

namespace OMA.S_oeis_a125468

open PowerSeries

/-- Two base-11 digits differ by at most 9. -/
def adjOk (x y : Fin 11) : Prop :=
  ((x : ℤ) - (y : ℤ)).natAbs ≤ 9

instance (x y : Fin 11) : Decidable (adjOk x y) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A circular word of length `n` over `Fin 11` has all circularly adjacent digits differing
by at most 9. -/
def isValid (n : ℕ) (w : Fin n → Fin 11) : Prop :=
  ∀ i : Fin n, adjOk (w i) (w ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)

instance (n : ℕ) (w : Fin n → Fin 11) : Decidable (isValid n w) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A125468: the number of base 11 circular n-digit numbers with adjacent digits differing
by 9 or less. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (isValid n)).card

theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 10 * X - 9 * X ^ 2)) =
      1 - X ^ 2 - 18 * X ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 1 + (5 - Real.sqrt 34) ^ n + (5 + Real.sqrt 34) ^ n) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 11 * a (n - 1) - a (n - 2) - 9 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a125468
